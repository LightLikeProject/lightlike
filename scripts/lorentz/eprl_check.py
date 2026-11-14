"""Numerical cross-checks for the Lorentzian EPRL vertex amplitude (milestone SF7).

Numerical evidence, not proof. Three independent checks of statements proved in Lean.

1. Signature bridge (Lightlike/Lorentz/Signature.lean). Physlib's covering map is
   L(M)_ij = 1/2 tr(s_i M s_j M^H) with s = (1, -sx, -sy, -sz) (`toLorentzGroup_eq_trace`),
   indexed by Fin 1 + Fin 3 = (0, 1, 2, 3). For random M in SL(2,C) the script checks
   * L^T eta L = eta with the project's eta = diag(-1, 1, 1, 1)
     (`lorentzMat_transpose_mul_eta_mul_self`), and L(MN) = L(M) L(N) (`lorentzMat_mul`);
   * L_00 = ||M||_F^2 / 2 = coshDist M (`coshDist_eq_lorentzMat`);
   * the normal N = L e0 has eta(N, N) = -1 and N^0 >= 1 (`normal_minkowskiForm_self`,
     `one_le_normal_zero`);
   * coshDist(A^-1 B) = -eta(N_A, N_B) (`coshDist_inv_mul`).
   Controls: with Physlib's eta_P = diag(1, -1, -1, -1) the last identity has the wrong sign,
   and coshDist(A B) differs from -eta(N_A, N_B).

2. Kernel exponent (Lightlike/Lorentz/KernelBound.lean). The kernel is
   I(g) = pi r / sinh r with cosh r = coshDist g, and the Haar measure in the radial variable is
   4 pi^3 sinh(r)^2 dr (`lintegral_coshDist`). So
   int I^p dg = 4 pi^3 pi^p int_0^oo (r / sinh r)^p sinh(r)^2 dr,
   finite for p = 5/2 (`lintegral_kernelE_rpow_lt_top`) and infinite for p = 2
   (`lintegral_kernelE_sq_eq_top`), where the integrand is r^2. The script evaluates the
   p = 5/2 integral and shows that the truncated p = 2 integral grows like R^3 / 3.

3. EPRL labels (Lightlike/Lorentz/EPRLTests.lean, `casimir2_eprlVec_fun`). With
   k = j and rho = gamma (j + 1), the second Casimir k rho equals gamma j (j + 1), gamma times the
   SU(2) Casimir of the lowest spin j (the linear simplicity constraint in the form of
   Ding-Rovelli, arXiv:1006.1294, eq. (24)). Control (`casimir2_wrong_label_ne`): the label
   rho = gamma j of Engle-Pereira gives gamma j^2.

The spin-0 coefficient sin(gamma r) / (gamma sinh r) (`eprlCoeff_spin_zero`) is the spherical
function at rho = gamma, checked by scripts/lorentz/spherical_check.py.

Run: .venv/bin/python -I scripts/lorentz/eprl_check.py   (needs numpy, scipy and sympy)
"""
import math

import numpy as np
import sympy as sp
from scipy import integrate, special

TOL = 1e-10
ETA = np.diag([-1.0, 1.0, 1.0, 1.0])
ETA_PHYSLIB = np.diag([1.0, -1.0, -1.0, -1.0])
SX = np.array([[0, 1], [1, 0]], dtype=complex)
SY = np.array([[0, -1j], [1j, 0]], dtype=complex)
SZ = np.array([[1, 0], [0, -1]], dtype=complex)
SIGMA_PRIME = [np.eye(2, dtype=complex), -SX, -SY, -SZ]
E0 = np.array([1.0, 0.0, 0.0, 0.0])


def random_sl2c(rng, scale=1.0):
    """A random matrix of determinant 1."""
    m = scale * (rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2)))
    return m / np.sqrt(np.linalg.det(m))


def lorentz(m):
    """Physlib's L(M)_ij = 1/2 tr(s_i M s_j M^H), real by construction."""
    out = np.empty((4, 4))
    for i in range(4):
        for j in range(4):
            val = 0.5 * np.trace(SIGMA_PRIME[i] @ m @ SIGMA_PRIME[j] @ m.conj().T)
            assert abs(val.imag) < TOL
            out[i, j] = val.real
    return out


def cosh_dist(m):
    """coshDist g = ||g||_F^2 / 2."""
    return float(np.sum(np.abs(m) ** 2) / 2)


def mink(v, w, eta=ETA):
    return float(v @ eta @ w)


def part1(rng):
    print("1. Signature bridge (Physlib -> project's eta = diag(-1,1,1,1))")
    worst = {"lorentz": 0.0, "mul": 0.0, "l00": 0.0, "unit": 0.0, "link": 0.0}
    min_n0 = math.inf
    ctrl_sign, ctrl_order = math.inf, 0.0
    for _ in range(200):
        a, b = random_sl2c(rng), random_sl2c(rng, scale=0.5)
        la, lb = lorentz(a), lorentz(b)
        worst["lorentz"] = max(worst["lorentz"], np.abs(la.T @ ETA @ la - ETA).max())
        worst["mul"] = max(worst["mul"], np.abs(lorentz(a @ b) - la @ lb).max())
        worst["l00"] = max(worst["l00"], abs(la[0, 0] - cosh_dist(a)))
        na, nb = la @ E0, lb @ E0
        worst["unit"] = max(worst["unit"], abs(mink(na, na) + 1))
        min_n0 = min(min_n0, na[0])
        lhs = cosh_dist(np.linalg.inv(a) @ b)
        worst["link"] = max(worst["link"], abs(lhs - (-mink(na, nb))) / lhs)
        # Controls: Physlib's eta gives -cosh <= -1; the product A B instead of A^-1 B.
        ctrl_sign = min(ctrl_sign, abs(lhs - (-mink(na, nb, ETA_PHYSLIB))))
        ctrl_order = max(ctrl_order, abs(cosh_dist(a @ b) - (-mink(na, nb))) / lhs)
    for key, val in worst.items():
        print(f"   max error {key:8s} {val:.2e}")
        assert val < 1e-9, key
    print(f"   min N^0 = {min_n0:.6f} (>= 1)")
    assert min_n0 >= 1 - TOL
    print(f"   control, Physlib eta: min |coshDist - (-eta_P(N_A,N_B))| = {ctrl_sign:.3f} "
          "(>= 2, wrong sign)")
    assert ctrl_sign >= 2 - 1e-9
    print(f"   control, A B instead of A^-1 B: max relative error {ctrl_order:.3f}")
    assert ctrl_order > 0.1


def part2():
    print("2. Kernel exponent: int (r/sinh r)^p sinh^2 r dr")

    def f(r, p):
        if r == 0.0:
            return 0.0
        # (r / sinh r)^p sinh^2 r = r^p sinh(r)^(2 - p), with log sinh r computed stably
        log_sinh = r + math.log1p(-math.exp(-2 * r)) - math.log(2)
        return r ** p * math.exp((2 - p) * log_sinh)

    val, err = integrate.quad(f, 0, np.inf, args=(2.5,), limit=200)
    total = 4 * math.pi ** 3 * math.pi ** 2.5 * val
    print(f"   p = 5/2: radial integral {val:.10f} (quad error {err:.1e}), "
          f"int I^(5/2) dg = {total:.6f}")
    assert math.isfinite(val) and err < 1e-8
    tails = []
    for big_r in (10.0, 20.0, 40.0):
        v2, _ = integrate.quad(f, 0, big_r, args=(2.0,), limit=200)
        v25, _ = integrate.quad(f, 0, big_r, args=(2.5,), limit=200)
        tails.append((big_r, v2, v25))
        print(f"   R = {big_r:4.0f}: p = 2 gives {v2:12.4f} (R^3/3 = {big_r ** 3 / 3:12.4f}), "
              f"p = 5/2 gives {v25:.10f}")
        assert abs(v2 - big_r ** 3 / 3) < 1e-6 * big_r ** 3
    # For p = 5/2 and r >= R, e^r (1 - e^(-2R)) / 2 <= sinh r <= e^r / 2, so the tail
    # int_R^oo r^(5/2) sinh(r)^(-1/2) dr lies between T and T / sqrt(1 - e^(-2R)), where
    # T = sqrt(2) int_R^oo r^(5/2) e^(-r/2) dr = sqrt(2) 2^(7/2) Gamma(7/2, R/2).
    for big_r, _, v25 in tails:
        tail = val - v25
        low = math.sqrt(2) * 2 ** 3.5 * special.gammaincc(3.5, big_r / 2) * special.gamma(3.5)
        high = low / math.sqrt(1 - math.exp(-2 * big_r))
        print(f"   R = {big_r:4.0f}: p = 5/2 tail {tail:.6e}, bracket [{low:.6e}, {high:.6e}]")
        assert low - 1e-7 < tail < high + 1e-7


def part3():
    print("3. EPRL labels: second Casimir k rho on the lowest SU(2) level")
    j, gamma = sp.symbols("j gamma", positive=True)
    k, rho = j, gamma * (j + 1)
    diff = sp.simplify(k * rho - gamma * j * (j + 1))
    print(f"   k = j, rho = gamma (j+1): k rho - gamma j (j+1) = {diff}")
    assert diff == 0
    wrong = sp.simplify(k * (gamma * j) - gamma * j * (j + 1))
    print(f"   control rho = gamma j: k rho - gamma j (j+1) = {sp.factor(wrong)} (nonzero)")
    assert wrong != 0
    for jj, gg in ((sp.Rational(1, 2), sp.Rational(1, 3)), (2, sp.Rational(7, 10))):
        assert sp.simplify(wrong.subs({j: jj, gamma: gg})) != 0


def main():
    rng = np.random.default_rng(20261110)
    part1(rng)
    part2()
    part3()
    print("OK")


if __name__ == "__main__":
    main()
