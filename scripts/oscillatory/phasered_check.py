"""Numerical check (not a proof) of local stationary phase in
Lightlike/Oscillatory/PhaseReduction.lean.

For a smooth phase phi on R^n with phi(0) = 0, d phi(0) = 0, Im phi >= 0, a nondegenerate
Hessian A = phi''(0), no other critical point on the support of u, and u smooth with compact
support (Lean: stationary_phase_local, for u supported near 0),
    I(tau) = int u(x) exp(i tau phi(x)) dx
           = L(tau) + O(tau^(-n/2-1)),   L(tau) = (2 pi/tau)^(n/2) invSqrtDet(-iA) u(0).
Hormander, ALPDO I, Theorem 7.7.5, also gives the next term, I = L (1 + kappa/tau + O(tau^-2)),
with kappa = L_1 u / u(0) and
    L_1 u = sum over (nu, mu) in {(1, 0), (2, 1), (3, 2)} of
            i^(-1) 2^(-nu) <A^-1 D, D>^nu (g^mu u)(0) / (mu! nu!),
where D = -i grad and g = phi - <A x, x>/2 is the part of the phase beyond its quadratic part.
kappa is computed exactly with SymPy from the Taylor polynomial of u; the terms with mu >= 1
are the contribution of g, which the Lean proof handles by the phase reduction.

Here u(x) = exp(1/4 - 1/(4 - 4|x|^2/R^2)) on |x| < R (zero outside), so u(0) = 1, with a radius R
chosen per instance. I(tau) is computed by the tensor-product trapezoidal rule on [-R, R]^n; the
integrand is smooth with compact support, so the rule converges faster than any power of the
step. The computation is independent of the Lean proof. Checks, on four instances (n = 1, 2;
cubic and quartic perturbations; real and complex Hessians; Im phi from a quartic term or from
Im A):
 1. A is symmetric with det A != 0, and |Re grad phi(x)| >= 0.05 |x| on the grid points of the
    support. So 0 is the only critical point there, and no stationary point of Re phi with weak
    damping exp(-tau Im phi) pollutes I(tau) at moderate tau. (The Lean test phase has such a
    point at x = -1/3, where Im phi = 1/81, so its radius is R = 1/4.);
 2. Im phi >= 0 on the grid;
 3. tau^(n/2+1) |I - L| has stopped growing: over each of the last two doublings of tau it grows
    by a factor of at most 1.25. A wrong leading coefficient leaves an error of order at least
    tau^(-n/2-1/2), so this quantity then grows by a factor of at least sqrt 2 per doubling;
 4. the next-order coefficient: kappa_est(tau) = tau (I/L - 1) = kappa + O(1/tau). Richardson
    extrapolation, kappa_R = 2 kappa_est(tau_max) - kappa_est(tau_max/2), removes the O(1/tau)
    term, so |kappa_R - kappa| must be at most a quarter of |kappa_est(tau_max) - kappa| (or below
    1e-3). If kappa were wrong, both distances would tend to the same nonzero value.
Controls, which must FAIL:
 (a) wrong phase: (2 pi/tau)^(1/2) u(0), the real Gaussian coefficient of Laplace's method
     without the Fresnel factor e^(i pi/4), for the Lean test phase x^2/2 + x^3 + i x^4 (Lean:
     testPhase_wrong_phase), must fail check 3;
 (b) the perturbation is seen: kappa computed without the terms of g (mu = 0 only, the value for
     the quadratic part alone), for the same phase, must fail check 4;
 (c) degenerate phase: phi = x^3 + i x^4 on R^1, A = 0. Then I decays like tau^(-1/3), while
     the formula's leading term is 0 (invSqrtDet 0 = 0 in Lean), so check 3 must fail.
The script exits with code 0 only if every check passes and every control fails.

Usage: python3 -I scripts/oscillatory/phasered_check.py
"""
import sys

import numpy as np
import sympy as sp

CHUNK = 200
X, Y = sp.symbols("x y", real=True)
S = sp.symbols("s")


def amplitude(r2, R):
    """The bump exp(1/4 - 1/(4 - 4 r^2/R^2)) on r < R, zero outside; u(0) = 1."""
    out = np.zeros_like(r2)
    inside = r2 < R * R
    out[inside] = np.exp(0.25 - 1.0 / (4.0 - 4.0 * r2[inside] / (R * R)))
    return out


class Instance:
    """phi = <A x, x>/2 + g on R^n, with the amplitude supported in the ball of radius R."""

    def __init__(self, n, A, g, R, taus, points):
        self.n, self.Asym, self.g, self.taus = n, A, g, taus
        self.Rsym, self.R = sp.nsimplify(R), float(R)
        self.h = 2 * self.R / points
        self.vars = [X] if n == 1 else [X, Y]
        v = sp.Matrix(self.vars)
        phi = (v.T * A * v)[0, 0] / 2 + g
        self.phase = sp.lambdify(self.vars, phi, "numpy")
        grad = [sp.diff(phi, w) for w in self.vars]
        self.re_grad = [sp.lambdify(self.vars, sp.re(sp.expand(d)), "numpy") for d in grad]
        self.A = np.array(A.evalf(), dtype=complex)

    def grid(self):
        """The trapezoidal grid on [-R, R]."""
        return np.arange(-self.R, self.R + self.h / 2, self.h)

    def integral(self, tau, phase=None):
        """I(tau) = int u exp(i tau phi) by the trapezoidal rule on [-R, R]^n (in blocks of CHUNK
        rows for n = 2)."""
        phase = phase or self.phase
        t = self.grid()
        if self.n == 1:
            return np.sum(amplitude(t * t, self.R) * np.exp(1j * tau * phase(t))) * self.h
        total = 0j
        y = t[None, :]
        for i0 in range(0, len(t), CHUNK):
            x = t[i0:i0 + CHUNK, None]
            total += np.sum(amplitude(x * x + y * y, self.R) * np.exp(1j * tau * phase(x, y)))
        return total * self.h * self.h

    def support_stats(self):
        """min Im phi, and min |Re grad phi(x)|/|x| over grid points 0 < |x| < R."""
        t = self.grid()
        if self.n == 1:
            x = t[(t * t < self.R ** 2) & (t != 0)]
            return self.phase(x).imag.min(), (np.abs(self.re_grad[0](x)) / np.abs(x)).min()
        im_min, ratio = np.inf, np.inf
        y = t[None, :]
        for i0 in range(0, len(t), CHUNK):
            x = t[i0:i0 + CHUNK, None] + 0 * y
            yy = y + 0 * x
            r2 = x * x + yy * yy
            m = (r2 < self.R ** 2) & (r2 > 0)
            im_min = min(im_min, self.phase(x, yy).imag[m].min())
            gx, gy = self.re_grad[0](x, yy) + 0 * x, self.re_grad[1](x, yy) + 0 * x
            ratio = min(ratio, (np.sqrt(gx * gx + gy * gy)[m] / np.sqrt(r2[m])).min())
        return im_min, ratio

    def kappa(self, with_g=True):
        """kappa = L_1 u / u(0) from Hormander's formula (7.7.13'), exactly from the Taylor
        polynomial of u to degree 8 (only degrees <= 6 enter)."""
        n = self.n
        useries = sp.series(sp.exp(sp.Rational(1, 4) - 1 / (4 - S)), S, 0, 5).removeO()
        r2 = sum(w ** 2 for w in self.vars)
        u = sp.expand(useries.subs(S, 4 * r2 / self.Rsym ** 2))
        Ainv = self.Asym.inv()

        def P(f):
            """<A^-1 D, D> f = -sum_ij (A^-1)_ij d_i d_j f."""
            return -sum(Ainv[i, j] * sp.diff(f, self.vars[i], self.vars[j])
                        for i in range(n) for j in range(n))

        total = 0
        at0 = {w: 0 for w in self.vars}
        for nu, mu in ([(1, 0), (2, 1), (3, 2)] if with_g else [(1, 0)]):
            f = sp.expand(self.g ** mu * u)
            for _ in range(nu):
                f = sp.expand(P(f))
            total += sp.Rational(1, 2 ** nu) * f.subs(at0) / (sp.factorial(mu) * sp.factorial(nu))
        return complex(sp.N(total / sp.I))


def inv_sqrt_det(M):
    """invSqrtDet M: the product of principal roots mu^(-1/2) over the eigenvalues of M."""
    return np.prod(np.linalg.eigvals(M).astype(complex) ** -0.5)


def leading(A, tau):
    """L(tau) = (2 pi/tau)^(n/2) invSqrtDet(-iA) u(0), with u(0) = 1."""
    n = A.shape[0]
    return (2 * np.pi / tau) ** (n / 2) * inv_sqrt_det(-1j * A)


T1 = [80.0, 160.0, 320.0, 640.0, 1280.0]
T2 = [10.0, 20.0, 40.0, 80.0, 160.0]
INSTANCES = {
    "phi = x^2/2 + x^3 + i x^4 (Lean: testPhase), R = 1/4":
        Instance(1, sp.Matrix([[1]]), X ** 3 + sp.I * X ** 4, sp.Rational(1, 4),
                 [1280.0, 2560.0, 5120.0, 10240.0, 20480.0], 200000),
    "phi = -x^2 + x^3/3 + i x^4, R = 3/2":
        Instance(1, sp.Matrix([[-2]]), X ** 3 / 3 + sp.I * X ** 4, sp.Rational(3, 2),
                 [20.0, 40.0, 80.0, 160.0, 320.0], 20000),
    "phi = (x^2 - y^2)/2 + x^2 y + i (x^4 + y^4), R = 1":
        Instance(2, sp.Matrix([[1, 0], [0, -1]]), X ** 2 * Y + sp.I * (X ** 4 + Y ** 4), 1,
                 [40.0, 80.0, 160.0, 320.0, 640.0], 4800),
    "phi = <A x, x>/2 + (x^3 - 3 x y^2)/10, A = [[1, 1/2], [1/2, -1]] + 0.3i Id, R = 2":
        Instance(2, sp.Matrix([[1, sp.Rational(1, 2)], [sp.Rational(1, 2), -1]])
                 + sp.Rational(3, 10) * sp.I * sp.eye(2), (X ** 3 - 3 * X * Y ** 2) / 10, 2, T2,
                 3200),
}


def no_growth(errs):
    """Check 3: the scaled error grows by a factor of at most 1.25 over each of the last two
    doublings of tau."""
    return errs[-1] <= 1.25 * errs[-2] and errs[-2] <= 1.25 * errs[-3]


def scaled_errors(inst, values, coeff_fn):
    """tau^(n/2+1) |I(tau) - coeff_fn(tau)| over the instance's taus."""
    return [tau ** (inst.n / 2 + 1) * abs(v - coeff_fn(tau)) for tau, v in zip(inst.taus, values)]


def kappa_check(inst, values, k):
    """Check 4: kappa_est(tau) = tau (I/L - 1) = kappa + O(1/tau). The Richardson value
    kappa_R = 2 kappa_est(tau_max) - kappa_est(tau_max/2) removes the O(1/tau) term, so
    |kappa_R - kappa| must be at most a quarter of |kappa_est(tau_max) - kappa|, or below 1e-3.
    If kappa were wrong, both would tend to the same nonzero distance and the ratio to 1."""
    est = [tau * (v / leading(inst.A, tau) - 1) for tau, v in zip(inst.taus, values)]
    kr = 2 * est[-1] - est[-2]
    plain, rich = abs(est[-1] - k), abs(kr - k)
    return rich <= max(plain / 4, 1e-3), plain, rich


def main():
    ok = True
    for name, inst in INSTANCES.items():
        values = [inst.integral(tau) for tau in inst.taus]
        im_min, ratio = inst.support_stats()
        sym = np.allclose(inst.A, inst.A.T)
        nondeg = abs(np.linalg.det(inst.A)) > 1e-9
        errs = scaled_errors(inst, values, lambda tau: leading(inst.A, tau))
        k = inst.kappa()
        good4, plain, rich = kappa_check(inst, values, k)
        good = sym and nondeg and im_min >= -1e-12 and ratio > 0.05 and no_growth(errs) and good4
        ok &= good
        print(f"{name}: invSqrtDet(-iA) = {inv_sqrt_det(-1j * inst.A):.6f}, kappa = {k:.6f}")
        print(f"  min Im phi = {im_min:.2e}, min |Re grad phi|/|x| = {ratio:.3f}")
        print("  tau =", ", ".join(f"{tau:g}" for tau in inst.taus))
        print("  tau^(n/2+1)|I - L| =", ", ".join(f"{e:.4f}" for e in errs))
        print(f"  |kappa_est - kappa| = {plain:.2e}, Richardson |kappa_R - kappa| = {rich:.2e}")
        print("  ", "OK" if good else "FAILED")

    inst = next(iter(INSTANCES.values()))
    values = [inst.integral(tau) for tau in inst.taus]
    controls_fail = True
    wrong_phase = scaled_errors(inst, values, lambda tau: (2 * np.pi / tau) ** 0.5)
    fails = not no_growth(wrong_phase)
    controls_fail &= fails
    print("control (a) no Fresnel phase, Lean testPhase: tau^(3/2)|I - L| =",
          ", ".join(f"{e:.2f}" for e in wrong_phase),
          "(fails check 3)" if fails else "(PASSES check 3: control broken)")
    k0 = inst.kappa(with_g=False)
    good4, plain, rich = kappa_check(inst, values, k0)
    controls_fail &= not good4
    print(f"control (b) kappa without g, {k0:.6f}: |kappa_est - kappa| = {plain:.2e}, "
          f"|kappa_R - kappa| = {rich:.2e}",
          "(fails check 4)" if not good4 else "(PASSES check 4: control broken)")
    degenerate = Instance(1, sp.Matrix([[0]]), X ** 3 + sp.I * X ** 4, 1, T1, 20000)
    dvals = [degenerate.integral(tau) for tau in degenerate.taus]
    degen_errs = scaled_errors(degenerate, dvals, lambda tau: 0.0)
    fails = not no_growth(degen_errs)
    controls_fail &= fails
    print("control (c) degenerate x^3 + i x^4, R = 1: tau^(3/2)|I - 0| =",
          ", ".join(f"{e:.2f}" for e in degen_errs),
          "(fails check 3)" if fails else "(PASSES check 3: control broken)")
    ok &= controls_fail
    print("OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
