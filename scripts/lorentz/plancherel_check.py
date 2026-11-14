"""Numerical cross-checks of the Plancherel formula of SL(2,C) (milestone HA2).

Part 1, the radial formula. 
Lean (Lightlike/Lorentz/SphericalPlancherel.lean, `spherical_plancherel`): for a radial
function f = F(coshDist g) on SL(2,C), F smooth with compact support,

    int_G |f|^2 dg = (2 pi^4)^{-1} int_0^oo rho^2 |fhat(rho)|^2 drho,
    fhat(rho)      = int_G f(g) phi_rho(g) dg,   phi_rho = sin(rho r) / (rho sinh r),

with the Haar measure normalised so that radial integrals are 4 pi^3 int_0^oo (.) sinh^2 r dr
(`integral_coshDist`).

The Lean proof goes through the Fourier transform of the odd profile sinh r F(cosh r) and
Plancherel's theorem on R. This script does not: it computes fhat(rho) by direct quadrature of
the radial integral at each rho (QAWO sine weight), and then the rho-integral by adaptive
quadrature, for two profiles (a real bump and a complex one).

Controls (wrong inputs): the flat spherical function sin(rho r)/(rho r) of R^3, the density
rho^2 + 1, and the hyperbolic-space constant (2 pi^2)^{-1} used with the group measure, each give
a different number.

Part 2, the full formula. Lean (Lightlike/Lorentz/Plancherel.lean, `plancherel_trace`):

    sum_n int (n^2 + 4 rho^2) tr pi_{n,rho}(F) drho = 16 pi^4 F(1),

proved in two steps, both checked here by direct quadrature of the defining integrals.

* Trace step (`integral_psKernel_diag`): tr pi_{n,rho}(F) = int K(z, z) d^2z with
  K(z, z) = int F(g) mult(n, rho, l) d^2b d^2l, g = fixChart z [b, z, l]. Since mult depends on l
  only, this says G(l) = int int F(g) d^2b d^2z equals pi Phi_{F#}(1/l), with F# the SU(2)
  conjugation average and Phi_F(mu) = int F([[mu, x], [0, 1/mu]]) d^2x. The script evaluates
  G(l) at several l (b rescaled by (1 + |z|^2) and centred, z on the Riemann sphere) for the
  invariant F0 = (tr X)^2 exp(-|X|^2) and the non-invariant F1 = X_00 exp(-|X|^2), whose average
  is (tr X / 2) exp(-|X|^2). Control: Phi_{F1} in place of Phi_{F1#} (no average) differs.
* Density step (`hasSum_density_orbInt`): with T(n, rho) = int mult(n, rho, l) Phi_F(1/l) d^2l,
  sum_n int (n^2 + 4 rho^2) T(n, rho) drho = 16 pi^3 F(1). The script computes T by quadrature in
  l = e^(s + i theta) for F0 and integrates over rho, without the Fourier inversion and limit
  formula of the Lean proof. It also checks the flat sum sum_n int T drho = 2 pi^2 Phi_F(1)
  (`hasSum_trace_flat`, divided by the trace factor pi). Controls: the densities n^2 + rho^2 and
  n^2 + 4 rho^2 + 1 differ.

Part 3, the constant 16 pi^4 including the sectors n != 0, from the definition of the kernel only.
With l = e^(s + i theta) and g(s, theta) = G(l), tr pi_{n,rho}(F) = int int e^(i(2 rho s + n theta))
g(s, theta) ds dtheta is a Fourier coefficient of g on R x S^1, so Fourier inversion gives

    sum_n int (n^2 + 4 rho^2) tr pi_{n,rho}(F) drho = -2 pi^2 (d_s^2 + d_theta^2) g(0, 0),

and the formula says that this is 16 pi^4 F(1). The script computes G(l) at the points of a
five-point stencil around l = 1 by the quadrature `chart_integral` of the defining integral, takes
the Laplacian by finite differences (step h and h/2, Richardson-extrapolated) and compares with
16 pi^4 F(1). Nothing of the Lean proof (SU(2) average, orbital integral, limit formula) is used.
The term -2 pi^2 d_theta^2 g(0, 0) is the part n^2 of the density, to which only n != 0
contributes; the script prints its share, which is 1/4 for F0, 1/8 for F1 and 1/3 for
F2 = X_00^2 exp(-|X|^2) (a function without symmetry and without a closed form here), so the
sectors n != 0 carry a sizeable part of the constant. Controls: dropping the part n^2 (the n = 0
reading) and the constant 1/(8 pi^4) of Perez-Rovelli gr-qc/0011037 (A11), (A16) in their
variables sigma = 2 rho (the left side is then sum_n int (n^2 + sigma^2) tr T_{n,sigma} dsigma =
2 x the above) both miss F(1); 1/(32 pi^4) and Ruehl's 1/2 with dg_R = (2 pi)^-4 dg recover it.

F0, F1 and F2 decay like Gaussians rather than having compact support; the identities are checked
for them as rapidly decreasing functions. This is numerical evidence, not proof.

Run: .venv/bin/python -I scripts/lorentz/plancherel_check.py   (needs numpy and scipy)
"""
import math

import numpy as np
from scipy import integrate

TOL = 1e-7
R_MAX = math.acosh(3.0)          # the profiles vanish for cosh r >= 3
RHO_MAX = 600.0                  # fhat decays like exp(-c sqrt(rho)); rho^2 fhat^2 is ~1e-12 here


def bump(t):
    """exp(-1 / (1 - (t - 2)^2)) on (1, 3), zero elsewhere."""
    u = t - 2.0
    return math.exp(-1.0 / (1.0 - u * u)) if abs(u) < 1.0 else 0.0


PROFILES = {
    "real bump": lambda t: complex(bump(t)),
    "complex bump": lambda t: bump(t) * complex(math.cos(3 * t), math.sin(3 * t)) * (t - 1.5),
}


def lhs(F):
    """int_G |F(coshDist)|^2 = 4 pi^3 int_0^oo sinh^2 r |F(cosh r)|^2 dr."""
    val, _ = integrate.quad(lambda r: math.sinh(r) ** 2 * abs(F(math.cosh(r))) ** 2, 0, R_MAX,
                            epsabs=1e-14, epsrel=1e-12, limit=400)
    return 4 * math.pi ** 3 * val


def fhat(F, rho, flat=False):
    """4 pi^3 int_0^oo sinh^2 r F(cosh r) phi_rho(r) dr with phi_rho = sin(rho r)/(rho sinh r),
    or the flat sin(rho r)/(rho r) when flat=True; the sine factor is the QAWO weight."""
    if flat:
        def amp(r):
            return math.sinh(r) ** 2 * F(math.cosh(r)) / (rho * r) if r > 0 else 0.0
    else:
        def amp(r):
            return math.sinh(r) * F(math.cosh(r)) / rho
    parts = []
    for part in (lambda r: amp(r).real, lambda r: amp(r).imag):
        v, _ = integrate.quad(part, 0, R_MAX, weight="sin", wvar=rho, epsabs=1e-14,
                              epsrel=1e-12, limit=400)
        parts.append(v)
    return 4 * math.pi ** 3 * complex(*parts)


def rhs(F, density=lambda rho: rho * rho, const=1 / (2 * math.pi ** 4), flat=False):
    """const * int_0^RHO_MAX density(rho) |fhat(rho)|^2 drho."""
    def integrand(rho):
        return density(rho) * abs(fhat(F, rho, flat)) ** 2
    pts = np.linspace(1e-9, RHO_MAX, 121)
    total = 0.0
    for a, b in zip(pts[:-1], pts[1:]):
        v, _ = integrate.quad(integrand, a, b, epsabs=1e-13, epsrel=1e-11, limit=200)
        total += v
    return const * total


def radial_checks():
    """Part 1: the radial formula and its controls."""
    ok = True
    for name, F in PROFILES.items():
        left = lhs(F)
        right = rhs(F)
        good = abs(left - right) < TOL * left
        ok &= good
        print(f"{name}: int_G |f|^2 = {left:.12e},  (2 pi^4)^-1 int rho^2 |fhat|^2 = {right:.12e}"
              f"  rel. diff {abs(left - right) / left:.1e}  {'OK' if good else 'FAIL'}")
        tail = abs(fhat(F, RHO_MAX)) ** 2 * RHO_MAX ** 2
        print(f"{name}: rho^2 |fhat|^2 at the cutoff rho = {RHO_MAX}: {tail:.1e}")
        controls = {
            "flat spherical function sin(rho r)/(rho r)": rhs(F, flat=True),
            "density rho^2 + 1": rhs(F, density=lambda rho: rho * rho + 1),
            "constant (2 pi^2)^-1": rhs(F, const=1 / (2 * math.pi ** 2)),
        }
        for label, val in controls.items():
            differs = abs(val - left) > 1e-3 * left
            ok &= differs
            print(f"{name}: control, {label}: {val:.12e}  "
                  f"{'differs as expected' if differs else 'FAIL: does not differ'}")
    return ok


# Part 2: the full formula. A 2x2 array is a row [X_00, X_01, X_10, X_11].

def hs_sq(X):
    """|X|^2 = sum |X_ij|^2, row-wise."""
    return np.sum(np.abs(X) ** 2, axis=-1)


def F0(X):
    """(tr X)^2 exp(-|X|^2), invariant under SU(2) conjugation; F0(1) = 4 e^-2."""
    return (X[..., 0] + X[..., 3]) ** 2 * np.exp(-hs_sq(X))


def F1(X):
    """X_00 exp(-|X|^2), not invariant; its SU(2) average is (tr X / 2) exp(-|X|^2)."""
    return X[..., 0] * np.exp(-hs_sq(X))


def gauss_orbit(mu):
    """int exp(-|[[mu, x], [0, 1/mu]]|^2) d^2x = pi exp(-(|mu|^2 + |mu|^-2))."""
    a = np.abs(mu) ** 2
    return math.pi * np.exp(-(a + 1 / a))


def phi_F0(mu):
    """Phi_{F0}(mu) = pi (mu + 1/mu)^2 exp(-(|mu|^2 + |mu|^-2))."""
    return (mu + 1 / mu) ** 2 * gauss_orbit(mu)


def phi_F1avg(mu):
    """Phi of the average of F1: pi (mu + 1/mu)/2 exp(-(|mu|^2 + |mu|^-2))."""
    return (mu + 1 / mu) / 2 * gauss_orbit(mu)


def phi_F1(mu):
    """Phi_{F1}(mu) = pi mu exp(-(|mu|^2 + |mu|^-2)), without the average (control)."""
    return mu * gauss_orbit(mu)


def orbital(F, mu, L=8.0, n=161):
    """Phi_F(mu) = int F([[mu, x], [0, 1/mu]]) d^2x by the trapezoid rule on [-L, L]^2."""
    x1 = np.linspace(-L, L, n)
    x = (x1[:, None] + 1j * x1[None, :]).ravel()
    X = np.stack([np.full_like(x, mu), x, np.zeros_like(x), np.full_like(x, 1 / mu)], axis=-1)
    return np.sum(F(X)) * (x1[1] - x1[0]) ** 2


def chart_integral(F, lam, nth=60, nph=48, L=7.0, nu=57):
    """G(lam) = int int F(g) d^2b d^2z, g = fixChart z [b, z, lam] = g0 + b g1 with
    g0 = [[1/lam, 0], [lam z - z/lam, lam]] and g1 = [[z, 1], [-z^2, -z]]. With w = (1 + |z|^2) b
    the measure is d^2w (1 + |z|^2)^-2 d^2z = d^2w (sin t / 4) dt dp on the Riemann sphere
    z = tan(t/2) e^(ip). The w-grid is centred at the minimiser of |g|^2, where
    |g1|^2 = (1 + |z|^2)^2."""
    t, wt = np.polynomial.legendre.leggauss(nth)
    t = (t + 1) * math.pi / 2
    wt = wt * math.pi / 2
    u1 = np.linspace(-L, L, nu)
    U = (u1[:, None] + 1j * u1[None, :]).ravel()
    du = (u1[1] - u1[0]) ** 2
    total = 0.0
    for tk, wk in zip(t, wt):
        r = math.tan(tk / 2)
        A = 1 + r * r
        for p in np.arange(nph) * 2 * math.pi / nph:
            z = r * complex(math.cos(p), math.sin(p))
            g0 = np.array([1 / lam, 0, lam * z - z / lam, lam])
            g1 = np.array([z, 1, -z * z, -z])
            w0 = -np.sum(g0 * np.conj(g1)) / A
            X = g0[None, :] + ((w0 + U) / A)[:, None] * g1[None, :]
            total += wk * (2 * math.pi / nph) * math.sin(tk) / 4 * np.sum(F(X)) * du
    return total


def T_modes(phi, ns_max=4, rho_max=40.0, n_rho=8001, S=3.0, ns=2401, nth=32):
    """T(n, rho) = int mult(n, rho, l) Phi(1/l) d^2l for |n| <= ns_max on a rho-grid. With
    l = e^(s + i theta): mult d^2l = e^(2 i rho s) e^(i n theta) ds dtheta (trapezoid rules)."""
    s = np.linspace(-S, S, ns)
    th = np.arange(nth) * 2 * math.pi / nth
    vals = phi(np.exp(-(s[:, None] + 1j * th[None, :])))
    rho = np.linspace(-rho_max, rho_max, n_rho)
    T = {}
    # numpy 2.0 with the macOS Accelerate BLAS raises spurious floating-point flags in complex
    # matmul; they are silenced here, and the results are checked to be finite instead.
    with np.errstate(all="ignore"):
        for n in range(-ns_max, ns_max + 1):
            c = vals @ np.exp(1j * n * th) * (2 * math.pi / nth) * (s[1] - s[0])
            out = np.empty(n_rho, dtype=complex)
            for k in range(0, n_rho, 500):
                out[k:k + 500] = np.exp(2j * np.outer(rho[k:k + 500], s)) @ c
            T[n] = out
    assert all(np.all(np.isfinite(T[n])) for n in T)
    return rho, T


def full_checks():
    """Part 2: the trace step and the density step of the full formula, with controls."""
    ok = True
    for mu in (1.0, 1.7, 0.6 + 0.5j):
        for name, F, phi in (("F0", F0, phi_F0), ("F1", F1, phi_F1)):
            num, exact = orbital(F, mu), phi(mu)
            good = abs(num - exact) < 1e-10 * abs(exact)
            ok &= good
            print(f"orbital integral Phi_{name}({mu}): quadrature vs closed form, rel. diff "
                  f"{abs(num - exact) / abs(exact):.1e}  {'OK' if good else 'FAIL'}")
    for lam in (1.0, 2.0, 0.6 + 0.5j, 1.3j):
        g0 = chart_integral(F0, lam)
        e0 = math.pi * phi_F0(1 / lam)
        g1 = chart_integral(F1, lam)
        e1 = math.pi * phi_F1avg(1 / lam)
        good = abs(g0 - e0) < TOL * abs(e0) and abs(g1 - e1) < TOL * abs(e1)
        ok &= good
        print(f"trace step at l = {lam}: G_F0 / (pi Phi_F0(1/l)) - 1 = {abs(g0 / e0 - 1):.1e}, "
              f"G_F1 / (pi Phi_F1#(1/l)) - 1 = {abs(g1 / e1 - 1):.1e}  {'OK' if good else 'FAIL'}")
        if lam != 1.0:
            wrong = math.pi * phi_F1(1 / lam)
            differs = abs(g1 - wrong) > 1e-3 * abs(g1)
            ok &= differs
            print(f"  control, no SU(2) average: pi Phi_F1(1/l) = {complex(wrong):.6f} vs "
                  f"G_F1 = {complex(g1):.6f}  "
                  f"{'differs as expected' if differs else 'FAIL: does not differ'}")
    rho, T = T_modes(phi_F0)
    h = rho[1] - rho[0]

    def total(density):
        return sum(np.sum(density(n, rho) * T[n]) * h for n in T)

    tail = max(abs(T[n][0]) for n in T)
    print(f"density step: max |T(n, rho)| at the cutoff |rho| = {rho[-1]}: {tail:.1e}")
    target = 16 * math.pi ** 3 * 4 * math.exp(-2)
    val = total(lambda n, r: n * n + 4 * r * r)
    good = abs(val - target) < TOL * target
    ok &= good
    print(f"density step: sum_n int (n^2 + 4 rho^2) T = {val.real:.12e}, 16 pi^3 F0(1) = "
          f"{target:.12e}, rel. diff {abs(val - target) / target:.1e}  {'OK' if good else 'FAIL'}")
    print(f"  trace form: pi times this = {math.pi * val.real:.12e}, 16 pi^4 F0(1) = "
          f"{math.pi * target:.12e}")
    flat = total(lambda n, r: 1 + 0 * r)
    flat_target = 2 * math.pi ** 2 * phi_F0(1.0)
    good = abs(flat - flat_target) < TOL * flat_target
    ok &= good
    print(f"flat sum: sum_n int T = {flat.real:.12e}, 2 pi^2 Phi_F0(1) = {flat_target:.12e}  "
          f"{'OK' if good else 'FAIL'}")
    controls = {
        "density n^2 + rho^2": total(lambda n, r: n * n + r * r),
        "density n^2 + 4 rho^2 + 1": total(lambda n, r: n * n + 4 * r * r + 1),
    }
    for label, v in controls.items():
        differs = abs(v - target) > 1e-3 * target
        ok &= differs
        print(f"density step: control, {label}: {v.real:.12e}  "
              f"{'differs as expected' if differs else 'FAIL: does not differ'}")
    return ok


# Part 3: the constant, with the sectors n != 0, from the kernel's definition.

def F2(X):
    """X_00^2 exp(-|X|^2): no symmetry; F2(1) = e^-2."""
    return X[..., 0] ** 2 * np.exp(-hs_sq(X))


def laplacian_parts(F, h):
    """d_s^2 g(0, 0) and d_theta^2 g(0, 0) for g(s, theta) = G(e^(s + i theta)), five-point
    stencils of step h, G by `chart_integral`."""
    c = np.array([-1 / 12, 4 / 3, -5 / 2, 4 / 3, -1 / 12]) / h ** 2
    gs = [chart_integral(F, complex(math.exp((k - 2) * h))) for k in range(5)]
    gt = [chart_integral(F, complex(math.cos((k - 2) * h), math.sin((k - 2) * h)))
          for k in range(5)]
    return complex(np.dot(c, gs)), complex(np.dot(c, gt))


def constant_checks(h=0.08):
    """Part 3: -2 pi^2 Laplacian of G at l = 1 against 16 pi^4 F(1), with the share of n != 0
    and the constants of the literature as controls."""
    ok = True
    for name, F, F_one in (("F0", F0, 4 * math.exp(-2)), ("F1", F1, math.exp(-2)),
                           ("F2", F2, math.exp(-2))):
        ss1, tt1 = laplacian_parts(F, h)
        ss2, tt2 = laplacian_parts(F, h / 2)
        ss, tt = (16 * ss2 - ss1) / 15, (16 * tt2 - tt1) / 15
        total = -2 * math.pi ** 2 * (ss + tt)
        target = 16 * math.pi ** 4 * F_one
        good = abs(total - target) < 1e-6 * target
        ok &= good
        share = (-2 * math.pi ** 2 * tt / target).real
        print(f"constant, {name}: sum_n int (n^2 + 4 rho^2) tr drho = {total.real:.10e}, "
              f"16 pi^4 F(1) = {target:.10e}, rel. diff {abs(total / target - 1):.1e}  "
              f"{'OK' if good else 'FAIL'}")
        n0 = -2 * math.pi ** 2 * ss
        differs = share > 0.1 and abs(n0 - target) > 0.1 * target
        ok &= differs
        print(f"  share of the part n^2 (sectors n != 0 only): {share:.6f}; without it "
              f"{n0.real:.6e}  {'differs as expected' if differs else 'FAIL: does not differ'}")
        pr_sum = 2 * total  # sigma = 2 rho: sum_n int (n^2 + sigma^2) tr T_{n,sigma} dsigma
        for label, value, expect in (
                ("Perez-Rovelli (A11), 1/(8 pi^4)", pr_sum / (8 * math.pi ** 4), 4.0),
                ("corrected, 1/(32 pi^4)", pr_sum / (32 * math.pi ** 4), 1.0),
                ("Ruehl, 1/2 with (2 pi)^-4 dg", pr_sum / (2 * (2 * math.pi) ** 4), 1.0)):
            ratio = (value / F_one).real
            good = abs(ratio - expect) < 1e-5
            ok &= good
            print(f"  {label}: gives {ratio:.8f} F(1)  {'OK' if good else 'FAIL'}")
    return ok


def main():
    ok = radial_checks()
    ok &= full_checks()
    ok &= constant_checks()
    print("OK" if ok else "FAILED")


if __name__ == "__main__":
    main()
