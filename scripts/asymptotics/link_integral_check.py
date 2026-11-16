"""Numerical check of `link_integral_explicit` and `link_eq_lor` (Lightlike/Asymptotics/Lorentzian/),
independent of the Lean proofs; numerical evidence, not proof.

(A) link_eq_lor, pointwise: conj F_g1(a^T (w,1)) F_g2(b^T (w,1)) == e^S / (|Z|^2 |Z'|^2).
(B) link_integral: <psi1, pi(a^-1 b) psi2>  (explicit unitary principal series on L2(C):
    (pi(c) f)(z) = m(den c z) f(mob c z), m(l) = |l|^(2 i rho - 2) (l/|l|)^n)
    == ((n+1)/pi)  * integral over C of e^S / (|Z|^2 |Z'|^2) dw,
    with psi_g(z) = sqrt((n+1)/pi) (1+|z|^2)^(i rho - 1 - n/2) (g00 z + g10)^n   (normalised, lowest level),
    xi = first column of conj(g1), xi' = first column of wM g2, Z = a^T (w,1), Z' = b^T (w,1).
The constant (n+1)/pi is (nrmA^2)^-1: ||tlin e_0||^2 = pi/(n+1) (computed here by quadrature too).
"""
import sys
import numpy as np

rng = np.random.default_rng(20261116)


def rand_su2():
    v = rng.normal(size=4)
    v /= np.linalg.norm(v)
    a, b = v[0] + 1j * v[1], v[2] + 1j * v[3]
    return np.array([[a, -np.conj(b)], [b, np.conj(a)]])


def rand_sl2c():
    m = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2))
    m *= 0.5
    m = m / np.sqrt(np.linalg.det(m) + 0j)
    return m


wM = np.array([[0, 1], [-1, 0]], dtype=complex)


def F(n, rho, g, zeta):
    N = abs(zeta[0]) ** 2 + abs(zeta[1]) ** 2
    return (N ** (1j * rho - 1)) * (N ** (-n / 2)) * (g[0, 0] * zeta[0] + g[1, 0] * zeta[1]) ** n


def e_s_over_density(n, rho, g1, g2, a, b, w, twist=True):
    zeta = np.array([w, np.ones_like(w)])
    Z = np.tensordot(a.T, zeta, axes=(1, 0))
    Zp = np.tensordot(b.T, zeta, axes=(1, 0))
    xi = np.conj(g1[:, 0])
    xip = ((wM if twist else np.eye(2)) @ g2)[:, 0]
    jxip = np.array([-np.conj(xip[1]), np.conj(xip[0])])
    ov1 = np.conj(Z[0]) * xi[0] + np.conj(Z[1]) * xi[1]
    ov2 = np.conj(jxip[0]) * Zp[0] + np.conj(jxip[1]) * Zp[1]
    nz = abs(Z[0]) ** 2 + abs(Z[1]) ** 2
    nzp = abs(Zp[0]) ** 2 + abs(Zp[1]) ** 2
    k = n / 2
    S = 2 * k * np.log(ov1 * ov2) - k * np.log(nz * nzp) + 1j * rho * np.log(nzp / nz)
    return np.exp(S) / (nz * nzp), Z, Zp


def grid(nt=700, nphi=700):
    x, wt = np.polynomial.legendre.leggauss(nt)
    t = (x + 1) * np.pi / 4
    wt = wt * np.pi / 4
    phi = np.arange(nphi) * 2 * np.pi / nphi
    T, P = np.meshgrid(t, phi, indexing="ij")
    r = np.tan(T)
    w = r * np.exp(1j * P)
    jac = r / np.cos(T) ** 2
    weights = (wt[:, None] * jac) * (2 * np.pi / nphi)
    return w, weights


def mobius(c, z):
    num = c[0, 0] * z + c[1, 0]
    den = c[0, 1] * z + c[1, 1]
    return num / den, den


def psi(n, rho, g, z):
    return np.sqrt((n + 1) / np.pi) * (1 + abs(z) ** 2) ** (1j * rho - 1 - n / 2) * (g[0, 0] * z + g[1, 0]) ** n


def mult(n, rho, l):
    al = abs(l)
    return al ** (2j * rho - 2) * (l / al) ** n


def run(n, rho, tol):
    g1, g2 = rand_su2(), rand_su2()
    a, b = rand_sl2c(), rand_sl2c()
    w, wt = grid()
    # (A) pointwise
    pts = rng.normal(size=5) + 1j * rng.normal(size=5)
    maxerr = 0.0
    for p in pts:
        zeta = np.array([p, 1.0 + 0j])
        lhs = np.conj(F(n, rho, g1, a.T @ zeta)) * F(n, rho, g2, b.T @ zeta)
        rhs, _, _ = e_s_over_density(n, rho, g1, g2, a, b, np.array(p))
        maxerr = max(maxerr, abs(lhs - rhs))
    # normalisation: ||f_0||^2 = pi/(n+1) (unnormalised tlin e_0: sqrt(C(n,0)) z^n (1+|z|^2)^(..))
    f0 = (1 + abs(w) ** 2) ** (-1 - n / 2) * abs(w) ** (2 * n) ** 0.5
    nrm2 = np.sum(wt * (1 + abs(w) ** 2) ** (-2 - n) * abs(w) ** (2 * n))
    # (B) explicit principal series
    c = np.linalg.inv(a) @ b
    mz, den = mobius(c, w)
    lhs_int = np.sum(wt * np.conj(psi(n, rho, g1, w)) * mult(n, rho, den) * psi(n, rho, g2, mz))
    dens, _, _ = e_s_over_density(n, rho, g1, g2, a, b, w)
    rhs_int = (n + 1) / np.pi * np.sum(wt * dens)
    # (B') unitarity form: <pi(a) psi1, pi(b) psi2> through the homogeneous formula
    zeta = np.array([w, np.ones_like(w)])
    za = np.tensordot(a.T, zeta, axes=(1, 0))
    zb = np.tensordot(b.T, zeta, axes=(1, 0))
    mid = np.sum(wt * np.conj(np.sqrt((n + 1) / np.pi) * F(n, rho, g1, za)) * np.sqrt((n + 1) / np.pi) * F(n, rho, g2, zb))
    print(f"n={n} rho={rho}: pointwise max err {maxerr:.2e}; ||tlin e0||^2={nrm2:.12f} (pi/(n+1)={np.pi/(n+1):.12f});")
    print(f"   <psi1,pi(a^-1 b)psi2> = {lhs_int:.10f}; via homogeneous F = {mid:.10f}; (n+1)/pi * int e^S rho = {rhs_int:.10f}")
    wrong, _, _ = e_s_over_density(n, rho, g1, g2, a, b, w, twist=False)
    wrong_int = (n + 1) / np.pi * np.sum(wt * wrong)
    print(f"   control (target spinor without the twist w): |explicit - wrong| = {abs(lhs_int - wrong_int):.2e}")
    assert abs(lhs_int - wrong_int) > 1e-3
    e1 = abs(lhs_int - rhs_int)
    e2 = abs(mid - rhs_int)
    ok = maxerr < 1e-10 and abs(nrm2 - np.pi / (n + 1)) < tol and e1 < tol and e2 < tol
    print(f"   |explicit - e^S| = {e1:.2e}, |homog - e^S| = {e2:.2e}; tolerance {tol:g}; {'OK' if ok else 'FAIL'}")
    return ok


if __name__ == "__main__":
    tol = 1e-6
    ok = True
    for n, rho in [(1, 0.7), (2, 1.3), (2, 0.0)]:
        ok = run(n, rho, tol) and ok
    print("OK" if ok else "FAIL")
    sys.exit(0 if ok else 1)
