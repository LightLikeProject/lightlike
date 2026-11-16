"""Numerical check (not a proof) of the Hessian block H^{X_a X_a} of the Lorentzian vertex action
against eq. (61) of Barrett, Dowdall, Fairbairn, Hellmann, Pereira (arXiv:0907.2440, Appendix A,
p. 33), with SciPy (second derivative of the action along X_a exp(t L) by central differences).

The action of one end of a triangle at a node is, with the spinor Z of the end (BDFHP (17), power form)
  source end:  n log<Z, xi>  - (n/2) log |Z|^2 - i p log |Z|^2      (Z = xi at the critical point),
  target end:  n log<J xi, Z> - (n/2) log |Z|^2 + i p log |Z|^2      (Z = lam J xi, lam in C*),
with n = 2k and p = gamma k, and Z -> exp(t L)^H Z for X -> X exp(t L), L = alpha J + beta K.
The unit vectors m_e = <xi, sigma xi> of the spinors xi_ab (source end) and xi_ba (target end) satisfy
the closure sum_e k_e m_e = 0 (BDFHP (25)); then the first derivative along every L vanishes.

Results (the generators J = i sigma/2, K = sigma/2 are those stated in BDFHP App. B eq. (64)):
 (a) at a node whose ends are all source ends, the second derivative is 1/4 of (61): (61) is reproduced
     with the generators i sigma and sigma (alpha, beta doubled);
 (b) at a node with source and target ends no variant of (61) reproduces the second derivative; the
     closed form of Lightlike/Asymptotics/Lorentzian/HessianNode.lean (endForm) does:
       k [ -1/2 (a,a) + i s (a,b) + s m.(a x b) - (1/2 + i s gamma) (b,b) ] summed over the ends,
     with s = +1 at a source end and -1 at a target end, (u,v) = u.v - (m.u)(m.v).
Controls: dropping the sign s, or the triple product, gives a large residual.
Usage: python3 -I scripts/asymptotics/lorentzian_hessian_paper61_check.py
"""
import sys

import numpy as np
import scipy.linalg as sl

rng = np.random.default_rng(11)
SIG = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]]), np.array([[1, 0], [0, -1]], complex)]
GAM = 0.8


def genm(c):
    return sum(c[i] * SIG[i] for i in range(3)) / 2


def jmap(v):
    return np.array([-np.conj(v[1]), np.conj(v[0])])


def spinor(nv):
    th = np.arccos(nv[2])
    ph = np.arctan2(nv[1], nv[0])
    return np.array([np.cos(th / 2), np.sin(th / 2) * np.exp(1j * ph)])


def closed_config(kind):
    while True:
        mv = rng.normal(size=(len(kind), 3))
        mv /= np.linalg.norm(mv, axis=1)[:, None]
        kk = np.linalg.svd(mv.T)[2][-1]
        if np.all(kk > 0) or np.all(kk < 0):
            break
    k = np.abs(kk)
    xis = [spinor(v) for v in mv]
    zs = [xis[e] if kind[e] == 'src' else (1.3 + 0.2 * e) * np.exp(0.3j * e) * jmap(xis[e])
          for e in range(len(kind))]
    return mv, k, xis, zs


def end_action(k, xi, z, end):
    n, p = 2 * k, GAM * k
    nz = np.vdot(z, z).real
    if end == 'src':
        return n * np.log(np.vdot(z, xi)) - (n / 2) * np.log(nz) - 1j * p * np.log(nz)
    return n * np.log(np.vdot(jmap(xi), z)) - (n / 2) * np.log(nz) + 1j * p * np.log(nz)


def derivs(cfg, kind, L, h=1e-3):
    mv, k, xis, zs = cfg

    def g(t):
        u = sl.expm(t * L).conj().T
        return sum(end_action(k[e], xis[e], u @ zs[e], kind[e]) for e in range(len(k)))
    return (g(h) - 2 * g(0) + g(-h)) / h ** 2, (g(h) - g(-h)) / (2 * h)


def proj(u, v, m):
    return u @ v - (m @ u) * (m @ v)


def paper61(cfg, al, be):
    mv, k, _, _ = cfg
    return sum(-2 * k[e] * proj(al, al, mv[e]) + 4j * k[e] * proj(al, be, mv[e])
               - (4j * GAM * k[e] + 2 * k[e]) * proj(be, be, mv[e]) for e in range(len(k)))


def variant(cfg, kind, al, be, v):
    mv, k, _, _ = cfg
    q = 0
    for e in range(len(k)):
        s = 1 if kind[e] == 'src' else -1
        ps = GAM * k[e] * (1 if v == 0 else s)
        a_ = 1 if v < 2 else s
        c_ = 0 if v < 3 else s * 4 * k[e] * (mv[e] @ np.cross(al, be))
        q += -2 * k[e] * proj(al, al, mv[e]) + a_ * 4j * k[e] * proj(al, be, mv[e]) \
            - (4j * ps + 2 * k[e]) * proj(be, be, mv[e]) + c_
    return q


def main():
    ok = True
    kind = ['src'] * 4
    cfg = closed_config(kind)
    worst, grad = 0.0, 0.0
    for _ in range(3):
        al, be = rng.normal(size=3), rng.normal(size=3)
        num, d1 = derivs(cfg, kind, 2 * genm(be + 1j * al))
        worst = max(worst, abs(num - paper61(cfg, al, be)) / abs(num))
        grad = max(grad, abs(d1))
    ratio = derivs(cfg, kind, genm(be + 1j * al))[0] / paper61(cfg, al, be)
    good = worst < 1e-5 and grad < 1e-4 and abs(ratio - 0.25) < 1e-5
    print(f"(a) all-source node: |numeric - (61)| / |numeric| = {worst:.2e} with the generators "
          f"i sigma, sigma; max |first derivative| = {grad:.1e}; ratio to (61) with J=i sigma/2, K=sigma/2: "
          f"{ratio.real:.5f}: {'ok' if good else 'FAIL'}")
    ok = ok and good
    kind = ['src', 'src', 'tgt', 'tgt']
    cfg = closed_config(kind)
    tot = [0.0] * 4
    ref = 0.0
    for _ in range(3):
        al, be = rng.normal(size=3), rng.normal(size=3)
        num = derivs(cfg, kind, 2 * genm(be + 1j * al))[0]
        ref += abs(num)
        for v in range(4):
            tot[v] += abs(num - variant(cfg, kind, al, be, v))
    names = ["(61) literal", "p -> s p", "p -> s p and s on (alpha,beta)", "plus s 4k m.(alpha x beta) [endForm x4]"]
    res = [t / ref for t in tot]
    good = res[0] > 0.1 and res[1] > 0.1 and res[2] > 0.05 and res[3] < 1e-4
    print("(b) node with two source and two target ends, relative residuals: "
          + ", ".join(f"{n}: {r:.2e}" for n, r in zip(names, res)) + f": {'ok' if good else 'FAIL'}")
    ok = ok and good
    print("OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
