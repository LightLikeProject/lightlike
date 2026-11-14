"""The saddle level (numerical evidence, not a proof).

Checks the statements of Lightlike/Asymptotics/Level.lean (step G6) for the regular unit
tetrahedron and for random Euclidean tetrahedra. With face sums A_i, quadrilateral sums B_k,
g(w) = w log w (principal log),

    psi(z) = g(z) - sum_i g(z - A_i) + sum_k g(z - B_k) - 2 pi i z + i pi sum_k B_k,

the saddle s (the root with Im s > 0 of the quadratic that clears the logarithms) and its level
kappa = Im psi(s):

  (L1) pi A_max < kappa < pi B_min (IsEuclid.pi_faceSum_lt_level);
  (L2) on the real axis Im psi(u) = bdry(u) = pi (min(u,0) - sum min(u - A_i, 0)
       + sum min(u - B_k, 0) - 2u + sum B_k), at points on all five pieces;
  (L3) a level below pi A_max or above pi B_min is taken by bdry exactly once, counted on a fine
       grid (eq_of_bdry_eq_of_not_mem); a level inside (pi A_max, pi B_min) is taken three
       times (for the regular tetrahedron 7 pi / 2 at u = 17/6, 7/2, 17/4), so the hypothesis
       that the level is outside the middle is needed.

Control (must FAIL): (L1) for the other root s-bar of the quadratic (Im < 0), whose level with
the same principal-branch phase lies outside [pi A_max, pi B_min]: the bound is a property of the
upper-half-plane saddle, not of every root.
Run: .venv/bin/python -I scripts/asymptotics/level_check.py   (expect "RESULT: OK")
"""
import random
from mpmath import mp, mpf, mpc, log, pi, sqrt, im, conj

mp.dps = 30
FACES = [(0, 1, 2), (0, 4, 5), (3, 1, 5), (3, 4, 2)]
QUADS = [(0, 1, 3, 4), (1, 2, 4, 5), (2, 0, 5, 3)]
I = mpc(0, 1)


def vol2(l):
    a, b, c, d, e, f = (t * t for t in l)
    return (a*d*(-a - d + b + e + c + f) + b*e*(a + d - b - e + c + f) + c*f*(a + d + b + e - c - f)
            - a*b*c - a*e*f - d*b*f - d*e*c) / 144


def sums(l):
    return [sum(l[i] for i in f) for f in FACES], [sum(l[i] for i in q) for q in QUADS]


def euclid(l):
    for f in FACES:
        x, y, z = (l[i] for i in f)
        if not (x < y + z and y < x + z and z < x + y):
            return False
    return vol2(l) > 0


def xlog(w):
    return w * log(w) if w != 0 else mpc(0)


def psi(A, B, z):
    return (xlog(z) - sum(xlog(z - a) for a in A) + sum(xlog(z - b) for b in B)
            - 2 * pi * I * z + pi * I * sum(B))


def saddle(A, B):
    def Q(x):
        p = x
        for b in B:
            p *= (b - x)
        q = mpf(1)
        for a in A:
            q *= (x - a)
        return p + q
    q0, q1p, q1m = Q(mpf(0)), Q(mpf(1)), Q(mpf(-1))
    q2, q1 = (q1p + q1m) / 2 - q0, (q1p - q1m) / 2
    r = sqrt(mpc(q1 * q1 - 4 * q2 * q0))
    s = (-q1 + r) / (2 * q2)
    return s if im(s) > 0 else (-q1 - r) / (2 * q2)


def bdry(A, B, u):
    return pi * (min(u, 0) - sum(min(u - a, 0) for a in A) + sum(min(u - b, 0) for b in B)
                 - 2 * u + sum(B))


def count_level(A, B, lev, lo, hi, n=20000):
    """Number of sign changes of bdry - lev on a grid of [lo, hi] (bdry is piecewise linear)."""
    xs = [lo + (hi - lo) * mpf(k) / n for k in range(n + 1)]
    vals = [bdry(A, B, x) - lev for x in xs]
    return sum(1 for a, b in zip(vals, vals[1:]) if (a < 0) != (b < 0))


def main():
    ok = True
    rng = random.Random(20261111)
    tets = [[mpf(1)] * 6]
    while len(tets) < 300:
        l = [mpf(rng.uniform(0.5, 3)) for _ in range(6)]
        if euclid(l):
            tets.append(l)
    lo_gap, hi_gap = mpf('inf'), mpf('inf')
    for l in tets:
        A, B = sums(l)
        k = im(psi(A, B, saddle(A, B)))
        lo_gap = min(lo_gap, k - pi * max(A))
        hi_gap = min(hi_gap, pi * min(B) - k)
    A, B = sums(tets[0])
    kr = im(psi(A, B, saddle(A, B)))
    l1 = lo_gap > 0 and hi_gap > 0
    print(f"(L1) regular: kappa = {mp.nstr(kr, 10)} in (3 pi, 4 pi) = ({mp.nstr(3 * pi, 8)}, "
          f"{mp.nstr(4 * pi, 8)}); {len(tets)} tetrahedra: min(kappa - pi A_max) = "
          f"{mp.nstr(lo_gap, 4)}, min(pi B_min - kappa) = {mp.nstr(hi_gap, 4)}: "
          f"{'OK' if l1 else 'FAIL'}")
    ok &= l1
    worst = mpf(0)
    for l in tets[:20]:
        A, B = sums(l)
        for u in (-1, max(A) / 2, (max(A) + min(B)) / 2, min(B) + 1, sum(B)):
            u = mpf(u)
            worst = max(worst, abs(im(psi(A, B, mpc(u, mpf('1e-25')))) - bdry(A, B, u)))
    l2 = worst < mpf('1e-15')
    print(f"(L2) Im psi = bdry on the real axis: max deviation {mp.nstr(worst, 3)}: "
          f"{'OK' if l2 else 'FAIL'}")
    ok &= l2
    bad = 0
    for l in tets[:30]:
        A, B = sums(l)
        lo, hi = -2 * max(B), 3 * sum(B)
        for frac in (mpf('0.3'), mpf('0.9')):
            bad += count_level(A, B, pi * max(A) * frac, lo, hi) != 1
        for extra in (mpf('0.2'), mpf(3)):
            bad += count_level(A, B, pi * min(B) + extra, lo, hi) != 1
    A, B = sums(tets[0])
    mid = count_level(A, B, 7 * pi / 2, mpf(-8), mpf(36))
    twice = abs(bdry(A, B, mpf(17) / 6) - 7 * pi / 2) + abs(bdry(A, B, mpf(17) / 4) - 7 * pi / 2)
    l3 = bad == 0 and mid == 3 and twice < mpf('1e-25')
    print(f"(L3) outside levels taken once: {120 - bad}/120; regular level 7 pi/2 taken {mid} "
          f"times (17/6, 7/2, 17/4): {'OK' if l3 else 'FAIL'}")
    ok &= l3
    out = 0
    for l in tets:
        A, B = sums(l)
        kb = im(psi(A, B, conj(saddle(A, B))))
        out += not (pi * max(A) < kb < pi * min(B))
    control = out > 0
    print(f"control (lower root s-bar): level outside (pi A_max, pi B_min) for {out}/{len(tets)}: "
          f"{'fails as it must' if control else 'UNEXPECTED PASS'}")
    ok &= control
    print("RESULT:", "OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
