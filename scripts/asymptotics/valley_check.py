"""Valleys of the continued phase at the saddle (numerical evidence, not a proof).

Checks the statements of Lightlike/Asymptotics/Valley.lean (step G3) for the regular unit
tetrahedron and for random Euclidean tetrahedra. With face sums A_i, quadrilateral sums B_k,

    psi(z) = g(z) - sum_i g(z - A_i) + sum_k g(z - B_k) - 2 pi i z + i pi sum_k B_k,  g(w) = w log w,

saddle s (Im s > 0, psi'(s) = 0), psi''(s) = 2b, u0 with b u0^2 = -|b|, |u0| = 1:

  (V1) psi''(s) = -896/81 - (136 sqrt2 / 81) i for the regular tetrahedron, |psi''(s)| = 8 sqrt2;
  (V2) Taylor bound: |psi(z) - psi(c) - psi'(c)(z-c) - psi''(c)/2 (z-c)^2| <= 32/(Im c)^2 |z-c|^3
       for |z - c| <= Im c / 2 (random centres c and points z);
  (V3) valley rays s + t eps u0 (1 + i tau), |tau| <= 1/2, 0 <= t <= r with
       r = min(Im s / 3, |b| / (8 K0)), K0 = 32 / (Im s)^2:
       |psi(s+tv) - psi(s) - b v^2 t^2| <= 4 K0 t^3 and Re psi(s+tv) <= Re psi(s) - |b| t^2 / 4;
  (V4) end-point levels: Im psi(s + r v) >= Im psi(s) + |b| r^2/2 at tau = -1/2 and
       <= Im psi(s) - |b| r^2/2 at tau = +1/2, in both valleys.

Control (must FAIL): (V3) in the direction i u0 (b (i u0)^2 = +|b|), where Re psi rises.
Run: .venv/bin/python -I scripts/asymptotics/valley_check.py   (expect "RESULT: OK")
"""
import random
from mpmath import mp, mpf, mpc, log, pi, sqrt, fabs, re, im

mp.dps = 40
FACES = [(0, 1, 2), (0, 4, 5), (3, 1, 5), (3, 4, 2)]
QUADS = [(0, 1, 3, 4), (1, 2, 4, 5), (2, 0, 5, 3)]
I = mpc(0, 1)


def vol2(l):
    a, b, c, d, e, f = (t * t for t in l)
    return (a*d*(-a - d + b + e + c + f) + b*e*(a + d - b - e + c + f) + c*f*(a + d + b + e - c - f)
            - a*b*c - a*e*f - d*b*f - d*e*c) / 144


def sums(l):
    return [sum(l[i] for i in f) for f in FACES], [sum(l[i] for i in q) for q in QUADS]


def xlog(w):
    return w * log(w) if w != 0 else mpc(0)


def psi(A, B, z):
    return (xlog(z) - sum(xlog(z - a) for a in A) + sum(xlog(z - b) for b in B)
            - 2 * pi * I * z + pi * I * sum(B))


def dpsi(A, B, z):
    return log(z) - sum(log(z - a) for a in A) + sum(log(z - b) for b in B) - 2 * pi * I


def d2psi(A, B, z):
    return 1 / z - sum(1 / (z - a) for a in A) + sum(1 / (z - b) for b in B)


def saddle(A, B):
    def Q(x):
        p = x
        for b in B:
            p *= (b - x)
        q = mpf(1)
        for a in A:
            q *= (x - a)
        return p + q
    q0 = Q(mpf(0))
    q1p = Q(mpf(1))
    q1m = Q(mpf(-1))
    q2 = (q1p + q1m) / 2 - q0
    q1 = (q1p - q1m) / 2
    disc = q1 * q1 - 4 * q2 * q0
    return (-q1 + sqrt(mpc(disc))) / (2 * q2) if im(sqrt(mpc(disc)) / q2) > 0 else \
        (-q1 - sqrt(mpc(disc))) / (2 * q2)


def euclid(l):
    for f in FACES:
        x, y, z = (l[i] for i in f)
        if not (x < y + z and y < x + z and z < x + y):
            return False
    return vol2(l) > 0


def valley_data(A, B):
    s = saddle(A, B)
    b = d2psi(A, B, s) / 2
    u0 = sqrt(-fabs(b) / b)
    K0 = 32 / im(s) ** 2
    r = min(im(s) / 3, fabs(b) / (8 * K0))
    return s, b, u0, K0, r


def check_rays(A, B, direction_factor=1):
    """(V3) on a grid; returns the worst slack (>= 0 means the bounds hold)."""
    s, b, u0, K0, r = valley_data(A, B)
    u = direction_factor * u0
    ps = psi(A, B, s)
    worst = mpf('inf')
    for eps in (1, -1):
        for tau in [mpf(k) / 8 - mpf(1) / 2 for k in range(9)]:
            v = eps * u * (1 + I * tau)
            for t in [r * k / 10 for k in range(1, 11)]:
                z = s + t * v
                err = fabs(psi(A, B, z) - ps - b * v * v * t * t)
                worst = min(worst, 4 * K0 * t ** 3 - err,
                            (re(ps) - fabs(b) * t * t / 4) - re(psi(A, B, z)))
    return worst


def check_levels(A, B):
    s, b, u0, K0, r = valley_data(A, B)
    kappa = im(psi(A, B, s))
    worst = mpf('inf')
    for eps in (1, -1):
        lo = im(psi(A, B, s + r * eps * u0 * (1 - I / 2)))
        hi = im(psi(A, B, s + r * eps * u0 * (1 + I / 2)))
        worst = min(worst, lo - (kappa + fabs(b) * r * r / 2), (kappa - fabs(b) * r * r / 2) - hi)
    return worst


def check_taylor(A, B, rng, n=40):
    worst = mpf('inf')
    s = saddle(A, B)
    for _ in range(n):
        c = s + mpc(rng.uniform(-1, 1), rng.uniform(-0.5, 2)) * im(s)
        if im(c) <= 0:
            continue
        rho = rng.uniform(0, 0.5) * im(c)
        ang = rng.uniform(0, 6.283185307179586)
        z = c + rho * mpc(mp.cos(ang), mp.sin(ang))
        rem = fabs(psi(A, B, z) - psi(A, B, c) - dpsi(A, B, c) * (z - c)
                   - d2psi(A, B, c) / 2 * (z - c) ** 2)
        worst = min(worst, 32 / im(c) ** 2 * fabs(z - c) ** 3 - rem)
    return worst


def main():
    ok = True
    A, B = sums([mpf(1)] * 6)
    s = saddle(A, B)
    target = mpc(mpf(-896) / 81, -136 * sqrt(2) / 81)
    v1 = fabs(d2psi(A, B, s) - target) < mpf(10) ** -30 and \
        fabs(fabs(d2psi(A, B, s)) - 8 * sqrt(2)) < mpf(10) ** -30
    print(f"(V1) regular psi''(s) = {mp.nstr(d2psi(A, B, s), 12)}; |psi'(s)| = "
          f"{mp.nstr(fabs(dpsi(A, B, s)), 3)}: {'OK' if v1 else 'FAIL'}")
    ok &= v1
    rng = random.Random(20261110)
    tets = [[mpf(1)] * 6]
    while len(tets) < 12:
        l = [mpf(rng.uniform(1, 2)) for _ in range(6)]
        if euclid(l):
            tets.append(l)
    wt = min(check_taylor(*sums(l), rng) for l in tets)
    wr = min(check_rays(*sums(l)) for l in tets)
    wl = min(check_levels(*sums(l)) for l in tets)
    for name, w in (("(V2) Taylor bound", wt), ("(V3) valley rays", wr), ("(V4) end levels", wl)):
        print(f"{name}: worst slack {mp.nstr(w, 6)}: {'OK' if w >= 0 else 'FAIL'}")
        ok &= w >= 0
    wc = min(check_rays(*sums(l), direction_factor=I) for l in tets)
    control = wc < 0
    print(f"control (ascent direction i u0): worst slack {mp.nstr(wc, 6)}: "
          f"{'fails as it must' if control else 'UNEXPECTED PASS'}")
    ok &= control
    print("RESULT:", "OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
