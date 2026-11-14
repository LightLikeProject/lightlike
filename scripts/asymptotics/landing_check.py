"""No landing in the middle of the real axis (numerical evidence, not a proof).

Checks the statements of Lightlike/Asymptotics/Landing.lean (step G4) for the regular unit
tetrahedron and for random Euclidean tetrahedra. With face sums A_i, quadrilateral sums B_k,
g(w) = w log w (principal log),

    psi(z)   = g(z) - sum_i g(z - A_i) + sum_k g(z - B_k) - 2 pi i z + i pi sum_k B_k,
    psi_M(z) = g(z) - sum_i g(z - A_i) - sum_k g(B_k - z) + i pi z,

and a real point p with 0 < p, A_i < p < B_k for all i, k (the middle interval):

  (L1) Im psi_M'(p) = pi, and psi_M'(p) is the boundary value of psi'(p + i eta), eta -> 0+;
       psi_M'(7/2) = log 7 + i pi for the regular tetrahedron;
  (L2) psi = psi_M on the closed upper half-disc around p of radius min(p - A_max, B_min - p)/2;
  (L3) the solution z of psi_M(z) = psi_M(p) + eps near p (Newton, eps > 0 small) has Im z < 0,
       so no point of the closed upper half-plane near p has psi(z) = psi(p) + eps;
  (L4) descent paths z' = -1/psi'(z) from random points below the saddle level land at a real
       x with x <= A_max or x >= B_min (RK4 integration in double precision).

Control (must FAIL): (L3) at p > B_max, where psi itself is holomorphic across the axis with
Im psi'(p) = -2 pi: there the solution of psi(z) = psi(p) + eps has Im z > 0.
Run: .venv/bin/python -I scripts/asymptotics/landing_check.py   (expect "RESULT: OK")
"""
import cmath
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


def dpsi(A, B, z):
    return log(z) - sum(log(z - a) for a in A) + sum(log(z - b) for b in B) - 2 * pi * I


def psiM(A, B, z):
    return xlog(z) - sum(xlog(z - a) for a in A) - sum(xlog(b - z) for b in B) + pi * I * z


def dpsiM(A, B, z):
    return log(z) - sum(log(z - a) for a in A) + sum(log(b - z) for b in B) + pi * I


def newton(f, df, target, z, n=60):
    for _ in range(n):
        z = z - (f(z) - target) / df(z)
    return z


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


def check_middle(A, B, rng):
    """(L1)-(L3) at random middle points; returns the worst slacks (>= 0 means OK)."""
    lo, hi = max(A), min(B)
    w1, w2, w3 = mpf('inf'), mpf('inf'), mpf('inf')
    for _ in range(5):
        p = lo + (hi - lo) * mpf(rng.uniform(0.05, 0.95))
        d = dpsiM(A, B, p)
        lim = dpsi(A, B, p + I * mpf(10) ** -25)
        w1 = min(w1, mpf(10) ** -20 - fabs(im(d) - pi), mpf(10) ** -20 - fabs(lim - d))
        rho = min(p - lo, hi - p) / 2
        for _ in range(10):
            z = p + rho * mpf(rng.uniform(0, 1)) * mp.expjpi(mpf(rng.uniform(0, 1)))
            w2 = min(w2, mpf(10) ** -30 - fabs(psi(A, B, z) - psiM(A, B, z)))
        for eps in (mpf(10) ** -2, mpf(10) ** -4, mpf(10) ** -6):
            z = newton(lambda z: psiM(A, B, z), lambda z: dpsiM(A, B, z),
                       psiM(A, B, p) + eps, p + eps / d)
            ok_root = fabs(psiM(A, B, z) - psiM(A, B, p) - eps) < mpf(10) ** -30
            w3 = min(w3, -im(z) if ok_root else mpf(-1))
    return w1, w2, w3


def control_right(A, B):
    """(L3) at p > B_max with psi itself; returns min Im z (> 0 means the obstruction is gone)."""
    p = max(B) + 1
    d = dpsi(A, B, p)
    worst = mpf('inf')
    for eps in (mpf(10) ** -2, mpf(10) ** -4, mpf(10) ** -6):
        z = newton(lambda z: psi(A, B, z), lambda z: dpsi(A, B, z), psi(A, B, p) + eps, p + eps / d)
        worst = min(worst, im(z))
    return worst


def fdpsi(A, B, z):
    return (cmath.log(z) - sum(cmath.log(z - a) for a in A) + sum(cmath.log(z - b) for b in B)
            - 2j * cmath.pi)


def land(A, B, z):
    """Integrate z' = -1/psi'(z) (Re psi falls at unit rate) until z reaches the real axis."""
    f = lambda w: -1 / fdpsi(A, B, w)
    dt = 1e-2
    for _ in range(200000):
        k1 = f(z)
        k2 = f(z + dt / 2 * k1) if (z + dt / 2 * k1).imag > 0 else None
        k3 = f(z + dt / 2 * k2) if k2 is not None and (z + dt / 2 * k2).imag > 0 else None
        k4 = f(z + dt * k3) if k3 is not None and (z + dt * k3).imag > 0 else None
        nz = z + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4) if k4 is not None else None
        if nz is None or nz.imag <= 0:
            dt /= 2
            if dt < 1e-13:
                return z.real
            continue
        z = nz
        if z.imag < 1e-11:
            return z.real
    return None


def check_landing(A, B, rng):
    """(L4); returns (worst slack, landings left of A_max, landings right of B_min)."""
    Af, Bf = [float(a) for a in A], [float(b) for b in B]
    s = saddle(A, B)
    D = float(re(psi(A, B, s)))
    lo, hi = max(Af), min(Bf)
    worst, nl, nr = float('inf'), 0, 0
    tries = 0
    while nl + nr < 6 and tries < 200:
        tries += 1
        z0 = complex(rng.uniform(-2, hi + 4), rng.uniform(0.05, 4))
        if float(re(psi(A, B, mpc(z0.real, z0.imag)))) >= D - 0.05:
            continue
        x = land(Af, Bf, z0)
        if x is None:
            return -1.0, nl, nr
        worst = min(worst, max(lo - x, x - hi) + 1e-6)
        nl += x <= lo + 1e-6
        nr += x >= hi - 1e-6
    return worst, nl, nr


def main():
    ok = True
    A, B = sums([mpf(1)] * 6)
    v = dpsiM(A, B, mpf(7) / 2)
    l1 = fabs(v - (log(7) + pi * I)) < mpf(10) ** -30
    print(f"(L1) regular psi_M'(7/2) = {mp.nstr(v, 12)} = log 7 + i pi: {'OK' if l1 else 'FAIL'}")
    ok &= l1
    rng = random.Random(20261110)
    tets = [[mpf(1)] * 6]
    while len(tets) < 12:
        l = [mpf(rng.uniform(1, 2)) for _ in range(6)]
        if euclid(l):
            tets.append(l)
    res = [check_middle(*sums(l), rng) for l in tets]
    for k, name in enumerate(("(L1) Im psi_M' = pi, boundary value of psi'",
                              "(L2) psi = psi_M on the upper half-disc",
                              "(L3) psi_M = psi_M(p) + eps only below the axis")):
        w = min(r[k] for r in res)
        print(f"{name}: worst slack {mp.nstr(w, 6)}: {'OK' if w >= 0 else 'FAIL'}")
        ok &= w >= 0
    wl, NL, NR = float('inf'), 0, 0
    for l in tets:
        w, nl, nr = check_landing(*sums(l), rng)
        wl, NL, NR = min(wl, w), NL + nl, NR + nr
    print(f"(L4) descent landings: {NL} left of A_max, {NR} right of B_min, none in between; "
          f"worst slack {wl:.3g}: {'OK' if wl >= 0 else 'FAIL'}")
    ok &= wl >= 0
    wc = min(control_right(*sums(l)) for l in tets)
    control = wc > 0
    print(f"control (L3 at p > B_max with psi): min Im z = {mp.nstr(wc, 6)} > 0: "
          f"{'fails as it must' if control else 'UNEXPECTED PASS'}")
    ok &= control
    print("RESULT:", "OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
