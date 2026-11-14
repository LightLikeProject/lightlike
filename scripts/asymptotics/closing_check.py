"""The closing argument (numerical evidence, not a proof).

Checks the statements of Lightlike/Asymptotics/Closing.lean (step G5) for the regular unit
tetrahedron and for random Euclidean tetrahedra. With face sums A_i, quadrilateral sums B_k,
g(w) = w log w (principal log),

    psi(z) = g(z) - sum_i g(z - A_i) + sum_k g(z - B_k) - 2 pi i z + i pi sum_k B_k,

the saddle s, b = psi''(s)/2, u0 = sqrt(-|b|/b) (so b u0^2 = -|b|, |u0| = 1) and the valley
directions v = valleyDir u0 eps tau = eps u0 (1 + i tau), eps = +-1, |tau| <= 1/2:

  (C0) the valley-ray bounds hold on a grid of [0, r]: Im(s + t v) > 0 and
       Re psi(s + t v) <= Re psi(s) - |b| t^2 / 4 (r is the largest of 0.4, 0.3, ... that works);
  (C1) Laplace on a valley ray (laplace_valley):
       I(N) = int_0^r v exp(N (psi(s + t v) - psi(s))) dt = eps u0 sqrt(pi/(N|b|)) / 2 + O(1/N):
       N * err stays bounded and err falls by at least 4 when N grows by 8 (an O(N^-1/2) error
       would fall only by sqrt 8 = 2.8), for both valleys and tau in {-1/2, 0, 1/2};
  (C2) the two half-Gaussians add: |I_1(N) - I_{-1}(N)| / sqrt(pi/(N|b|)) -> 1;
  (C3) descent paths z' = -1/psi'(z) from s + r v_1 and s + r v_{-1} (tau = 0) land at two
       different real points, both outside (A_max, B_min) (IsEuclid.exists_landing_ne).

Control (must FAIL): the lower bound of (C2) for two rays in the SAME valley (tau = +-1/2):
|I_1(tau=1/2) - I_1(tau=-1/2)| / sqrt(pi/(N|b|)) -> 0, so G5 needs opposite valleys.
Run: .venv/bin/python -I scripts/asymptotics/closing_check.py   (expect "RESULT: OK")
"""
import cmath
import random
from mpmath import mp, mpf, mpc, log, pi, sqrt, fabs, re, im, exp, quad

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
    q0, q1p, q1m = Q(mpf(0)), Q(mpf(1)), Q(mpf(-1))
    q2, q1 = (q1p + q1m) / 2 - q0, (q1p - q1m) / 2
    r = sqrt(mpc(q1 * q1 - 4 * q2 * q0))
    s = (-q1 + r) / (2 * q2)
    return s if im(s) > 0 else (-q1 - r) / (2 * q2)


def vdir(u0, eps, tau):
    return eps * u0 * (1 + I * tau)


def valley_data(A, B):
    """(C0): s, |b|, u0 and the largest r on the list for which the valley-ray bounds hold."""
    s = saddle(A, B)
    b = d2psi(A, B, s) / 2
    nb = fabs(b)
    u0 = sqrt(-nb / b)
    D = re(psi(A, B, s))
    for r in (mpf('0.4'), mpf('0.3'), mpf('0.2'), mpf('0.1'), mpf('0.05')):
        ok = True
        for eps in (1, -1):
            for tau in (mpf(-1) / 2, mpf(0), mpf(1) / 2):
                v = vdir(u0, eps, tau)
                for k in range(1, 41):
                    t = r * k / 40
                    z = s + t * v
                    if im(z) <= 0 or re(psi(A, B, z)) > D - nb / 4 * t * t:
                        ok = False
        if ok:
            return s, nb, u0, r
    return None


def ray_integral(A, B, s, v, r, N):
    ps = psi(A, B, s)
    f = lambda t: v * exp(N * (psi(A, B, s + t * v) - ps))
    w = r / 200
    return quad(f, [0, w, 4 * w, 16 * w, r])


def check_laplace(A, B, data):
    """(C1), (C2) and the control; returns (worst C1 slack, worst C2 gap, worst control ratio)."""
    s, nb, u0, r = data
    Ns = [c / (nb * r * r) for c in (mpf(400), mpf(3200))]
    w1, w2, wc = mpf('inf'), mpf(0), mpf(0)
    ints = {}
    for eps in (1, -1):
        for tau in (mpf(-1) / 2, mpf(0), mpf(1) / 2):
            v = vdir(u0, eps, tau)
            errs = []
            for N in Ns:
                val = ray_integral(A, B, s, v, r, N)
                ints[(eps, tau, N)] = val
                errs.append(fabs(val - eps * u0 * sqrt(pi / (N * nb)) / 2))
            # C/N: err(8N)/err(N) <= 1/4 (an O(N^-1/2) error would give 0.35)
            w1 = min(w1, errs[0] / 4 - errs[1])
    for N in Ns[1:]:
        q = sqrt(pi / (N * nb))
        w2 = max(w2, fabs(fabs(ints[(1, mpf(0), N)] - ints[(-1, mpf(0), N)]) / q - 1))
        wc = max(wc, fabs(ints[(1, mpf(1) / 2, N)] - ints[(1, mpf(-1) / 2, N)]) / q)
    return w1, w2, wc


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


def check_landing(A, B, data):
    """(C3); returns (|x1 - x2|, worst outside-the-middle slack)."""
    s, nb, u0, r = data
    Af, Bf = [float(a) for a in A], [float(b) for b in B]
    lo, hi = max(Af), min(Bf)
    xs = []
    for eps in (1, -1):
        z = s + r * vdir(u0, eps, mpf(0))
        x = land(Af, Bf, complex(float(re(z)), float(im(z))))
        if x is None:
            return -1.0, -1.0
        xs.append(x)
    return abs(xs[0] - xs[1]), min(max(lo - x, x - hi) + 1e-6 for x in xs)


def main():
    ok = True
    rng = random.Random(20261111)
    tets = [[mpf(1)] * 6]
    while len(tets) < 12:
        l = [mpf(rng.uniform(1, 2)) for _ in range(6)]
        if euclid(l):
            tets.append(l)
    data = [valley_data(*sums(l)) for l in tets]
    c0 = all(d is not None for d in data)
    print(f"(C0) valley-ray bounds on a grid, r in {sorted({float(d[3]) for d in data if d})}: "
          f"{'OK' if c0 else 'FAIL'}")
    ok &= c0
    if not c0:
        print("RESULT: FAIL")
        return 1
    res = [check_laplace(*sums(l), d) for l, d in zip(tets, data)]
    w1 = min(x[0] for x in res)
    print(f"(C1) Laplace error O(1/N) on both valleys, three tilts: worst slack "
          f"{mp.nstr(w1, 6)}: {'OK' if w1 >= 0 else 'FAIL'}")
    ok &= w1 >= 0
    w2 = max(x[1] for x in res)
    print(f"(C2) opposite valleys: | |I_1 - I_-1| / sqrt(pi/(N|b|)) - 1 | <= {mp.nstr(w2, 6)}: "
          f"{'OK' if w2 < mpf('0.05') else 'FAIL'}")
    ok &= w2 < mpf('0.05')
    lands = [check_landing(*sums(l), d) for l, d in zip(tets, data)]
    sep = min(x[0] for x in lands)
    out = min(x[1] for x in lands)
    c3 = sep > 1e-3 and out >= 0
    print(f"(C3) opposite-valley descents land apart: min |x1 - x2| = {sep:.4g}, "
          f"outside-the-middle slack {out:.3g}: {'OK' if c3 else 'FAIL'}")
    ok &= c3
    wc = max(x[2] for x in res)
    control = wc < mpf('0.05')
    print(f"control (same valley, tau = +-1/2): max |I - I'| / sqrt(pi/(N|b|)) = "
          f"{mp.nstr(wc, 6)} -> 0: {'fails as it must' if control else 'UNEXPECTED PASS'}")
    ok &= control
    print("RESULT:", "OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
