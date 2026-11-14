"""The contour identity for Racah's sum (numerical evidence, not a proof).

Checks the statements of Lightlike/Asymptotics/ContourIdentity.lean. For integer face sums
a_i and quadrilateral sums b_k, the kernel is

    f(z) = pi T(z) / sin(pi z),
    T(z) = prod_{j=0}^{a_0} (z - a_0 + 1 + j) * prod_{i=1}^{3} 1/Gamma(z - a_i + 1) * prod_k 1/Gamma(b_k - z + 1),

an entire T times pi / sin(pi z). With x1 < max a_i and x2 > min b_k real, and any path from x1 to
x2 through the upper half-plane,

  (C1) Racah's sum S = sum_t (-1)^t (t+1)! / (prod (t - a_i)! prod (b_k - t)!) equals
       -(1/pi) Im of the integral of f along the path, for three paths (semicircle, box, high
       arch); in Lean the integral is the difference Phi(x2) - Phi(x1) of a primitive
       (racahSum_eq_im_primitive);
  (C2) T(z) = Gamma(z + 2) prod_i 1/Gamma(z - a_i + 1) prod_k 1/Gamma(b_k - z + 1) at points of
       the upper half-plane (racahT_eq_Gamma);
  (C3) the residue of f at each integer t is (-1)^t T(t), and T(t) is Racah's term
       (tendsto_mul_racahKernel, racahT_natCast).

Control (must FAIL): starting the path at x1 between two poles with non-zero residue misses
those to its left, so the value is wrong; this is why the identity needs x1 < max a_i.
Run: .venv/bin/python -I scripts/asymptotics/contour_identity_check.py   (expect "RESULT: OK")
"""
from mpmath import mp, mpf, mpc, pi, sin, gamma, rgamma, quad, factorial, im, exp

mp.dps = 30
I = mpc(0, 1)
FACES = [(0, 1, 2), (0, 4, 5), (3, 1, 5), (3, 4, 2)]
QUADS = [(0, 1, 3, 4), (1, 2, 4, 5), (2, 0, 5, 3)]


def sums(J):
    return [sum(J[e] for e in f) for f in FACES], [sum(J[e] for e in q) for q in QUADS]


def racah_sum(a, b):
    s = mpf(0)
    for t in range(b[0] + 1):
        if all(t >= x for x in a) and all(t <= y for y in b):
            den = mpf(1)
            for x in a:
                den *= factorial(t - x)
            for y in b:
                den *= factorial(y - t)
            s += (-1) ** t * factorial(t + 1) / den
    return s


def T(a, b, z):
    p = mpc(1)
    for j in range(a[0] + 1):
        p *= z - a[0] + 1 + j
    for x in a[1:]:
        p *= rgamma(z - x + 1)
    for y in b:
        p *= rgamma(y - z + 1)
    return p


def f(a, b, z):
    return pi * T(a, b, z) / sin(pi * z)


def seg_integral(a, b, z0, z1):
    return quad(lambda t: f(a, b, z0 + t * (z1 - z0)) * (z1 - z0), [0, 1])


def path_integral(a, b, pts):
    return sum(seg_integral(a, b, p, q) for p, q in zip(pts, pts[1:]))


def arc_integral(a, b, x1, x2):
    c, r = (x1 + x2) / 2, (x2 - x1) / 2
    return quad(lambda th: f(a, b, c + r * exp(I * th)) * I * r * exp(I * th), [pi, pi / 2, 0])


def main():
    ok = True
    cases = [(1, 1, 1, 1, 1, 1), (2, 2, 2, 2, 2, 2), (2, 3, 2, 3, 2, 3), (1, 2, 3, 2, 2, 2)]
    worst = mpf(0)
    for J in cases:
        a, b = sums(J)
        S = racah_sum(a, b)
        x1, x2 = mpf(max(a)) - mpf('0.37'), mpf(min(b)) + mpf('0.61')
        vals = [arc_integral(a, b, x1, x2),
                path_integral(a, b, [mpc(x1), mpc(x1, 1), mpc(x2, 1), mpc(x2)]),
                path_integral(a, b, [mpc(x1), mpc(x1 - 2, 3), mpc(x2 + 1, 4), mpc(x2)])]
        for v in vals:
            worst = max(worst, abs(-im(v) / pi - S) / max(1, abs(S)))
        print(f"  J = {J}: S = {mp.nstr(S, 12)}, -(1/pi) Im int = "
              f"{', '.join(mp.nstr(-im(v) / pi, 12) for v in vals)}")
    c1 = worst < mpf('1e-15')
    print(f"(C1) S = -(1/pi) Im int_P f on 3 paths x {len(cases)} spins: max rel. error "
          f"{mp.nstr(worst, 3)}: {'OK' if c1 else 'FAIL'}")
    ok &= c1
    worst = mpf(0)
    for J in cases:
        a, b = sums(J)
        for z in (mpc('0.3', '0.7'), mpc('-4.2', '1.1'), mpc('7.9', '0.05'), mpc('2', '3')):
            g = gamma(z + 2)
            for x in a:
                g *= rgamma(z - x + 1)
            for y in b:
                g *= rgamma(y - z + 1)
            worst = max(worst, abs(T(a, b, z) - g) / max(1, abs(g)))
    c2 = worst < mpf('1e-20')
    print(f"(C2) polynomial form of T = Gamma form on the upper half-plane: max rel. deviation "
          f"{mp.nstr(worst, 3)}: {'OK' if c2 else 'FAIL'}")
    ok &= c2
    worst = mpf(0)
    for J in cases:
        a, b = sums(J)
        for t in range(-3, b[0] + 3):
            with mp.workdps(70):  # sin(pi z) near an integer cancels about 25 digits
                eps = mpf('1e-25')
                res = (eps * I) * f(a, b, t + eps * I)  # (z - t) f(z) at z = t + i eps
            term = mpf(0)
            if 0 <= t and all(t >= x for x in a) and all(t <= y for y in b):
                den = mpf(1)
                for x in a:
                    den *= factorial(t - x)
                for y in b:
                    den *= factorial(y - t)
                term = (-1) ** t * factorial(t + 1) / den
            worst = max(worst, abs(res - term) / max(1, abs(term)))
            worst = max(worst, abs((-1) ** t * T(a, b, t) - term) / max(1, abs(term)))
    c3 = worst < mpf('1e-9')
    print(f"(C3) residues (z - t) f(z) -> (-1)^t T(t) = Racah's term at t = -3..b_0+2: max rel. "
          f"deviation {mp.nstr(worst, 3)}: {'OK' if c3 else 'FAIL'}")
    ok &= c3
    a, b = sums(cases[2])
    S = racah_sum(a, b)
    v = arc_integral(a, b, mpf(max(a)) + mpf('0.5'), mpf(min(b)) + mpf('0.61'))
    control = abs(-im(v) / pi - S) > mpf('1e-3')
    print(f"control (x1 = max a + 1/2, between poles): -(1/pi) Im int = {mp.nstr(-im(v) / pi, 12)} "
          f"vs S = {mp.nstr(S, 12)}: {'fails as it must' if control else 'UNEXPECTED PASS'}")
    ok &= control
    print("RESULT:", "OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
