"""Saddle-point identities behind the Ponzano-Regge formula (numerical evidence, not a proof).

Racah's sum for {lambda j} has summands Gamma-ratios whose Stirling exponent, written in the
shifted lengths l_e = lambda j_e + 1/2, is lambda * psi(sigma / lambda) with

    psi(x) = x log x - sum_i (x - A_i) log(x - A_i) - sum_k (B_k - x) log(B_k - x) + i pi x,

A_i = face perimeters, B_k = sums over the four edges avoiding an opposite pair (principal logs).
Its critical points solve the quadratic Q(x) = x prod(B_k - x) + prod(x - A_i) = q2 x^2 + q1 x + q0.
This script checks, for real edge lengths of Euclidean tetrahedra:

  (I1) q1^2 - 4 q2 q0 = -576 vol2 and q2 = 2 (l0 l3 + l1 l4 + l2 l5);
  (I2) psi'(x+) = 0 with principal branches, x+ = (-q1 + 24 i sqrt(vol2)) / (2 q2);
  (I3) Re psi(x+) = D = 1/2 sum_faces [P log P - sum over the three P - 2a terms t log t];
  (I4) Im psi(x+) = S_Regge(l) = sum_e l_e theta_e (exterior dihedral angles), exactly;
  (I5) per edge, the principal arguments add up to theta_e;
  (I6) K = i prod(x+ - A_i)^(-1/2) / sqrt(-psi''(x+)) has |K| = 1/sqrt(24 V), arg K = pi/4,
       i.e. the saddle gives cos(S_Regge + pi/4) / sqrt(12 pi V) exactly;
  (I7) landing structure: Im psi(u + i0) = kappa = Im psi(x+) has exactly three real solutions
       u_L < A_max < u_M < B_min < u_R, with F(u_L) < c < F(u_M), F(u_R) < c (F = Re psi on R).

Control (must FAIL): (I4) with interior instead of exterior angles.
Run: .venv/bin/python -I scripts/asymptotics/saddle_identities.py   (expect "RESULT: OK")
"""
import random
from mpmath import mp, mpf, mpc, log, pi, sqrt, acos, re, im, arg, fabs

mp.dps = 40
FACES = [(0, 1, 2), (0, 4, 5), (3, 1, 5), (3, 4, 2)]
QUADS = [(0, 1, 3, 4), (1, 2, 4, 5), (2, 0, 5, 3)]


def vol2(l):
    a, b, c, d, e, f = (t * t for t in l)
    return (a*d*(-a - d + b + e + c + f) + b*e*(a + d - b - e + c + f) + c*f*(a + d + b + e - c - f)
            - a*b*c - a*e*f - d*b*f - d*e*c) / 144


def cos_dihedral(pq, pr, qr, ps, qs, rs):
    ru = (pr**2 + pq**2 - qr**2) / (2 * pq)
    su = (ps**2 + pq**2 - qs**2) / (2 * pq)
    return ((pr**2 + ps**2 - rs**2) / 2 - ru * su) / sqrt((pr**2 - ru**2) * (ps**2 - su**2))


def interior_angles(l):
    AB, BC, CA, CD, AD, BD = l
    return [acos(cos_dihedral(AB, CA, BC, AD, BD, CD)), acos(cos_dihedral(BC, AB, CA, BD, CD, AD)),
            acos(cos_dihedral(CA, BC, AB, CD, AD, BD)), acos(cos_dihedral(CD, CA, AD, BC, BD, AB)),
            acos(cos_dihedral(AD, AB, BD, CA, CD, BC)), acos(cos_dihedral(BD, AB, AD, BC, CD, CA))]


def check(l, control=False):
    A = [sum(l[e] for e in f) for f in FACES]
    B = [sum(l[e] for e in q) for q in QUADS]
    Q = lambda x: x * (B[0] - x) * (B[1] - x) * (B[2] - x) + (x - A[0]) * (x - A[1]) * (x - A[2]) * (x - A[3])
    q0 = Q(mpf(0)); q1 = (Q(mpf(1)) - Q(mpf(-1))) / 2; q2 = (Q(mpf(1)) + Q(mpf(-1))) / 2 - q0
    V2 = vol2(l); V = sqrt(V2)
    err = {}
    err["I1"] = max(fabs(q1**2 - 4*q2*q0 + 576*V2), fabs(q2 - 2*(l[0]*l[3] + l[1]*l[4] + l[2]*l[5])))
    xp = mpc(-q1 / (2*q2), 12 * V / q2)
    psi = xp*log(xp) - sum((xp - a)*log(xp - a) for a in A) - sum((b - xp)*log(b - xp) for b in B) + 1j*pi*xp
    dpsi = log(xp) - sum(log(xp - a) for a in A) + sum(log(b - xp) for b in B) + 1j*pi
    d2psi = 1/xp - sum(1/(xp - a) for a in A) - sum(1/(b - xp) for b in B)
    err["I2"] = fabs(dpsi)
    xl = lambda t: t * log(t)
    D = sum((xl(l[a] + l[b] + l[c]) - xl(l[a] + l[b] - l[c]) - xl(l[a] - l[b] + l[c]) - xl(-l[a] + l[b] + l[c])) / 2
            for a, b, c in FACES)
    err["I3"] = fabs(re(psi) - D)
    phi = interior_angles(l)
    theta = [(phi[e] if control else pi - phi[e]) for e in range(6)]
    err["I4"] = fabs(im(psi) - sum(l[e] * theta[e] for e in range(6)))
    al = [arg(xp - a) for a in A]; be = [-arg(b - xp) for b in B]
    err["I5"] = max(fabs(sum(al[i] for i in range(4) if e in FACES[i]) +
                         sum(be[k] for k in range(3) if e in QUADS[k]) - theta[e]) for e in range(6))
    g = mp.e ** (-sum(log(xp - a) for a in A) / 2)
    sq = 1 / sqrt(-d2psi)
    K = 1j * g * sq
    err["I6"] = min(fabs(K - mp.e ** (1j*pi/4) / sqrt(24*V)), fabs(K + mp.e ** (1j*pi/4) / sqrt(24*V)))
    # I7: landing structure
    c, kap = re(psi), im(psi)
    def L(u):
        s = pi*u + (pi*u if u < 0 else 0)
        s -= sum(pi*(u - a) for a in A if u < a)
        s += sum(pi*(b - u) for b in B if u > b)
        return s
    def F(u):
        f = lambda w: w * log(fabs(w)) if w != 0 else mpf(0)
        return f(u) - sum(f(u - a) for a in A) - sum(f(b - u) for b in B)
    pts = sorted(set([mpf(0)] + A + B)); grid = [pts[0] - 100] + pts + [pts[-1] + 100]
    roots = []
    for a0, b0 in zip(grid[:-1], grid[1:]):
        fa, fb = L(a0) - kap, L(b0) - kap
        if fa * fb < 0:
            roots.append(a0 + (b0 - a0) * fa / (fa - fb))
    ok7 = (len(roots) == 3 and roots[0] < max(A) < roots[1] < min(B) < roots[2]
           and F(roots[0]) < c < F(roots[1]) and F(roots[2]) < c)
    err["I7"] = mpf(0) if ok7 else mpf(1)
    return err


def random_tetrahedron(rng):
    while True:
        P = [[rng.gauss(0, 1) for _ in range(3)] for _ in range(4)]
        if rng.random() < 0.3:
            s = 10 ** rng.uniform(-2, 0)
            for p in P:
                p[2] *= s
        d = lambda i, j: sqrt(sum((mpf(P[i][k]) - mpf(P[j][k]))**2 for k in range(3)))
        l = [d(0, 1), d(1, 2), d(2, 0), d(2, 3), d(0, 3), d(1, 3)]
        if vol2(l) > 0:
            return l


def main():
    rng = random.Random(2026)
    samples = [[mpf(x) for x in t] for t in [(1.5,)*6, (2.5, 2.5, 2.5, 2.5, 2.5, 3.5), (8.5, 4.5, 8.5, 8.5, 4.5, 8.5)]]
    samples += [random_tetrahedron(rng) for _ in range(300)]
    worst = {}
    for l in samples:
        for k, v in check(l).items():
            worst[k] = max(worst.get(k, mpf(0)), v)
    for k in sorted(worst):
        print(f"{k}: max error {float(worst[k]):.3e}")
    control = max(check(l, control=True)["I4"] for l in samples[:20])
    print(f"control (interior angles in I4): min over samples of the error should be large; got max {float(control):.3e}")
    ok = all(worst[k] < mpf(10) ** -25 for k in worst) and control > 1
    print("RESULT:", "OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
