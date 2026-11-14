"""Numerical check (not a proof) of `RacahSumAsymptotics` (Lightlike/Asymptotics/Assembly.lean),
proven in Lightlike/Asymptotics/SaddleAssembly.lean (`racahSumAsymptotics`):

    sqrt(sqrt(vol2(l))) * exp(-D(l)) * racahSum(lambda j)  -  cos(S_Regge(l) + pi/4) / (sqrt(12 pi) (2 pi)^2)  ->  0,

with l_e = lambda j_e + 1/2, D = prefactorRate (Saddle.lean), S_Regge = sum_e l_e theta_e (exterior
dihedral angles) and racahSum the exact alternating sum of Assembly.lean (Python integers).
An independent check of the constant and the phase in the Lean statement: if either were wrong, the
statement would be false, and the controls below show that the check would notice.

Normalised error: eps(lambda) = | sqrt(12 pi) (2 pi)^2 sqrt(sqrt(vol2)) e^{-D} racahSum - cos(S + pi/4) |,
reported as the maximum over windows of 5 consecutive lambda.
Acceptance (same as scripts/pr_asymptotics.py):
  - window max at lambda in [76, 80] < 0.05 for every tetrahedron;
  - log-log slope of the window maxima <= -0.8 between [10, 14] and [76, 80].
Controls (must FAIL, window max at [76, 80] >= 0.1 for every tetrahedron):
  - phase cos(S) without the pi/4;
  - constant (2 pi)^(5/2) in place of (2 pi)^2.
Run: .venv/bin/python -I scripts/asymptotics/racah_sum_asymptotics.py   (expect "RESULT: OK")
"""
import math
from fractions import Fraction
from mpmath import mp, mpf, sqrt, cos, acos, pi, log, exp

mp.dps = 60


def racah_sum(J):
    """racahSum of Assembly.lean at integer spins J = (J0..J5), exactly."""
    face = [J[0] + J[1] + J[2], J[0] + J[4] + J[5], J[3] + J[1] + J[5], J[3] + J[4] + J[2]]
    quad = [J[0] + J[1] + J[3] + J[4], J[1] + J[2] + J[4] + J[5], J[2] + J[0] + J[5] + J[3]]
    s = Fraction(0)
    for t in range(max(face), min(quad) + 1):
        den = 1
        for a in face:
            den *= math.factorial(t - a)
        for b in quad:
            den *= math.factorial(b - t)
        s += Fraction((-1) ** t * math.factorial(t + 1), den)
    return s


def geometry(l):
    """vol2 and exterior dihedral angles from lengths (AB, BC, CA, CD, AD, BD), as in PonzanoRegge."""
    AB, BC, CA, CD, AD, BD = l
    a, b, c, d, e, f = AB, BC, CA, CD, AD, BD
    V2 = (a*a*d*d*(-a*a - d*d + b*b + e*e + c*c + f*f) + b*b*e*e*(a*a + d*d - b*b - e*e + c*c + f*f)
          + c*c*f*f*(a*a + d*d + b*b + e*e - c*c - f*f)
          - a*a*b*b*c*c - a*a*e*e*f*f - d*d*b*b*f*f - d*d*e*e*c*c) / 144
    dist = {frozenset("AB"): AB, frozenset("BC"): BC, frozenset("CA"): CA,
            frozenset("CD"): CD, frozenset("AD"): AD, frozenset("BD"): BD}
    L = lambda u, v: dist[frozenset((u, v))]

    def interior(P, Q, R, S):
        pq = L(P, Q)
        ru = (L(P, R)**2 + pq**2 - L(Q, R)**2) / (2 * pq)
        su = (L(P, S)**2 + pq**2 - L(Q, S)**2) / (2 * pq)
        rs = (L(P, R)**2 + L(P, S)**2 - L(R, S)**2) / 2
        return acos((rs - ru * su) / sqrt((L(P, R)**2 - ru**2) * (L(P, S)**2 - su**2)))
    edges = [("A", "B", "C", "D"), ("B", "C", "A", "D"), ("C", "A", "B", "D"),
             ("C", "D", "A", "B"), ("A", "D", "B", "C"), ("B", "D", "A", "C")]
    return V2, [pi - interior(*e) for e in edges]


def prefactor_rate(l):
    """prefactorRate of Saddle.lean: 1/2 (sum_i A_i log A_i - sum_i sum_k (B_k - A_i) log(B_k - A_i))."""
    A = [l[0] + l[1] + l[2], l[0] + l[4] + l[5], l[3] + l[1] + l[5], l[3] + l[4] + l[2]]
    B = [l[0] + l[1] + l[3] + l[4], l[1] + l[2] + l[4] + l[5], l[2] + l[0] + l[5] + l[3]]
    return (sum(a * log(a) for a in A) - sum((b - a) * log(b - a) for a in A for b in B)) / 2


def eps(j, lam, phase0=pi / 4, const=(2 * pi) ** 2):
    l = [mpf(lam * x) + mpf(1) / 2 for x in j]
    V2, theta = geometry(l)
    S = sum(li * ti for li, ti in zip(l, theta))
    rs = racah_sum([lam * x for x in j])
    val = sqrt(sqrt(V2)) * exp(-prefactor_rate(l)) * mpf(rs.numerator) / mpf(rs.denominator)
    return abs(sqrt(12 * pi) * const * val - cos(S + phase0))


TETS = {"regular (1,1,1,1,1,1)": (1, 1, 1, 1, 1, 1),
        "irregular (2,2,2,2,2,3)": (2, 2, 2, 2, 2, 3),
        "irregular (2,3,3,2,3,2)": (2, 3, 3, 2, 3, 2)}
WINDOWS = [range(10, 15), range(20, 25), range(40, 45), range(76, 81)]

if __name__ == "__main__":
    ok = True
    for name, j in TETS.items():
        mx = [max(eps(j, lam) for lam in w) for w in WINDOWS]
        slope = float((log(mx[-1]) - log(mx[0])) / (log(78) - log(12)))
        good = mx[-1] < 0.05 and slope <= -0.8
        ok &= good
        print(f"{name}: window max eps = " + ", ".join(f"{float(e):.4f}" for e in mx) +
              f"; log-log slope {slope:.2f} [{'pass' if good else 'FAIL'}]")
    for label, kw in [("phase cos(S), no pi/4", {"phase0": mpf(0)}),
                      ("constant (2 pi)^(5/2)", {"const": (2 * pi) ** mpf(2.5)})]:
        for name, j in TETS.items():
            m = max(eps(j, lam, **kw) for lam in WINDOWS[-1])
            fails = m >= 0.1
            ok &= fails
            print(f"control [{label}] {name}: window max eps at 76-80 = {float(m):.4f} "
                  f"[{'fails as it should' if fails else 'DOES NOT FAIL'}]")
    print("RESULT: OK" if ok else "RESULT: FAIL")
    raise SystemExit(0 if ok else 1)
