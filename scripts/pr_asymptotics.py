"""Numerical study (not a proof) of the Ponzano-Regge asymptotic formula for the 6j symbol:

    {6j}(lambda j) ~ cos( sum_e (lambda j_e + 1/2) theta_e + pi/4 ) / sqrt(12 pi V)

V is the volume and theta_e the exterior dihedral angles of the Euclidean tetrahedron with edge
lengths l_e = lambda j_e + 1/2. Same tetrahedron labelling as Lightlike/PonzanoRegge
(j1 = AB, j2 = BC, j3 = CA, j4 = CD, j5 = AD, j6 = BD; triads = faces).

The 6j value is exact: Racah's single-sum formula with Python integers, validated against
SymPy's wigner_6j in tv_check.py. Spins here are ordinary (not doubled).

Normalised error: eps(lambda) = | sqrt(12 pi V) {6j} - cos(Phi + pi/4) |, reported as the maximum over
windows of 5 consecutive lambda. A single lambda can be accidentally close when two cosines happen
to agree.
Acceptance:
  - window max at lambda in [76, 80] < 0.05;
  - log-log slope of the window maxima <= -0.8 between [10, 14] and [76, 80].
Control (--no-shift): l_e = lambda j_e. This changes the phase by the constant -1/2 sum theta_e, so the
window max must stay large (>= 0.1) in every window.
Exit 0 when every tetrahedron meets the acceptance criteria; the default run also runs the control
and exits 0 only if it is detected. With --no-shift, only the control runs (exit 1, as it must).
"""
import math, sys
from fractions import Fraction
from mpmath import mp, mpf, sqrt, cos, acos, pi, log

mp.dps = 50
HALF = mpf(1) / 2

def tri_ok(a, b, c):
    return a <= b + c and b <= a + c and c <= a + b

def six_j(j1, j2, j3, j4, j5, j6):
    """Classical 6j, ordinary integer spins, Racah formula (exact up to one square root)."""
    tri = [(j1, j2, j3), (j1, j5, j6), (j4, j2, j6), (j4, j5, j3)]
    if not all(tri_ok(*t) for t in tri):
        return mpf(0)
    d2 = Fraction(1)
    for a, b, c in tri:
        d2 *= Fraction(math.factorial(a + b - c) * math.factorial(a - b + c) *
                       math.factorial(-a + b + c), math.factorial(a + b + c + 1))
    al = [sum(t) for t in tri]
    be = [j1 + j2 + j4 + j5, j2 + j3 + j5 + j6, j3 + j1 + j6 + j4]
    s = Fraction(0)
    for z in range(max(al), min(be) + 1):
        den = 1
        for a in al:
            den *= math.factorial(z - a)
        for b in be:
            den *= math.factorial(b - z)
        s += Fraction((-1) ** z * math.factorial(z + 1), den)
    return sqrt(mpf(d2.numerator) / mpf(d2.denominator)) * mpf(s.numerator) / mpf(s.denominator)

def geometry(l):
    """Volume and exterior dihedral angles from edge lengths (AB, BC, CA, CD, AD, BD)."""
    AB, BC, CA, CD, AD, BD = l
    a, b, c, d, e, f = AB, BC, CA, CD, AD, BD   # opposite pairs (a,d), (b,e), (c,f)
    V2 = (a*a*d*d*(-a*a - d*d + b*b + e*e + c*c + f*f) + b*b*e*e*(a*a + d*d - b*b - e*e + c*c + f*f)
          + c*c*f*f*(a*a + d*d + b*b + e*e - c*c - f*f)
          - a*a*b*b*c*c - a*a*e*e*f*f - d*d*b*b*f*f - d*d*e*e*c*c) / 144
    dist = {frozenset("AB"): AB, frozenset("BC"): BC, frozenset("CA"): CA,
            frozenset("CD"): CD, frozenset("AD"): AD, frozenset("BD"): BD}
    L = lambda u, v: dist[frozenset((u, v))]
    def interior(P, Q, R, S):   # dihedral angle at edge PQ between faces PQR and PQS
        pq = L(P, Q)
        ru = (L(P, R)**2 + pq**2 - L(Q, R)**2) / (2 * pq)
        su = (L(P, S)**2 + pq**2 - L(Q, S)**2) / (2 * pq)
        rs = (L(P, R)**2 + L(P, S)**2 - L(R, S)**2) / 2
        return acos((rs - ru * su) / sqrt((L(P, R)**2 - ru**2) * (L(P, S)**2 - su**2)))
    edges = [("A", "B", "C", "D"), ("B", "C", "A", "D"), ("C", "A", "B", "D"),
             ("C", "D", "A", "B"), ("A", "D", "B", "C"), ("B", "D", "A", "C")]
    theta = [pi - interior(*e) for e in edges]
    return V2, theta

def eps(j, lam, shift=HALF):
    l = [mpf(lam * x) + shift for x in j]
    V2, theta = geometry(l)
    if V2 <= 0:
        return None
    phase = sum(li * ti for li, ti in zip(l, theta)) + pi / 4
    val = six_j(*[lam * x for x in j])
    return abs(sqrt(12 * pi * sqrt(V2)) * val - cos(phase))

TETS = {"regular (1,1,1,1,1,1)": (1, 1, 1, 1, 1, 1),
        "irregular (2,2,2,2,2,3)": (2, 2, 2, 2, 2, 3),
        "irregular (2,3,3,2,3,2)": (2, 3, 3, 2, 3, 2)}

WINDOWS = [range(10, 15), range(20, 25), range(40, 45), range(76, 81)]

def run(shift):
    """Window maxima and slope per tetrahedron; prints one line each."""
    tag = "[NO SHIFT] " if shift == 0 else ""
    out = {}
    for name, j in TETS.items():
        mx = [max(eps(j, lam, shift) for lam in w) for w in WINDOWS]
        slope = float((log(mx[-1]) - log(mx[0])) / (log(78) - log(12)))
        print(f"{tag}{name}: window max eps = " + ", ".join(f"{float(e):.4f}" for e in mx) +
              f" (windows 10-14, 20-24, 40-44, 76-80); log-log slope {slope:.2f}")
        out[name] = (mx, slope)
    return out

def accepted(mx, slope):
    return mx[-1] < 0.05 and slope <= -0.8

def main() -> int:
    if "--no-shift" in sys.argv:
        return 0 if all(accepted(*r) for r in run(mpf(0)).values()) else 1
    ok = all(accepted(*r) for r in run(HALF).values())
    caught = all(min(mx) >= 0.1 for mx, _ in run(mpf(0)).values())
    print("OK" if ok and caught else "FAIL: " + ("acceptance" if not ok else "the control was not detected"))
    return 0 if ok and caught else 1

if __name__ == "__main__":
    sys.exit(main())
