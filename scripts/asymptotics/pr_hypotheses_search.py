"""Hypotheses of PR.PonzanoReggeFormula (numerical evidence, not a proof).

The statement assumes, for spins j = (j1..j6) labelled as in PonzanoRegge/ (j1 = AB, j2 = BC,
j3 = CA, j4 = CD, j5 = AD, j6 = BD; faces = triads (j1 j2 j3), (j1 j5 j6), (j4 j2 j6), (j4 j5 j3)):
  (H1) the weak triangle inequalities on the four faces (IsTriad), and
  (H2) vol2(j) > 0 (Euler-Tartaglia squared volume of the edge lengths j).

1. (H2) alone is not enough: for j = (1, 1, 3, 1, 5, 3), vol2 = 13/8 > 0 but the face (1, 1, 3) is
   not a triangle, so every 6j symbol {lambda j} vanishes, while cos(S_Regge + pi/4) does not tend to 0.
2. (H1) + (H2) need nothing more on the box j in {0..6}^6: every tuple satisfying both has four
   strict triangles with positive area, hence (Cayley-Menger, nested chain edge/face/tetrahedron) a
   genuine non-degenerate Euclidean tetrahedron with the given edge lengths.

Control: the same search without (H1) must find tuples with vol2 > 0 and a non-triangular face
(at least the counterexample above).

Exact integer arithmetic throughout (144 * vol2 and 16 * area^2 are integers).
"""
from itertools import product
from fractions import Fraction

def vol2_144(a, b, c, d, e, f):
    a, b, c, d, e, f = (x * x for x in (a, b, c, d, e, f))
    return (a*d*(-a - d + b + e + c + f) + b*e*(a + d - b - e + c + f) + c*f*(a + d + b + e - c - f)
            - a*b*c - a*e*f - d*b*f - d*e*c)

def tri_weak(a, b, c):
    return c <= a + b and a <= b + c and b <= a + c

def heron16(a, b, c):   # 16 * area^2
    return (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c)

def faces(j):
    j1, j2, j3, j4, j5, j6 = j
    return [(j1, j2, j3), (j1, j5, j6), (j4, j2, j6), (j4, j5, j3)]

def main():
    # 1. the counterexample
    j = (1, 1, 3, 1, 5, 3)
    v = Fraction(vol2_144(*j), 144)
    print("counterexample j =", j, " vol2 =", v, "=", float(v), " faces weakly triangular:",
          [tri_weak(*t) for t in faces(j)])
    assert v > 0 and not tri_weak(1, 1, 3)
    # 2. exhaustive search on {0..6}^6
    n_both = n_strict = n_vol_only_bad = 0
    examples_bad = []
    for j in product(range(7), repeat=6):
        if vol2_144(*j) <= 0:
            continue
        fs = faces(j)
        if all(tri_weak(*t) for t in fs):
            n_both += 1
            if all(heron16(*t) > 0 for t in fs):
                n_strict += 1
        else:
            n_vol_only_bad += 1
            if len(examples_bad) < 3:
                examples_bad.append(j)
    print("box {0..6}^6: tuples with (H1)+(H2):", n_both, "; of these with four strict faces:", n_strict)
    print("control: tuples with vol2 > 0 but a non-triangular face:", n_vol_only_bad,
          "e.g.", examples_bad)
    ok = (n_both == n_strict and n_vol_only_bad > 0)
    print("RESULT:", "OK" if ok else "FAIL")
    return 0 if ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
