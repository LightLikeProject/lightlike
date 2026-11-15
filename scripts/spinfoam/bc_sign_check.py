"""Numerical cross-check (not a proof) of the triangle 15j value of Lightlike/Spin4/VertexTests.lean.

Spin j/2 on the edges 01, 02, 12 of K5, zero elsewhere, intertwiners i1 = j/2 and 0 at the other
nodes: the 15j contraction (the Lean formula, evaluated with SymPy 3j symbols) is 1/sqrt(j+1), so
the Barrett-Crane vertex is 1/(j+1) (`bcVertex_triangle`). The three spins sum to 3j/2, a
half-integer for odd j, where the Baez-Christensen convention (-1)^(sum of doubled spins) gives
-1/(j+1) (`bcVertexBC_triangle_one`).

Wrong-input control: the same contraction with the intertwiner label i1 = 0 (not admissible for
the node (j, 0, 0, j) unless j = 0) gives 0, not 1/sqrt(j+1).

Run: python3 scripts/spinfoam/bc_sign_check.py   (needs sympy; expects "OK")
"""
import sys

from sympy import Rational as R, sqrt
from sympy.physics.wigner import wigner_3j


def tj(a, b, c, m1, m2, m3):
    return wigner_3j(R(a, 2), R(b, 2), R(c, 2), R(m1, 2), R(m2, 2), R(m3, 2))


def es(j, m):
    return (-1) ** ((j - m) // 2)


def fj(j1, j2, j3, j4, k, m1, m2, m3, m4):
    s = 0
    for mu in range(-k, k + 1, 2):
        s += (-1) ** ((k - mu) // 2) * tj(j1, j2, k, m1, m2, mu) * tj(k, j3, j4, -mu, m3, m4)
    return sqrt(k + 1) * s


def triangle(j, i1):
    pr = range(-j, j + 1, 2)
    tot = 0
    for m0 in pr:
        for m1 in pr:
            for m4 in pr:
                tot += (es(j, m0) * es(j, m1) * es(j, m4) * fj(j, j, 0, 0, 0, m0, m1, 0, 0)
                        * fj(j, 0, 0, j, i1, m4, 0, 0, -m0) * fj(0, 0, j, j, 0, 0, 0, -m1, -m4))
    return tot.simplify()


ok = True
for j in range(1, 6):
    v = triangle(j, j)
    good = (v - 1 / sqrt(j + 1)).simplify() == 0
    ctrl = triangle(j, 0) == 0
    print(j, v, 'matches 1/sqrt(j+1):', good, '; wrong label gives 0:', ctrl)
    ok = ok and good and ctrl
print('OK' if ok else 'FAIL')
sys.exit(0 if ok else 1)
