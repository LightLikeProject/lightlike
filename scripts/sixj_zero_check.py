"""Numerical check (not a proof) of the closed form of a 6j symbol with a zero entry, in the
doubled units of Physlib's sixJSym:

  sixJSym 0 b c d e f = [b = c, e = f, (b e d) admissible] * (-1)^((b+e+d)/2) / sqrt((b+1)(e+1)).

Used for stage 6 (zero spins) of the Biedenharn-Elliott proof. Doubled spins 0..4 (spins 0..2).
"""
import itertools, sys
from sympy import Rational, S, sqrt, simplify
from sympy.physics.wigner import wigner_6j

def adm(a, b, c):
    return (a + b + c) == int(a + b + c) and abs(a - b) <= c <= a + b

def six_j(*j):
    j1, j2, j3, j4, j5, j6 = j
    if not (adm(j1, j2, j3) and adm(j1, j5, j6) and adm(j4, j2, j6) and adm(j4, j5, j3)):
        return S(0)
    return wigner_6j(*j)

bad = total = nonzero = 0
for B, C, D, E, F in itertools.product(range(5), repeat=5):
    v = six_j(0, *(Rational(k, 2) for k in (B, C, D, E, F)))
    tri = (B + E + D) % 2 == 0 and abs(B - E) <= D <= B + E
    w = (-1) ** ((B + E + D) // 2) / sqrt((B + 1) * (E + 1)) if (B == C and E == F and tri) else 0
    total += 1; nonzero += (w != 0); bad += simplify(v - w) != 0
print(f"{total} cases ({nonzero} nonzero): {bad} mismatches")
sys.exit(0 if bad == 0 and nonzero > 0 else 1)
