"""Numerical check (not a proof): both sides of Biedenharn-Elliott (beLHS, beRHS in the letters
of Lightlike/PonzanoRegge/BiedenharnElliott.lean) are invariant under the vertex
permutations of the 2-3 configuration (p=AB q=BC r=CA a=AD d=BD e=CD b=AE c=BE f=CE).
Exhaustive over doubled spins 0..2 (19,683 tuples); exact SymPy arithmetic.
"""
import itertools, sys
from sympy import Rational, S
from sympy.physics.wigner import wigner_6j

def adm(a, b, c):
    return (a + b + c) % 2 == 0 and abs(a - b) <= c <= a + b

def sj(j1, j2, j3, j4, j5, j6):  # doubled-unit arguments
    if not (adm(j1, j2, j3) and adm(j1, j5, j6) and adm(j4, j2, j6) and adm(j4, j5, j3)):
        return S(0)
    return wigner_6j(*(Rational(k, 2) for k in (j1, j2, j3, j4, j5, j6)))

def lhs(a, b, c, d, e, f, p, q, r):
    s = a + b + c + d + e + f + p + q + r
    return sum((-1) ** ((s + x) // 2) * (x + 1) * sj(a, b, x, c, d, p) * sj(c, d, x, e, f, q)
               * sj(e, f, x, b, a, r) for x in range(a + b + 1) if (s + x) % 2 == 0)

def rhs(a, b, c, d, e, f, p, q, r):
    return sj(p, q, r, e, a, d) * sj(p, q, r, f, b, c)

perms = {  # (a,b,c,d,e,f,p,q,r) -> permuted letters
    "D<->E": lambda a, b, c, d, e, f, p, q, r: (b, a, d, c, f, e, p, q, r),
    "A<->B": lambda a, b, c, d, e, f, p, q, r: (d, c, b, a, e, f, p, r, q),
    "A<->C": lambda a, b, c, d, e, f, p, q, r: (e, f, c, d, a, b, q, p, r),
    "B<->C": lambda a, b, c, d, e, f, p, q, r: (a, b, f, e, d, c, r, q, p),
}
tuples = list(itertools.product(range(3), repeat=9))  # exhaustive, doubled spins 0..2
bad = 0
for name, P in perms.items():
    bad_l = sum(lhs(*P(*t)) != lhs(*t) for t in tuples)
    bad_r = sum(rhs(*P(*t)) != rhs(*t) for t in tuples)
    nz = sum(rhs(*t) != 0 for t in tuples)
    print(f"{name}: LHS mismatches {bad_l}, RHS mismatches {bad_r} (of {len(tuples)}, {nz} with RHS != 0)")
    bad += bad_l + bad_r + (nz == 0)
sys.exit(0 if bad == 0 else 1)
