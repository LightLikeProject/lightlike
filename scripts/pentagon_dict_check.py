"""Numerical check (not a proof) of the dictionary used to turn the Lean theorem
Lightlike.Pentagon.pentagon_rc into Biedenharn-Elliott in the form of Lightlike.beLHS = Lightlike.beRHS.

Pentagon spins (true spins): j1..j4, J12, J34, J123, J234, J; summed J23.
rc(x,y,z; T, X, Y) = (-1)^(x+y+z+T) sqrt((2X+1)(2Y+1)) {x y X; z T Y}   (Physlib's recoupling_eq_sixJ)
pentagon_rc:  rc(j1,j2,J34;J,J12,J234) rc(J12,j3,j4;J,J123,J34)
            = sum_J23 rc(j2,j3,j4;J234,J23,J34) rc(j1,J23,j4;J,J123,J234) rc(j1,j2,j3;J123,J12,J23)
Dictionary to BE letters: a=j2 b=j3 c=j4 d=J234 e=j1 f=J123 p=J34 q=J r=J12, x=J23.
Checks: (1) the rc-pentagon holds; (2) it equals BE (sign (-1)^(S+x), weight 2x+1) under the dictionary.
"""
import itertools, sys
from sympy import Rational, S, sqrt, simplify
from sympy.physics.wigner import wigner_6j

def adm(a, b, c):
    return (a + b + c) == int(a + b + c) and abs(a - b) <= c <= a + b

def sj(j1, j2, j3, j4, j5, j6):
    if not (adm(j1, j2, j3) and adm(j1, j5, j6) and adm(j4, j2, j6) and adm(j4, j5, j3)):
        return S(0)
    return wigner_6j(j1, j2, j3, j4, j5, j6)

def rc(x, y, z, T, X, Y):
    return (-1) ** int(x + y + z + T) * sqrt((2 * X + 1) * (2 * Y + 1)) * sj(x, y, X, z, T, Y)

half = [Rational(k, 2) for k in range(1, 4)]          # positive spins 1/2..3/2
allj = [Rational(k, 2) for k in range(0, 7)]
checked = nontriv = 0; err1 = err2 = 0.0
for j1, j2, j3, j4 in itertools.product(half, repeat=4):
    for J12, J34 in itertools.product(allj, repeat=2):
        if J12 == 0 or J34 == 0 or not adm(j1, j2, J12) or not adm(j3, j4, J34):
            continue
        for J123, J234, J in itertools.product(allj, repeat=3):
            if not (adm(J12, j3, J123) and adm(J123, j4, J) and adm(j2, J34, J234) and adm(j1, J234, J)):
                continue
            lhs = rc(j1, j2, J34, J, J12, J234) * rc(J12, j3, j4, J, J123, J34)
            rhs = sum(rc(j2, j3, j4, J234, x, J34) * rc(j1, x, j4, J, J123, J234) * rc(j1, j2, j3, J123, J12, x)
                      for x in allj)
            a, b, c, d, e, f, p, q, r = j2, j3, j4, J234, j1, J123, J34, J, J12
            Ssum = a + b + c + d + e + f + p + q + r
            be_l = sum((-1) ** int(Ssum + x) * (2 * x + 1) * sj(a, b, x, c, d, p) * sj(c, d, x, e, f, q)
                       * sj(e, f, x, b, a, r) for x in allj if (Ssum + x) == int(Ssum + x))
            be_r = sj(p, q, r, e, a, d) * sj(p, q, r, f, b, c)
            checked += 1; nontriv += (be_r != 0)
            err1 = max(err1, abs(float(lhs - rhs))); err2 = max(err2, abs(float(be_l - be_r)))
print(f"{checked} admissible labellings ({nontriv} nontrivial): rc-pentagon max err {err1:.1e}; BE via dictionary max err {err2:.1e}")
sys.exit(0 if err1 < 1e-12 and err2 < 1e-12 and nontriv > 0 else 1)
