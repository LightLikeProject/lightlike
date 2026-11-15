"""Numerical check (not a proof) of Bing's house, Barrett and Naish-Guzman 2009, section 2.4.

Z = sum_c (2c+1) (sum_a (-1)^a (2a+1) {a c c; c c c})^2 with the inner sums over a = 0..2c.
Summing a and b first gives 1 (sum rule (6)); the simple cutoff (all spins <= Lambda) gives Z_Lambda
that does not settle. Exact rational arithmetic via sympy. Wrong-input control: flipping the sign
of the Racah factor breaks the sum rule.
"""
import sys
from sympy import Rational, S
from sympy.physics.wigner import wigner_6j

def racah(C, x, sign=1):
    # doubled spins C = 2c, x = 2a; term (-1)^((2C+x)/2) (x+1) {x/2 C/2 C/2; C/2 C/2 C/2}
    if x % 2 or C % 2:  # the triad (c c c) needs 3c integral, so odd C gives 0
        return S(0)
    j = Rational(C, 2)
    return (-1) ** ((2 * C + x) // 2) * (x + 1) * wigner_6j(Rational(x, 2), j, j, j, j, j) * sign

def inner(C, L):
    return sum(racah(C, x) for x in range(0, min(2 * C, L) + 1))

def z_cut(L):
    return sum((C + 1) * inner(C, L) ** 2 for C in range(0, L + 1))

def main():
    ok = True
    for C in range(0, 13):
        full = inner(C, 10 ** 6)
        ok &= full == (1 if C == 0 else 0)
    print('sum rule (6), C = 0..12:', ok)
    bad = sum(racah(2, x, -1 if x == 4 else 1) for x in range(5))
    print('wrong-input control (sign of the x=4 term flipped), C=2 sum:', bad, '(must be nonzero)')
    ok &= bad != 0
    zs = {L: z_cut(L) for L in (0, 1, 2, 3, 4, 6, 8, 12, 16, 20, 24, 28)}
    for L, z in zs.items():
        print('cutoff L (doubled spins <= L):', L, ' Z_L =', z, '=', float(z))
    ok &= zs[2] == Rational(37, 12)
    print('OK' if ok else 'FAIL')
    sys.exit(0 if ok else 1)

if __name__ == '__main__':
    main()
