"""Exact cut-off sums of the tetrahedron: Z_N = sum over doubled spins <= N of prod(s_e+1) * 6j^2.

Numerical evidence for Lightlike/SpinFoam/TetrahedronCutoff.lean (not a proof). Doubled spins
s_e, 6j symbol {s0 s1 s2; s5 s4 s3} in Physlib's arrangement. Wrong-input control: a table with
one inadmissible triad has 6j = 0, and the all-2 symbol is 1/6.
Run: .venv/bin/python -I scripts/spinfoam/tetra_partition_check.py
"""
from itertools import product
from sympy import Rational, simplify
from sympy.physics.wigner import wigner_6j


def six_j(s):
    j = [Rational(x, 2) for x in s]
    try:
        return wigner_6j(j[0], j[1], j[2], j[5], j[4], j[3])
    except ValueError:  # an inadmissible triad: the symbol is 0
        return Rational(0)


def z(N):
    tot = 0
    for s in product(range(N + 1), repeat=6):
        w = 1
        for x in s:
            w *= x + 1
        v = six_j(s)
        if v != 0:
            tot += w * v**2
    return simplify(tot)


if __name__ == "__main__":
    assert six_j((2,) * 6) == Rational(1, 6), "all-2 control"
    assert six_j((1, 1, 1, 0, 0, 0)) == 0, "inadmissible triad control"
    prev = 0
    for N in range(0, 4):
        zn = z(N)
        assert zn >= prev
        prev = zn
        print(N, zn, float(zn))
