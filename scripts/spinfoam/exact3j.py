"""Exact Wigner 3j symbols for `gauge_cutoff_limit.py`.

`vertex_check.threej` sums the Racah formula in floating point: for doubled spins around 20 and more the
alternating sum loses all digits. Here the sum is exact (integers and fractions) and only the final
square root is taken, with mpmath at 60 digits, then rounded to a float, so each 3j symbol is correct
to double precision.
"""
import math
from fractions import Fraction
from functools import lru_cache

import mpmath

mpmath.mp.dps = 60


@lru_cache(maxsize=None)
def threej_exact(j1, j2, j3, m1, m2, m3):
    """Wigner 3j symbol, doubled spins and projections (same convention as `vertex_check.threej`)."""
    if m1 + m2 + m3 != 0:
        return 0.0
    for j, m in ((j1, m1), (j2, m2), (j3, m3)):
        if abs(m) > j or (j - m) % 2:
            return 0.0
    if (j1 + j2 + j3) % 2 or j3 > j1 + j2 or j1 > j2 + j3 or j2 > j1 + j3:
        return 0.0
    f = math.factorial
    h = lambda x: x // 2
    delta = Fraction(f(h(j1 + j2 - j3)) * f(h(j1 - j2 + j3)) * f(h(-j1 + j2 + j3)),
                     f(h(j1 + j2 + j3) + 1))
    pre2 = delta * (f(h(j1 + m1)) * f(h(j1 - m1)) * f(h(j2 + m2)) * f(h(j2 - m2))
                    * f(h(j3 + m3)) * f(h(j3 - m3)))
    s = Fraction(0)
    for k in range(0, h(j1 + j2 + j3) + 2):
        args = [k, h(j3 - j2 + m1) + k, h(j3 - j1 - m2) + k, h(j1 + j2 - j3) - k, h(j1 - m1) - k,
                h(j2 + m2) - k]
        if min(args) < 0:
            continue
        den = 1
        for x in args:
            den *= f(x)
        s += Fraction((-1) ** k, den)
    val = mpmath.sqrt(mpmath.mpf(pre2.numerator) / mpmath.mpf(pre2.denominator)) \
        * (mpmath.mpf(s.numerator) / mpmath.mpf(s.denominator))
    return float((-1) ** h(j1 - j2 - m3) * val)
