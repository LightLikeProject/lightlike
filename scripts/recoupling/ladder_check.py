"""Numerical check (not a proof) of the ladder results in Lightlike/Recoupling/Ladder.lean
and FifteenJ.lean, in physical units, with SymPy's 3j and 6j symbols.

rung(a a' b b' c) f (q) = sum_p f(p) (-1)^(a-p1) (-1)^(b-p2)
                          sum_mc (-1)^(c-mc) (a a' c; -p1 q1 mc)(b b' c; -p2 q2 -mc).

1. rung_coupled: rung applied to (a b x; . . xi) is (-1)^(2x + a'+b+c+x) {a b x; b' a' c}
   times (a' b' x; . . xi). Control: the sign (-1)^(a'+b'+c+x) must fail.
2. fifteenJ_eq_mobius: the closed Moebius ladder of five rungs, sum_p ladder(delta_p)(p2, p1),
   equals (-1)^(2 b1) times the 15j symbol of the first kind. Control: without the sign it fails.
"""
import itertools
import random
import sys
from functools import lru_cache
from sympy import Rational as R
from sympy.physics.wigner import wigner_3j, wigner_6j


def adm(a, b, c):
    return (a + b + c) == int(a + b + c) and abs(a - b) <= c <= a + b


def projs(j):
    return [-j + n for n in range(int(2 * j) + 1)]


@lru_cache(maxsize=None)
def w3(*a):
    return float(wigner_3j(*a))


@lru_cache(maxsize=None)
def w6(*j):
    j1, j2, j3, j4, j5, j6 = j
    if not (adm(j1, j2, j3) and adm(j1, j5, j6) and adm(j4, j2, j6) and adm(j4, j5, j3)):
        return 0.0
    return float(wigner_6j(*j))


def eps(j, m):
    return (-1) ** int(j - m)


def rung(a, a2, b, b2, c, f):
    out = {}
    for q in itertools.product(projs(a2), projs(b2)):
        tot = 0.0
        for p in itertools.product(projs(a), projs(b)):
            v = f.get(p, 0.0)
            if v == 0.0:
                continue
            k = sum(eps(c, mc) * w3(a, a2, c, -p[0], q[0], mc) * w3(b, b2, c, -p[1], q[1], -mc)
                    for mc in projs(c))
            tot += v * eps(a, p[0]) * eps(b, p[1]) * k
        out[q] = tot
    return out


def coupled(a, b, x, xi):
    return {p: w3(a, b, x, p[0], p[1], xi) for p in itertools.product(projs(a), projs(b))}


random.seed(2)
sp = [R(n, 2) for n in range(5)]
n = bad = ctrl = 0
while n < 200:
    a, b, a2, b2, c = [random.choice(sp) for _ in range(5)]
    xs = [x for x in [R(k, 2) for k in range(9)] if adm(a, b, x) and adm(a2, b2, x)]
    if not xs:
        continue
    x = random.choice(xs)
    xi = random.choice(projs(x))
    six = w6(a, b, x, b2, a2, c)
    lhs = rung(a, a2, b, b2, c, coupled(a, b, x, xi))
    rhs = coupled(a2, b2, x, xi)
    e = 2 * x + a2 + b + c + x
    e2 = a2 + b2 + c + x
    if e != int(e):
        continue
    n += 1
    bad += any(abs(lhs[q] - (-1) ** int(e) * six * rhs[q]) > 1e-9 for q in rhs)
    if e2 == int(e2):
        ctrl += any(abs(lhs[q] - (-1) ** int(e2) * six * rhs[q]) > 1e-9 for q in rhs)
print(f"rung eigenvectors: {n} cases, {bad} mismatches; wrong sign fails in {ctrl}")


def fifteen(a, b, c):
    A = list(a) + [b[0]]
    B = list(b) + [a[0]]
    s = sum(a) + sum(b) + sum(c)
    if s != int(s):
        return 0.0
    tot = 0.0
    for k in range(int(2 * (a[0] + b[0])) + 1):
        x = R(k, 2)
        p = 1.0
        for t in range(5):
            p *= w6(A[t], B[t], x, B[t + 1], A[t + 1], c[t])
        tot += float(2 * x + 1) * p
    return (-1) ** int(s) * tot


def mobius(a, b, c):
    A = list(a) + [b[0]]
    B = list(b) + [a[0]]
    tot = 0.0
    for p in itertools.product(projs(A[0]), projs(B[0])):
        f = {p: 1.0}
        for t in range(5):
            f = rung(A[t], A[t + 1], B[t], B[t + 1], c[t], f)
        tot += f.get((p[1], p[0]), 0.0)
    return tot


random.seed(4)
sp = [R(n, 2) for n in range(4)]
m = mbad = mctrl = 0
tries = 0
while m < 40 and tries < 200000:
    tries += 1
    a = [random.choice(sp) for _ in range(5)]
    b = [random.choice(sp) for _ in range(5)]
    c = [random.choice(sp) for _ in range(5)]
    A, B = a + [b[0]], b + [a[0]]
    if not all(adm(A[t], A[t + 1], c[t]) and adm(B[t], B[t + 1], c[t]) for t in range(5)):
        continue
    f = fifteen(a, b, c)
    if abs(f) < 1e-12:
        continue
    mo = mobius(a, b, c)
    m += 1
    mbad += abs(mo - (-1) ** int(2 * b[0]) * f) > 1e-9
    mctrl += abs(mo - f) > 1e-9
print(f"closed ladder = (-1)^(2 b1) 15j: {m} nonzero cases, {mbad} mismatches; "
      f"without the sign fails in {mctrl}")
ok = bad == 0 and ctrl > 0 and mbad == 0 and mctrl > 0
print("OK" if ok else "FAIL")
sys.exit(0 if ok else 1)
