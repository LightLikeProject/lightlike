"""Numerical check (not a proof) of the 15j results in Lightlike/Recoupling/FifteenJ.lean,
in physical (not doubled) units, with SymPy's 3j and 6j symbols.

15j symbol of the first kind (Donà and Sarno, arXiv:1807.03066, eq. (5)):
  {15j}(a, b, c) = (-1)^S sum_x (2x+1) prod_{t=1..5} {a_t b_t x; b_{t+1} a_{t+1} c_t},
  closure (a_6, b_6) = (b_1, a_1), S = sum of the fifteen spins.

4-simplex contraction: five 4-valent intertwiners iota (Martin-Dussaud eqs. (44)-(45)), vertex a
with legs a+1, a+2, a+3, a+4 (mod 5) and virtual spin i_a on the pair (a+1, a+2); edge ab (a < b)
with projection m at a, -m at b and sign (-1)^(j_ab - m).

1. Contraction = prod_a sqrt(2 i_a + 1) * {15j}(a, b, c) with a = (i0, j02, i2, j24, i4),
   b = (j14, i1, j13, i3, j03), c = (j01, j12, j23, j34, j04). Spins up to 3/2 (floating point).
   Controls (wrong inputs): the untwisted closure and the formula without (-1)^S must fail.
2. Zero-spin reduction (exact): for a_1 = 0, {15j} = (-1)^(S + (b1+a2+b2) + (b1+b5+a5))
   / sqrt((2a2+1)(2b5+1)) {a2 b2 b1; b3 a3 c2}{a3 b3 b1; b4 a4 c3}{a4 b4 b1; b5 a5 c4}
   if c1 = a2, c5 = b5 and the triads (b1 a2 b2), (b1 b5 a5) are admissible, else 0.
3. Values used by Lightlike/Recoupling/Tests.lean.
4. A value with all fifteen spins nonzero (Lightlike/Recoupling/Tests.lean, fifteenJ_all_nonzero):
  triangle spins 1/2,
   virtual spins 1, so a = (1, 1/2, 1, 1/2, 1), b = (1/2, 1, 1/2, 1, 1/2), c = (1/2, ..., 1/2).
   The 15j formula gives -7/432 (two terms, x = 1/2 and 3/2); the contraction of the ten 3j
   symbols, evaluated exactly from SymPy's wigner_3j and without the 6j formula, gives
   -7 sqrt(3)/48 = 9 sqrt(3) * (-7/432). Control: the untwisted closure gives 0.
"""
import itertools
import math
import random
import sys
from functools import lru_cache
from sympy import Rational as R, S, sqrt, simplify
from sympy.physics.wigner import wigner_3j, wigner_6j


def adm(a, b, c):
    return (a + b + c) == int(a + b + c) and abs(a - b) <= c <= a + b


def projs(j):
    return [-j + n for n in range(int(2 * j) + 1)]


def six(*j):
    j1, j2, j3, j4, j5, j6 = j
    if not (adm(j1, j2, j3) and adm(j1, j5, j6) and adm(j4, j2, j6) and adm(j4, j5, j3)):
        return S(0)
    return wigner_6j(*j)


@lru_cache(maxsize=None)
def w3(*a):
    return float(wigner_3j(*a))


@lru_cache(maxsize=None)
def w6(*a):
    return float(six(*a))


def iota_exact(j1, j2, j3, j4, k, m1, m2, m3, m4):
    """The intertwiner of `iota`, exactly, from SymPy's 3j symbols."""
    if not (adm(j1, j2, k) and adm(k, j3, j4)):
        return S(0)
    mu = -(m1 + m2)
    if abs(mu) > k or (k - mu) != int(k - mu):
        return S(0)
    return sqrt(2 * k + 1) * (-1) ** int(k - mu) * wigner_3j(j1, j2, k, m1, m2, mu) * wigner_3j(k, j3, j4, -mu, m3, m4)


@lru_cache(maxsize=None)
def iota(j1, j2, j3, j4, k, m1, m2, m3, m4):
    if not (adm(j1, j2, k) and adm(k, j3, j4)):
        return 0.0
    mu = -(m1 + m2)
    if abs(mu) > k or (k - mu) != int(k - mu):
        return 0.0
    return math.sqrt(2 * k + 1) * (-1) ** int(k - mu) * w3(j1, j2, k, m1, m2, mu) * w3(k, j3, j4, -mu, m3, m4)


def E(a, b):
    return (min(a, b), max(a, b))


EDGES = [E(a, b) for a in range(5) for b in range(a + 1, 5)]


def simplex(j, i, exact=False):
    zero, one, f = (S(0), S(1), iota_exact) if exact else (0.0, 1.0, iota)
    tot = zero
    for ms in itertools.product(*(projs(j[e]) for e in EDGES)):
        m = dict(zip(EDGES, ms))
        val = one
        for e in EDGES:
            val *= (-1) ** int(j[e] - m[e])
        for a in range(5):
            legs = [(a + t) % 5 for t in (1, 2, 3, 4)]
            mm = [m[E(a, b)] if a < b else -m[E(a, b)] for b in legs]
            if sum(mm) != 0:
                val = zero
                break
            v = f(*[j[E(a, b)] for b in legs], i[a], *mm)
            if v == 0:
                val = zero
                break
            val *= v
        tot += val
    return simplify(tot) if exact else tot


def fifteen(a, b, c, twist=True, phase=True, exact=False):
    A = list(a) + ([b[0]] if twist else [a[0]])
    B = list(b) + ([a[0]] if twist else [b[0]])
    s = sum(a) + sum(b) + sum(c)
    if s != int(s):
        return S(0) if exact else 0.0
    f = six if exact else w6
    tot = S(0) if exact else 0.0
    for n in range(int(2 * (a[0] + b[0])) + 1):
        x = R(n, 2)
        p = S(1) if exact else 1.0
        for t in range(5):
            p *= f(A[t], B[t], x, B[t + 1], A[t + 1], c[t])
            if p == 0:
                break
        tot += (2 * x + 1) * p if exact else float(2 * x + 1) * p
    return ((-1) ** int(s) if phase else 1) * tot if exact else float(((-1) ** int(s) if phase else 1) * tot)


def labels(j, i):
    a = (i[0], j[E(0, 2)], i[2], j[E(2, 4)], i[4])
    b = (j[E(1, 4)], i[1], j[E(1, 3)], i[3], j[E(0, 3)])
    c = (j[E(0, 1)], j[E(1, 2)], j[E(2, 3)], j[E(3, 4)], j[E(0, 4)])
    return a, b, c


def reduction(a, b, c):
    if not (c[0] == a[1] and c[4] == b[4] and adm(b[0], a[1], b[1]) and adm(b[0], b[4], a[4])):
        return S(0)
    s = sum(a) + sum(b) + sum(c)
    if s != int(s):
        return S(0)
    e = s + (b[0] + a[1] + b[1]) + (b[0] + b[4] + a[4])
    return ((-1) ** int(e) / sqrt((2 * a[1] + 1) * (2 * b[4] + 1)) * six(a[1], b[1], b[0], b[2], a[2], c[1])
            * six(a[2], b[2], b[0], b[3], a[3], c[2]) * six(a[3], b[3], b[0], b[4], a[4], c[3]))


# 1. contraction versus the 15j symbol of the first kind
random.seed(7)
spins = [R(n, 2) for n in range(4)]
n = bad = untw = noph = 0
tries = 0
while n < 400 and tries < 200000:
    tries += 1
    j = {e: random.choice(spins) for e in EDGES}
    i = []
    for a in range(5):
        legs = [(a + t) % 5 for t in (1, 2, 3, 4)]
        js = [j[E(a, b)] for b in legs]
        cand = [k for k in [R(m, 2) for m in range(9)] if adm(js[0], js[1], k) and adm(k, js[2], js[3])]
        if not cand:
            break
        i.append(random.choice(cand))
    if len(i) < 5:
        continue
    z = simplex(j, i)
    lab = labels(j, i)
    norm = math.sqrt(math.prod(float(2 * k + 1) for k in i))
    f = fifteen(*lab)
    if abs(z) < 1e-12 and abs(f) < 1e-12:
        continue
    n += 1
    bad += abs(z - norm * f) > 1e-9
    untw += abs(z - norm * fifteen(*lab, twist=False)) > 1e-9
    noph += abs(z - norm * fifteen(*lab, phase=False)) > 1e-9
print(f"contraction = prod sqrt(2i+1) * 15j_I: {n} nonzero cases, {bad} mismatches")
print(f"controls: untwisted closure fails in {untw}, no (-1)^S fails in {noph} (expected > 0)")

# 2. zero-spin reduction, exact, on configurations with all triads admissible at x = b_1
random.seed(11)
sp = [R(m, 2) for m in range(5)]
rn = rbad = 0
tries = 0
while rn < 200 and tries < 500000:
    tries += 1
    a = [S(0)] + [random.choice(sp) for _ in range(4)]
    b = [random.choice(sp) for _ in range(5)]
    c = [a[1]] + [random.choice(sp) for _ in range(3)] + [b[4]]
    A, B, x = a + [b[0]], b + [a[0]], b[0]
    if not all(adm(A[t], B[t], x) and adm(A[t], A[t + 1], c[t]) and adm(B[t + 1], B[t], c[t])
               and adm(B[t + 1], A[t + 1], x) for t in range(5)):
        continue
    v = fifteen(a, b, c, exact=True)
    if v == 0:
        continue
    rn += 1
    rbad += simplify(v - reduction(a, b, c)) != 0
print(f"zero-spin reduction: {rn} nonzero cases, {rbad} mismatches")

# 3. values for the Lean trust checks
h = R(1, 2)
v1 = fifteen([0] * 5, [h] * 5, [0, 0, 0, 0, h], exact=True)
v1u = fifteen([0] * 5, [h] * 5, [0, 0, 0, 0, h], twist=False, exact=True)
jc = {e: R(0) for e in EDGES}
for e in [(0, 3), (0, 4), (1, 3), (1, 4)]:
    jc[e] = h
zc = simplex(jc, [0, h, 0, h, 0])
z0 = simplex({e: R(0) for e in EDGES}, [0] * 5)
print(f"values: 15j(0; 1/2..; 0,0,0,0,1/2) = {v1}, untwisted = {v1u}, 4-cycle contraction = {zc}, "
      f"all-zero contraction = {z0}, all-zero 15j = {fifteen([0]*5, [0]*5, [0]*5, exact=True)}")

# 4. all fifteen spins nonzero: the 15j formula against the exact contraction of ten 3j symbols
j4 = {e: h for e in EDGES}
i4 = [S(1)] * 5
a4, b4, c4 = labels(j4, i4)
v4 = fifteen(a4, b4, c4, exact=True)
v4u = fifteen(a4, b4, c4, twist=False, exact=True)
z4 = simplex(j4, i4, exact=True)
lab_ok = (list(a4), list(b4), list(c4)) == ([1, h, 1, h, 1], [h, 1, h, 1, h], [h] * 5)
print(f"all spins nonzero: 15j({a4}; {b4}; {c4}) = {v4}, untwisted = {v4u}; "
      f"exact contraction of ten 3j symbols = {z4}, 9 sqrt(3) * 15j = {simplify(9 * sqrt(3) * v4)}")
ok = (n > 0 and bad == 0 and untw > 0 and noph > 0 and rn > 0 and rbad == 0 and v1 == R(1, 4)
      and v1u == 0 and abs(zc - 0.5) < 1e-12 and abs(z0 - 1) < 1e-12
      and lab_ok and v4 == R(-7, 432) and v4u == 0 and simplify(z4 + 7 * sqrt(3) / 48) == 0
      and simplify(z4 - 9 * sqrt(3) * v4) == 0)
print("OK" if ok else "FAIL")
sys.exit(0 if ok else 1)
