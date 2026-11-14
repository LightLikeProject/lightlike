"""Numerical check (not a proof) of the orthogonality of the 15j symbols of the first kind,
Lightlike/Recoupling/Orthogonality.lean (sum_fifteenJ_mul_fifteenJ), in physical units:

  sum_{a2..a5} prod_t (2a_t+1) {15j}(a,b,c) {15j}(a,b',c) = delta_{bb'} / prod_{t=2..5} (2b_t+1)

for fixed a1, b1, c1..c5, with a_{t+1} <= a_t + c_t (the ranges of the Lean statement), when the
vertices (b1 c1 b2), (b2 c2 b3), (b3 c3 b4), (b4 c4 b5), (b5 c5 a1) are admissible, and 0 otherwise.
{15j} as in fifteenj_check.py (Dona and Sarno, arXiv:1807.03066, eq. (5)).

Controls (wrong inputs): without the weights (2a_t+1), and with the untwisted closure, the
relation must fail.
"""
import itertools
import math
import random
import sys
from functools import lru_cache
from sympy import Rational as R
from sympy.physics.wigner import wigner_6j


def adm(a, b, c):
    return (a + b + c) == int(a + b + c) and abs(a - b) <= c <= a + b


@lru_cache(maxsize=None)
def w6(*j):
    j1, j2, j3, j4, j5, j6 = j
    if not (adm(j1, j2, j3) and adm(j1, j5, j6) and adm(j4, j2, j6) and adm(j4, j5, j3)):
        return 0.0
    return float(wigner_6j(*j))


def fifteen(a, b, c, twist=True):
    A = list(a) + ([b[0]] if twist else [a[0]])
    B = list(b) + ([a[0]] if twist else [b[0]])
    s = sum(a) + sum(b) + sum(c)
    if s != int(s):
        return 0.0
    tot = 0.0
    for n in range(int(2 * (a[0] + b[0])) + 1):
        x = R(n, 2)
        p = 1.0
        for t in range(5):
            p *= w6(A[t], B[t], x, B[t + 1], A[t + 1], c[t])
            if p == 0.0:
                break
        tot += float(2 * x + 1) * p
    return (-1) ** int(s) * tot


def a_chains(a1, c):
    # all (a2..a5) with a_{t+1} <= a_t + c_t, half-integer steps (the Lean ranges, physical units)
    def rec(prev, t):
        if t == 4:
            yield ()
            return
        for n in range(int(2 * (prev + c[t])) + 1):
            x = R(n, 2)
            for rest in rec(x, t + 1):
                yield (x,) + rest
    return list(rec(a1, 0))


def rhs(a1, b, bp, c):
    chain = [b[0]] + list(b[1:]) + [a1]
    ok = all(adm(chain[t], c[t], chain[t + 1]) for t in range(5))
    if tuple(b) != tuple(bp) or not ok:
        return 0.0
    return 1.0 / math.prod(float(2 * x + 1) for x in b[1:])


def b_chains(b1, a1, c):
    out = []
    for bb in itertools.product([R(k, 2) for k in range(7)], repeat=4):
        chain = [b1] + list(bb) + [a1]
        if all(adm(chain[t], c[t], chain[t + 1]) for t in range(5)):
            out.append([b1] + list(bb))
    return out


random.seed(5)
sp = [R(k, 2) for k in range(4)]
n = bad = nz = ctrl_w = ctrl_t = 0
tries = 0
while n < 80 and tries < 5000:
    tries += 1
    a1, b1 = random.choice(sp), random.choice(sp)
    c = [random.choice(sp) for _ in range(5)]
    bs = b_chains(b1, a1, c)
    if len(bs) < 2:
        continue
    chains = a_chains(a1, c)
    if len(chains) > 4000:
        continue
    for _ in range(4):
        b = random.choice(bs)
        bp = b if random.random() < 0.5 else random.choice(bs)
        lhs = lhs_w = lhs_t = 0.0
        for aa in chains:
            a = [a1] + list(aa)
            w = math.prod(float(2 * x + 1) for x in aa)
            f, fp = fifteen(a, b, c), fifteen(a, bp, c)
            lhs += w * f * fp
            lhs_w += f * fp
            lhs_t += w * fifteen(a, b, c, False) * fifteen(a, bp, c, False)
        r = rhs(a1, b, bp, c)
        n += 1
        nz += r != 0
        bad += abs(lhs - r) > 1e-9
        ctrl_w += abs(lhs_w - r) > 1e-9
        ctrl_t += abs(lhs_t - r) > 1e-9
print(f"orthogonality: {n} cases ({nz} with nonzero right side), {bad} mismatches")
print(f"controls: without weights fails in {ctrl_w}, untwisted closure fails in {ctrl_t} (expected > 0)")
ok = bad == 0 and nz > 0 and ctrl_w > 0 and ctrl_t > 0
print("OK" if ok else "FAIL")
sys.exit(0 if ok else 1)
