"""Numerical check (not a proof) of the Barrett-Crane vertex against published 10j values.

The vertex `bcVertex` of Lightlike/SpinFoam/BarrettCrane.lean is evaluated from its definition, in
floating point: the intertwiners `fourJ` from SymPy's 3j symbols (doubled spins), the legs of
`k5Legs` (a negated projection is a reversed index), the edge form `edgeSign` = (-1)^((j - m)/2),
and bcVertex = sum_i k5Contract(j; iota_{i_a})^2 over the channels i of the five nodes
(`k5Contract4_mul`). bcVertexBC = (-1)^(sum of doubled spins) * bcVertex.

Published values (Christensen's table of Riemannian 10j symbols computed with the Christensen-Egan
algorithm, jdc.math.uwo.ca/spin-foams/10j-samples/riemannian; exact rationals by Egan,
gregegan.net/SCIENCE/tenJ/tenJ.html):
  all ten spins 1/2: 7/18;  all spins 1: 307/1500;  all spins 3/2: 9263/73500;
  spins 1 on the edges (i, i+1) and 1/2 on the edges (i, i+2): -0.0943287037037036923959.
The edge labels are Christensen-Egan's j_{1,i} (vertex i to i+1) and j_{2,i} (vertex i to i+2).

Lean: Lightlike/SpinFoam/BarrettCraneValues.lean proves the values 7/18, 307/1500 and -163/1728.
Control (wrong input): intertwiners without the normalisation sqrt(k+1) give a different value.
"""
import itertools
import sys
from fractions import Fraction

import numpy as np
from sympy import Rational
from sympy.physics.wigner import wigner_3j


def tj(a, b, c, ma, mb, mc):
    return float(wigner_3j(Rational(a, 2), Rational(b, 2), Rational(c, 2),
                           Rational(ma, 2), Rational(mb, 2), Rational(mc, 2)))


def proj(j):
    return list(range(-j, j + 1, 2))


def tri(a, b, c):
    return (a + b + c) % 2 == 0 and c <= a + b and a <= b + c and b <= a + c


def four_j(j1, j2, j3, j4, k, normalised=True):
    P = [proj(x) for x in (j1, j2, j3, j4)]
    T = np.zeros([len(p) for p in P])
    for idx in itertools.product(*[range(len(p)) for p in P]):
        m = [P[t][idx[t]] for t in range(4)]
        s = sum((-1) ** ((k - mu) // 2) * tj(j1, j2, k, m[0], m[1], mu) * tj(k, j3, j4, -mu, m[2], m[3])
                for mu in proj(k))
        T[idx] = (np.sqrt(k + 1) if normalised else 1.0) * s
    return T


# k5Legs: the legs of node a as (edge, sign); edges 0:(0,1) 1:(0,2) 2:(0,3) 3:(0,4) 4:(1,2)
# 5:(1,3) 6:(1,4) 7:(2,3) 8:(2,4) 9:(3,4).
LEGS = [[(0, 1), (1, 1), (2, 1), (3, 1)], [(4, 1), (5, 1), (6, 1), (0, -1)],
        [(7, 1), (8, 1), (1, -1), (4, -1)], [(9, 1), (2, -1), (5, -1), (7, -1)],
        [(3, -1), (6, -1), (8, -1), (9, -1)]]


def bc_vertex(j, normalised=True):
    spins = [[j[e] for e, _ in L] for L in LEGS]
    chans = [[k for k in range(s[0] + s[1] + 1) if tri(s[0], s[1], k) and tri(k, s[2], s[3])] for s in spins]
    cache = {}

    def node(a, k):
        key = (tuple(spins[a]), k)
        if key not in cache:
            cache[key] = four_j(*spins[a], k, normalised)
        T = cache[key]
        for t, (_, sg) in enumerate(LEGS[a]):
            if sg < 0:
                T = np.flip(T, axis=t)
        return T

    letters = "abcdefghij"
    sub = ",".join("".join(letters[e] for e, _ in L) for L in LEGS) + "," + ",".join(letters[e] for e in range(10))
    W = [np.array([(-1) ** ((j[e] - m) // 2) for m in proj(j[e])], dtype=float) for e in range(10)]
    total = 0.0
    for ks in itertools.product(*chans):
        v = np.einsum(sub + "->", *[node(a, ks[a]) for a in range(5)], *W, optimize=True)
        total += v * v
    return total


def ce_spins(j1, j2):
    """Doubled spins in the library's edge order from Christensen-Egan's j_{1,i}, j_{2,i}."""
    pair = {(0, 1): 0, (0, 2): 1, (0, 3): 2, (0, 4): 3, (1, 2): 4, (1, 3): 5, (1, 4): 6, (2, 3): 7, (2, 4): 8, (3, 4): 9}
    j = [None] * 10
    for i in range(5):
        j[pair[tuple(sorted((i, (i + 1) % 5)))]] = j1[i]
        j[pair[tuple(sorted((i, (i + 2) % 5)))]] = j2[i]
    return j


def main():
    cases = [("all spins 1/2", [1] * 10, float(Fraction(7, 18))),
             ("all spins 1", [2] * 10, float(Fraction(307, 1500))),
             ("all spins 3/2", [3] * 10, float(Fraction(9263, 73500))),
             ("spins 1 on (i,i+1), 1/2 on (i,i+2)", ce_spins([2] * 5, [1] * 5), -0.0943287037037036923959)]
    ok = True
    for name, j, pub in cases:
        v = (-1) ** sum(j) * bc_vertex(j)
        good = abs(v - pub) < 1e-12
        ok &= good
        print(f"{name}: bcVertexBC = {v:.15f}, published {pub:.15f}: {'OK' if good else 'FAIL'}")
    bad = bc_vertex([1] * 10, normalised=False)
    detected = abs(bad - 7 / 18) > 1e-3
    ok &= detected
    print(f"control, intertwiners without sqrt(k+1), spins 1/2: {bad:.15f} vs 7/18: "
          f"{'detected' if detected else 'NOT detected'}")
    print("OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
