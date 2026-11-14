"""Numerical cross-check of the Ooguri vertex conventions (Lightlike/SpinFoam/Vertex.lean).

Numerical evidence, not proof. Doubled spins and projections throughout.

For random colourings of a 4-simplex it compares
  * the direct contraction of the five canonical intertwiners with the strand rule `firstVert`
    (orientation o = +1 and o = -1), computed here with numpy from the 3j symbols, and
  * the closed form `ampP` of Lightlike/SpinFoam/Vertex.lean: the 15j contraction `fifteenJSimplex`
    in the pentagram
    order (0, 2, 4, 1, 3) of the sorted vertices, times the signs listed in `ampP`.
Lean proves the two equal for all colourings (`vertexContr_eq`); this script checks the statement
independently, and the values that Lightlike/SpinFoam/Tests.lean proves: 1/2 on the cycle colouring
(`ampP_cycle`) and 1/sqrt 2 on the colouring with spin 1/2 on the three triangles and three
tetrahedra through the edge of positions 0, 1 (`ampP_tri`).

Wrong-input control: the 15j contraction with the identity labelling (0, 1, 2, 3, 4), i.e.
`fifteenJSimplex` fed directly with the vertex order, must disagree on some colouring, and it does
on the cycle colouring of Lightlike/SpinFoam/Tests.lean (value 0 instead of 1/2).

Run: .venv/bin/python -I scripts/spinfoam/vertex_check.py   (expects "OK")
"""
import itertools
import math
import random
import sys
from functools import lru_cache

import numpy as np


@lru_cache(maxsize=None)
def threej(j1, j2, j3, m1, m2, m3):
    """Wigner 3j symbol (Racah formula), doubled spins and projections."""
    if m1 + m2 + m3 != 0:
        return 0.0
    for j, m in ((j1, m1), (j2, m2), (j3, m3)):
        if abs(m) > j or (j - m) % 2:
            return 0.0
    if (j1 + j2 + j3) % 2 or j3 > j1 + j2 or j1 > j2 + j3 or j2 > j1 + j3:
        return 0.0
    f = math.factorial
    h = lambda x: x // 2
    delta = f(h(j1 + j2 - j3)) * f(h(j1 - j2 + j3)) * f(h(-j1 + j2 + j3)) / f(h(j1 + j2 + j3) + 1)
    pre = math.sqrt(delta * f(h(j1 + m1)) * f(h(j1 - m1)) * f(h(j2 + m2)) * f(h(j2 - m2))
                    * f(h(j3 + m3)) * f(h(j3 - m3)))
    s = 0.0
    for k in range(0, h(j1 + j2 + j3) + 2):
        args = [k, h(j3 - j2 + m1) + k, h(j3 - j1 - m2) + k, h(j1 + j2 - j3) - k, h(j1 - m1) - k,
                h(j2 + m2) - k]
        if min(args) < 0:
            continue
        s += (-1) ** k / np.prod([f(x) for x in args])
    return (-1) ** h(j1 - j2 - m3) * pre * s


def proj(j):
    return list(range(-j, j + 1, 2))


def sgn(e):
    return -1.0 if e % 2 else 1.0


@lru_cache(maxsize=None)
def fourj(j1, j2, j3, j4, k):
    """`fourJ j1 j2 j3 j4 k` as a numpy tensor indexed by projections."""
    T = np.zeros((j1 + 1, j2 + 1, j3 + 1, j4 + 1))
    for (a, m1), (b, m2), (c, m3), (d, m4) in itertools.product(
            enumerate(proj(j1)), enumerate(proj(j2)), enumerate(proj(j3)), enumerate(proj(j4))):
        T[a, b, c, d] = math.sqrt(k + 1) * sum(
            sgn((k - mu) // 2) * threej(j1, j2, k, m1, m2, mu) * threej(k, j3, j4, -mu, m3, m4)
            for mu in proj(k))
    return T


def cmat(j):
    """The bilinear form (-1)^((j - m)/2) delta_{m', -m}."""
    M = np.zeros((j + 1, j + 1))
    for i, m in enumerate(proj(j)):
        M[i, proj(j).index(-m)] = sgn((j - m) // 2)
    return M


def contract(tensors, pairs):
    names = {}
    letters = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'

    def idx(n):
        if n not in names:
            names[n] = letters[len(names)]
        return names[n]
    ops, subs = [], []
    for arr, legs in tensors:
        ops.append(arr)
        subs.append(''.join(idx(l) for l in legs))
    for a, b, M in pairs:
        ops.append(M)
        subs.append(idx(a) + idx(b))
    return float(np.einsum(','.join(subs) + '->', *ops, optimize='greedy'))


# --- the strand rule `firstVert` of Lightlike/SpinFoam/Vertex.lean, at the positions 0..4 of the
# sorted vertices ---
def inc(p):
    return -1 if p % 2 else 1


def inc_erase(p, q):
    """FourD.inc of the vertex at position q in the face opposite position p."""
    return inc(q if q < p else q - 1)


def first(o, a, b):
    if o * inc(a) * inc_erase(a, b) == 1:
        return a if inc_erase(a, b) == 1 else b
    return b if inc_erase(b, a) == 1 else a


def vertex_contr(o, J, K):
    """`vertexContr`: canonical intertwiners (legs succAbove 0, 2, 1, 3), strand rule `first`."""
    tensors = []
    for i in range(5):
        w = [x for x in range(5) if x != i]
        legs = [w[0], w[2], w[1], w[3]]
        sp = [J[frozenset((i, q))] for q in legs]
        tensors.append((fourj(*sp, K[i]), [(i, q) for q in legs]))
    pairs = []
    for a, b in itertools.combinations(range(5), 2):
        fa = first(o, a, b)
        sb = b if fa == a else a
        pairs.append(((fa, sb), (sb, fa), cmat(J[frozenset((a, b))])))
    return contract(tensors, pairs)


def fifteen_simplex(j, i):
    """Recoupling's `fifteenJSimplex`: vertex a has legs a+1..a+4 (mod 5), virtual spin on
    (a+1, a+2); edge ab (a < b) carries m at a and -m at b, with the sign (-1)^((j - m)/2)."""
    tensors = []
    for a in range(5):
        legs = [(a + d) % 5 for d in (1, 2, 3, 4)]
        sp = [j[tuple(sorted((a, b)))] for b in legs]
        tensors.append((fourj(*sp, i[a]), [(a, b) for b in legs]))
    pairs = [((a, b), (b, a), cmat(j[(a, b)])) for a in range(5) for b in range(a + 1, 5)]
    return contract(tensors, pairs)


PENT = (0, 2, 4, 1, 3)


def amp_closed(J, K):
    """`ampP` of Lightlike/SpinFoam/Vertex.lean."""
    Jp = lambda p, q: J[frozenset((p, q))]
    j = {(a, b): Jp(PENT[a], PENT[b]) for a in range(5) for b in range(a + 1, 5)}
    val = fifteen_simplex(j, [K[PENT[a]] for a in range(5)])
    e = (Jp(0, 2) + Jp(0, 4) + Jp(2, 4) + K[0] + (Jp(1, 3) + Jp(0, 1) + K[1]) // 2
         + (K[2] + Jp(2, 4) + Jp(1, 2)) // 2 + (Jp(2, 3) + Jp(0, 2) + K[2]) // 2 + K[2]
         + (K[3] + Jp(3, 4) + Jp(1, 3)) // 2 + K[4])
    return sgn(e) * val


def amp_identity(J, K):
    """Wrong input: `fifteenJSimplex` with the identity labelling of the vertices."""
    j = {(a, b): J[frozenset((a, b))] for a in range(5) for b in range(a + 1, 5)}
    return fifteen_simplex(j, list(K))


def tri(a, b, c):
    return (a + b + c) % 2 == 0 and a <= b + c and b <= a + c and c <= a + b


def random_colouring(rng, maxj):
    while True:
        J = {frozenset(p): rng.randint(0, maxj) for p in itertools.combinations(range(5), 2)}
        K = []
        for i in range(5):
            w = [x for x in range(5) if x != i]
            sp = [J[frozenset((i, q))] for q in (w[0], w[2], w[1], w[3])]
            ks = [k for k in range(2 * maxj + 1) if tri(sp[0], sp[1], k) and tri(k, sp[2], sp[3])]
            if not ks:
                break
            K.append(rng.choice(ks))
        if len(K) == 5:
            return J, K


def main():
    rng = random.Random(2026)
    bad = nonzero = 0
    for _ in range(300):
        J, K = random_colouring(rng, 2)
        ref = amp_closed(J, K)
        nonzero += abs(ref) > 1e-12
        for o in (1, -1):
            if abs(vertex_contr(o, J, K) - ref) > 1e-9:
                bad += 1
    # the cycle colouring of Lightlike/SpinFoam/Tests.lean
    J = {frozenset(p): 0 for p in itertools.combinations(range(5), 2)}
    for p in ((0, 1), (0, 3), (1, 2), (2, 3)):
        J[frozenset(p)] = 1
    K = [0, 1, 1, 0, 0]
    cyc = [vertex_contr(o, J, K) for o in (1, -1)] + [amp_closed(J, K)]
    wrong = amp_identity(J, K)
    # the edge colouring of Lightlike/SpinFoam/Tests.lean (`triJ`, `triK`)
    Je = {frozenset(p): int(min(p) >= 2) for p in itertools.combinations(range(5), 2)}
    Ke = [0, 0, 1, 1, 1]
    edge = [vertex_contr(o, Je, Ke) for o in (1, -1)] + [amp_closed(Je, Ke)]
    print('random colourings: nonzero', nonzero, 'mismatches', bad)
    print('cycle colouring: contraction o=+1, o=-1, closed form =', cyc, '; identity labelling =',
          wrong)
    print('edge colouring: contraction o=+1, o=-1, closed form =', edge, '; 1/sqrt 2 =',
          1 / math.sqrt(2))
    ok = bad == 0 and nonzero > 50 and all(abs(c - 0.5) < 1e-12 for c in cyc) and abs(wrong) < 1e-12
    ok = ok and all(abs(c - 1 / math.sqrt(2)) < 1e-12 for c in edge)
    print('OK' if ok else 'FAIL')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
