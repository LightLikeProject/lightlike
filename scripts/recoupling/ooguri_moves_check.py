"""Numerical check (not a proof) of the Pachner moves of the Ooguri (SU(2) BF) state sum.

Numerical evidence, not proof. Doubled spins and projections throughout. Floating point,
tolerance 1e-9 (relative).

The state sum is the one of Lightlike/SpinFoam/Ooguri.lean: a colouring gives every triangle
a spin and every tetrahedron the virtual spin of its canonical intertwiner, and has the weight

    prod over triangles (j + 1)  *  prod over 4-simplices vertexAmp(s, colouring),

where vertexAmp is the closed form of Lightlike/SpinFoam/Vertex.lean (the 15j symbol
`fifteenJSimplex` in the
pentagram order (s0, s2, s4, s1, s3) of the sorted vertices, times the signs of `ampP`). Lean
proves that this closed form is the contraction of the five intertwiners (`vertexContr_eq`);
scripts/spinfoam/vertex_check.py checks that independently.

A Pachner move on the six vertices S of a 5-simplex replaces the 4-simplices {S \\ a : a in A}
by {S \\ b : b in B}, where S = A + B. On the side of A the inner faces are those containing B;
they are summed (the triangles with weight j + 1, the tetrahedra over their admissible virtual
spins), the boundary faces are fixed at random admissible values.

Checks:
  3-3   (#A = #B = 3) the two sides agree, on random boundaries for all ten splittings
        (Lean: `amplitudeGF_move33`);
  2-4   (#A = 4) with the inner triangle B + {min A} fixed at spin y, the side of A is
        (y + 1)^2 times the side of B;
  1-5   (#A = 5) with the four inner triangles through B + {min A} fixed at spin y, the side of A
        is (y + 1)^8 times the side of B;
  value the state sum of the boundary of the 5-simplex (the 4-sphere with 6 4-simplices) with
        every triangle spin at most 1/2 is 7717715/243 = 31760.1440...;
  edge  the same state sum with every triangle that does not contain the edge {0, 1} at spin 0
        and the four triangles through it at spin 0 or 1/2 is 5 (Lean, with the faces outside
        the edge gauge-fixed at 0: `amplitudeGF_sphere6_edge` in Lightlike/SpinFoam/Tests.lean).
  gauge the gauge rule `IsGauge` of Ooguri.lean on the boundary of the 5-simplex: a set of ten
        triangles is collapsible together with the vertices and edges exactly when its spins 0
        force all twenty triangles to spin 0 (all 184756 sets); the state sum with the triangles
        of a gauge set at spin 0 and the others at spin <= 1/2 is 1 for the star of a vertex and
        for `twistT` (Lean: `amplitudeGF_starT`, `amplitudeGF_twistT`), and 5 for `gauge9`, the
        star without one triangle (control; Lean: `amplitudeGF_gauge9_one`).
  moves the Pachner moves 1-5, 2-4, 3-3 of Lightlike/FourD/Tests.lean on the boundary of the
  5-simplex,
        reimplemented from the definitions of Lightlike/FourD/Pachner.lean: each is a move, the
        moves with
        the two sides exchanged undo them, the Euler characteristic stays 2 (Lean:
        `pachner_move_move_predicts`, `pachner_euler4_predicts`). Controls: the 1-5 move repeated
        without exchanging the sides is not a move and returns K1; the unsigned face count is 62,
        then 92 (`pachner_repeat_fails`, `pachner_unsigned_euler_fails`).

Wrong-input controls (SF4b, SF5b): the 3-3 identity must FAIL for
  * a perturbed 15j: vertexAmp multiplied by 1.1 whenever the tetrahedron opposite the least
    vertex of the 4-simplex has virtual spin 1 (doubled 2);
  * the absolute value |vertexAmp|;
and the boundary value must change for |vertexAmp|.

Run: .venv/bin/python -I scripts/recoupling/ooguri_moves_check.py   (expects "OK")
"""
import itertools
import math
import random
import sys
from functools import lru_cache

import numpy as np

TOL = 1e-9


# --- 3j symbols, intertwiners and the 15j symbol (as in scripts/spinfoam/vertex_check.py) ---
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
    """Full contraction: `tensors` are (array, leg names), `pairs` are (leg, leg, matrix) with
    sum_{x,y} A[x] M[x,y] B[y]; every leg occurs in exactly one pair."""
    names = {}
    letters = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'

    def idx(n):
        if n not in names:
            names[n] = letters[len(names)]
        return names[n]
    ops, subs = [], []
    for arr, lg in tensors:
        ops.append(arr)
        subs.append(''.join(idx(l) for l in lg))
    for a, b, M in pairs:
        ops.append(M)
        subs.append(idx(a) + idx(b))
    return float(np.einsum(','.join(subs) + '->', *ops, optimize='greedy'))


def fifteen_simplex(j, i):
    """Recoupling's `fifteenJSimplex`: vertex a has legs a+1..a+4 (mod 5), virtual spin on
    (a+1, a+2); edge ab (a < b) carries m at a and -m at b, with the sign (-1)^((j - m)/2)."""
    tensors = []
    for a in range(5):
        lg = [(a + d) % 5 for d in (1, 2, 3, 4)]
        sp = [j[tuple(sorted((a, b)))] for b in lg]
        tensors.append((fourj(*sp, i[a]), [(a, b) for b in lg]))
    pairs = [((a, b), (b, a), cmat(j[(a, b)])) for a in range(5) for b in range(a + 1, 5)]
    return contract(tensors, pairs)


PENT = (0, 2, 4, 1, 3)
PAIRS = list(itertools.combinations(range(5), 2))


@lru_cache(maxsize=None)
def amp_closed(Jt, Kt):
    """`ampP` of Lightlike/SpinFoam/Vertex.lean; Jt[n] is the spin of the triangle opposite the
    positions PAIRS[n], Kt[i] the virtual spin of the tetrahedron opposite position i."""
    J = dict(zip(PAIRS, Jt))
    Jp = lambda p, q: J[(min(p, q), max(p, q))]
    j = {(a, b): Jp(PENT[a], PENT[b]) for a, b in PAIRS}
    val = fifteen_simplex(j, [Kt[PENT[a]] for a in range(5)])
    e = (Jp(0, 2) + Jp(0, 4) + Jp(2, 4) + Kt[0] + (Jp(1, 3) + Jp(0, 1) + Kt[1]) // 2
         + (Kt[2] + Jp(2, 4) + Jp(1, 2)) // 2 + (Jp(2, 3) + Jp(0, 2) + Kt[2]) // 2 + Kt[2]
         + (Kt[3] + Jp(3, 4) + Jp(1, 3)) // 2 + Kt[4])
    return sgn(e) * val


def local(s, col):
    """The colouring of the 4-simplex s at the positions of its sorted vertices."""
    srt = sorted(s)
    Jt = tuple(col[s - {srt[p], srt[q]}] for p, q in PAIRS)
    Kt = tuple(col[s - {srt[i]}] for i in range(5))
    return Jt, Kt


def vertex_amp(s, col):
    return amp_closed(*local(s, col))


def perturbed_amp(s, col):
    """Wrong input: the 15j multiplied by 1.1 when the tetrahedron opposite the least vertex has
    virtual spin 1."""
    Jt, Kt = local(s, col)
    return amp_closed(Jt, Kt) * (1.1 if Kt[0] == 2 else 1.0)


def abs_amp(s, col):
    """Wrong input: the absolute value of the 15j."""
    return abs(vertex_amp(s, col))


# --- complexes and state sums ---
def tri(a, b, c):
    return (a + b + c) % 2 == 0 and a <= b + c and b <= a + c and c <= a + b


def faces(S, k):
    return [frozenset(c) for c in itertools.combinations(sorted(S), k)]


def legs(t):
    """The legs t \\ w0, t \\ w2, t \\ w1, t \\ w3 of the canonical intertwiner of t."""
    w = sorted(t)
    return [t - {w[0]}, t - {w[2]}, t - {w[1]}, t - {w[3]}]


def virtual(col, t):
    """The admissible virtual spins of the tetrahedron t."""
    a, b, c, d = (col[f] for f in legs(t))
    return [k for k in range(a + b + 1) if tri(a, b, k) and tri(k, c, d)]


def side(S, A, col, amp, N, fixed=()):
    """The side of A of a move on S: the 4-simplices {S \\ a : a in A}, the inner faces (those
    containing B = S \\ A) summed, except the triangles in `fixed`, whose spins are taken from
    `col` (their weight j + 1 is kept). Inner triangle spins run over 0..N."""
    S = frozenset(S)
    B = S - frozenset(A)
    simps = [S - {a} for a in sorted(A)]
    itris = [f for f in faces(S, 3) if B <= f]
    itets = [t for t in faces(S, 4) if B <= t]
    free = [f for f in itris if f not in fixed]
    total = 0.0
    for xs in itertools.product(range(N + 1), repeat=len(free)):
        c = dict(col)
        c.update(zip(free, xs))
        ks = [virtual(c, t) for t in itets]
        if not all(ks):
            continue
        w = math.prod(c[f] + 1 for f in itris)
        for kk in itertools.product(*ks):
            c.update(zip(itets, kk))
            total += w * math.prod(amp(s, c) for s in simps)
    return total


def random_boundary(S, rng, maxj):
    """Random spins at most maxj on all triangles of S and admissible virtual spins on all its
    tetrahedra. The parities come from a random Z/2 cochain on the edges, so that every
    tetrahedron has even total spin."""
    while True:
        e = {x: rng.randint(0, 1) for x in faces(S, 2)}
        col = {}
        for f in faces(S, 3):
            par = sum(e[frozenset(p)] for p in itertools.combinations(sorted(f), 2)) % 2
            col[f] = rng.choice([x for x in range(maxj + 1) if x % 2 == par])
        ok = True
        for t in faces(S, 4):
            ks = virtual(col, t)
            if not ks:
                ok = False
                break
            col[t] = rng.choice(ks)
        if ok:
            return col


def close(x, y):
    return abs(x - y) <= TOL * max(1.0, abs(x), abs(y))


def check33(amp, rng, trials, maxj):
    """Returns (nonzero cases, mismatches) over all ten splittings of the six vertices."""
    S = frozenset(range(6))
    nonzero = bad = 0
    for sigma in itertools.combinations(range(6), 3):
        if 0 not in sigma:
            continue
        tau = tuple(sorted(S - set(sigma)))
        for _ in range(trials):
            col = random_boundary(S, rng, maxj)
            L = side(S, tau, col, amp, 3 * maxj)
            R = side(S, sigma, col, amp, 3 * maxj)
            nonzero += abs(L) > TOL or abs(R) > TOL
            bad += not close(L, R)
    return nonzero, bad


def check_gauge(nbig, rng, trials, maxj, ys):
    """2-4 (nbig = 4) and 1-5 (nbig = 5) with the inner triangles through B + {min A} fixed at
    spin y. Returns (nonzero cases, mismatches)."""
    S = frozenset(range(6))
    nonzero = bad = 0
    for A in itertools.combinations(range(6), nbig):
        B = S - set(A)
        gauge = [f for f in faces(S, 3) if B <= f and min(A) in f]
        for _ in range(trials):
            col = random_boundary(S, rng, maxj)
            small = side(S, tuple(sorted(B)), col, vertex_amp, 0)
            for y in ys:
                c = dict(col)
                c.update({f: y for f in gauge})
                big = side(S, A, c, vertex_amp, 2 * max(ys) + 2 * maxj, fixed=gauge)
                fac = (y + 1) ** (2 * len(gauge))
                nonzero += abs(big) > TOL or abs(small) > TOL
                bad += not close(big, fac * small)
    return nonzero, bad


def sphere_value(amp):
    """The state sum of the boundary of the 5-simplex, every triangle spin 0 or 1 (doubled),
    every tetrahedron summed over its admissible virtual spins."""
    S = frozenset(range(6))
    tris, tets = faces(S, 3), faces(S, 4)
    simps = faces(S, 5)
    total, configs = 0.0, 0
    for spins in itertools.product((0, 1), repeat=len(tris)):
        col = dict(zip(tris, spins))
        ks = [virtual(col, t) for t in tets]
        if not all(ks):
            continue
        configs += 1
        w = math.prod(x + 1 for x in spins)
        for kk in itertools.product(*ks):
            col.update(zip(tets, kk))
            total += w * math.prod(amp(s, col) for s in simps)
    return total, configs


def edge_value(amp):
    """The state sum of the boundary of the 5-simplex with every triangle that does not contain
    {0, 1} at spin 0, the triangles through {0, 1} at spin 0 or 1 (doubled) and every tetrahedron
    summed over its admissible virtual spins."""
    S = frozenset(range(6))
    tris, tets, simps = faces(S, 3), faces(S, 4), faces(S, 5)
    free = [f for f in tris if {0, 1} <= f]
    total = 0.0
    for spins in itertools.product((0, 1), repeat=len(free)):
        col = {f: 0 for f in tris}
        col.update(zip(free, spins))
        ks = [virtual(col, t) for t in tets]
        if not all(ks):
            continue
        w = math.prod(col[f] + 1 for f in tris)
        for kk in itertools.product(*ks):
            col.update(zip(tets, kk))
            total += w * math.prod(amp(s, col) for s in simps)
    return total


def collapsible(S, gauge):
    """Whether the vertices, the edges and the triangles `gauge` of the boundary of the simplex on
    S form a collapsible 2-complex. Removing a triangle through a free edge never destroys the
    free edge of another triangle, so greedy collapsing decides collapsibility in dimension 2:
    collapse triangles while one has a free edge, then the remaining graph must be a tree."""
    T = set(gauge)
    edges = set(faces(S, 2))
    while True:
        cnt = {}
        for t in T:
            for e in itertools.combinations(sorted(t), 2):
                cnt[frozenset(e)] = cnt.get(frozenset(e), 0) + 1
        step = next(((t, frozenset(e)) for t in sorted(T, key=sorted)
                     for e in itertools.combinations(sorted(t), 2) if cnt[frozenset(e)] == 1), None)
        if step is None:
            break
        T.discard(step[0])
        edges.discard(step[1])
    if T:
        return False
    parent = {v: v for v in S}

    def root(v):
        while parent[v] != v:
            v = parent[v]
        return v
    for e in edges:
        a, b = (root(v) for v in e)
        if a == b:
            return False
        parent[a] = b
    return len(edges) == len(S) - 1


def forces_all(S, gauge):
    """Whether spin 0 on `gauge` forces spin 0 on every triangle: a tetrahedron with three
    triangles at spin 0 has its fourth triangle at spin 0 (`weight_tet_zero` in Ooguri.lean)."""
    Z = set(gauge)
    tris = faces(S, 3)
    changed = True
    while changed:
        changed = False
        for t in faces(S, 4):
            rest = [f for f in (frozenset(c) for c in itertools.combinations(sorted(t), 3))
                    if f not in Z]
            if len(rest) == 1:
                Z.add(rest[0])
                changed = True
    return len(Z) == len(tris)


def gauge_value(amp, gauge, cut):
    """The state sum of the boundary of the 5-simplex with the triangles of `gauge` at spin 0, the
    other triangles at doubled spin <= cut and every tetrahedron summed over its admissible
    virtual spins."""
    S = frozenset(range(6))
    tris, tets, simps = faces(S, 3), faces(S, 4), faces(S, 5)
    free = [f for f in tris if f not in gauge]
    total = 0.0
    for spins in itertools.product(range(cut + 1), repeat=len(free)):
        col = {f: 0 for f in tris}
        col.update(zip(free, spins))
        ks = [virtual(col, t) for t in tets]
        if not all(ks):
            continue
        w = math.prod(col[f] + 1 for f in tris)
        for kk in itertools.product(*ks):
            col.update(zip(tets, kk))
            total += w * math.prod(amp(s, col) for s in simps)
    return total


# --- Pachner moves on the 4-sphere (the move sequence of Lightlike/FourD/Tests.lean) ---
def subfaces(K, k):
    """The k-dimensional faces of a complex given by its 4-simplices."""
    return {frozenset(c) for s in K for c in itertools.combinations(sorted(s), k + 1)}


def fvec(K):
    return tuple(len(subfaces(K, k)) for k in range(5))


def euler(K):
    return sum((-1) ** k * n for k, n in enumerate(fvec(K)))


def is_move(K, A, B):
    """The conditions of `IsMove` in Lightlike/FourD/Pachner.lean."""
    S = A | B
    return (not (A & B) and len(A) + len(B) == 6 and A and B
            and all(S - {v} in K for v in B)
            and all(any(s == S - {v} for v in B) for s in K if A <= s)
            and not any(B <= s for s in K))


def move(K, A, B):
    S = A | B
    return frozenset({s for s in K if not A <= s} | {S - {u} for u in A})


def pachner_sequence():
    """K0 -> K1 -> K2 -> K3 by a 1-5, a 2-4 and a 3-3 move; the moves with the two sides
    exchanged must undo them and the Euler characteristic must stay 2. Controls: the 1-5 move
    repeated without exchanging the sides is not a move and returns K1; the unsigned face count
    changes from 62 to 92."""
    f = frozenset
    K0 = frozenset(f(c) for c in itertools.combinations(range(6), 5))
    steps = [(f({0, 1, 2, 3, 4}), f({6})), (f({0, 1, 2, 3}), f({5, 6})), (f({0, 2, 3}), f({4, 5, 6}))]
    Ks, ok = [K0], True
    for A, B in steps:
        ok &= bool(is_move(Ks[-1], A, B))
        Ks.append(move(Ks[-1], A, B))
    for i, (A, B) in enumerate(steps):
        ok &= bool(is_move(Ks[i + 1], B, A)) and move(Ks[i + 1], B, A) == Ks[i]
    fv = [fvec(K) for K in Ks]
    eu = [euler(K) for K in Ks]
    ok &= fv == [(6, 15, 20, 15, 6), (7, 20, 30, 25, 10), (7, 21, 34, 30, 12), (7, 21, 34, 30, 12)]
    ok &= eu == [2, 2, 2, 2]
    A, B = steps[0]
    rep_move, rep = is_move(Ks[1], A, B), move(Ks[1], A, B)
    unsigned = [sum(fvec(K)) for K in Ks[:2]]
    ok &= not rep_move and rep == Ks[1] and rep != K0 and unsigned == [62, 92]
    return fv, eu, rep_move, rep == Ks[1], unsigned, ok


def main():
    rng = random.Random(2026)
    ok = True

    nz, bad = check33(vertex_amp, rng, 3, 2)
    print(f'3-3, vertexAmp:      {nz} nonzero cases, {bad} mismatches')
    ok &= bad == 0 and nz >= 20
    for name, amp in (('perturbed 15j', perturbed_amp), ('|15j|', abs_amp)):
        nz, bad = check33(amp, random.Random(2026), 3, 2)
        print(f'3-3, {name + ":":15s} {nz} nonzero cases, {bad} mismatches (control, must be > 0)')
        ok &= bad > 0

    for nbig, label in ((4, '2-4'), (5, '1-5')):
        nz, bad = check_gauge(nbig, rng, 1, 1, (0, 1, 2))
        print(f'{label}, gauge fixed:   {nz} nonzero cases, {bad} mismatches')
        ok &= bad == 0 and nz > 0

    Z, n = sphere_value(vertex_amp)
    Zabs, _ = sphere_value(abs_amp)
    print(f'boundary of the 5-simplex, spins <= 1/2: Z = {Z:.9f} over {n} spin configurations;'
          f' 7717715/243 = {7717715 / 243:.9f}; with |15j|: {Zabs:.9f}')
    ok &= n == 1024 and close(Z, 7717715 / 243) and not close(Zabs, Z)

    Ze = edge_value(vertex_amp)
    print(f'boundary of the 5-simplex, spins <= 1/2 on the triangles through {{0, 1}}: Z = {Ze:.9f}')
    ok &= close(Ze, 5)

    S = frozenset(range(6))
    agree = ncol = 0
    for sub in itertools.combinations(faces(S, 3), 10):
        c = collapsible(S, sub)
        ncol += c
        agree += c == forces_all(S, sub)
    print(f'gauge rule on the boundary of the 5-simplex: {ncol} collapsible sets of ten triangles;'
          f' collapsible == forces all triangles for {agree} of 184756')
    ok &= agree == 184756 and ncol > 0
    star = [f for f in faces(S, 3) if 5 in f]
    twist = [frozenset(t) for t in ((0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 1, 5), (0, 2, 3), (1, 2, 4),
                               (1, 3, 4), (1, 3, 5), (2, 3, 5), (3, 4, 5))]
    gauge9 = [f for f in star if f != frozenset((0, 1, 5))]
    Zs, Zt, Z9 = (gauge_value(vertex_amp, g, 1) for g in (star, twist, gauge9))
    print(f'gauge-fixed state sums, spins <= 1/2: star {Zs:.9f}, twistT {Zt:.9f}'
          f' (collapsible: {collapsible(S, star)}, {collapsible(S, twist)});'
          f' gauge9 {Z9:.9f} (collapsible: {collapsible(S, gauge9)}; control, must be 5)')
    ok &= close(Zs, 1) and close(Zt, 1) and close(Z9, 5)
    ok &= collapsible(S, star) and collapsible(S, twist) and not collapsible(S, gauge9)

    fv, eu, rep_move, rep_same, unsigned, okp = pachner_sequence()
    print(f'Pachner moves 1-5, 2-4, 3-3 on the boundary of the 5-simplex: face numbers {fv},'
          f' Euler characteristics {eu}, inverse moves undo them: {okp};'
          f' 1-5 repeated: a move {rep_move}, returns K1 {rep_same} (control);'
          f' unsigned face counts {unsigned} (control, must change)')
    ok &= okp

    print('OK' if ok else 'FAIL')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
