"""Numerical check (not a proof): does the gauge-fixed Ponzano-Regge amplitude depend on the
maximal tree? Same weights as Lightlike/PonzanoRegge: edge (2j+1)(-1)^{2j}, triangle
(-1)^{ja+jb+jc}, tetrahedron {6j}; spin 0 on the tree edges, spin <= cut on every other edge
(uniform cutoff, in doubled units).

1. S^3 after a 1-4 move (boundary of the 4-simplex with one tetrahedron subdivided, 6 vertices):
   the amplitude for EVERY spanning tree of the 1-skeleton, and whether all trees are connected
   by triangle exchanges (the exchanges of Lightlike.PR.amplitudeGF_exchange).
2. A solid torus (a ring of three triangulated prisms, 9 vertices), which has a non-contractible
   loop: the trees connected to a tree T1 by triangle exchanges (they must all agree, by the Lean
   theorem), and 40 random spanning trees, split into those connected to T1 and those not.

Values are computed in exact arithmetic (SymPy) and compared after evaluation to 40 digits.
"""
import functools, itertools, random
from sympy import S, N
from sympy.physics.wigner import wigner_6j


def adm2(a, b, c):  # doubled spins
    return (a + b + c) % 2 == 0 and abs(a - b) <= c <= a + b


@functools.lru_cache(maxsize=None)
def six_j2(a, b, c, d, e, f):  # doubled spins; {a b c; d e f}
    if not (adm2(a, b, c) and adm2(a, e, f) and adm2(d, b, f) and adm2(d, e, c)):
        return S(0)
    return wigner_6j(*(S(x) / 2 for x in (a, b, c, d, e, f)))


def edges_of(tets):
    return sorted({frozenset(p) for t in tets for p in itertools.combinations(t, 2)}, key=sorted)


def tris_of(tets):
    return sorted({frozenset(p) for t in tets for p in itertools.combinations(t, 3)}, key=sorted)


def weight(tets, tris, edges, col):
    w = S(1)
    for e in edges:
        w *= (col[e] + 1) * (-1) ** col[e]
    for f in tris:
        w *= (-1) ** (sum(col[frozenset(p)] for p in itertools.combinations(f, 2)) // 2)
    for t in tets:
        p, q, r, s = t
        e = lambda u, v: col[frozenset((u, v))]
        w *= six_j2(e(p, q), e(q, r), e(r, p), e(r, s), e(p, s), e(q, s))
        if w == 0:
            return S(0)
    return w


def amplitude_gf(tets, tree, cut):
    """Sum of the weight over colourings: 0 on tree edges, 0..cut on the others, with pruning on
    triangles whose three spins are already fixed."""
    edges, tris = edges_of(tets), tris_of(tets)
    free = [e for e in edges if e not in tree]
    col = {e: 0 for e in tree}
    tri_edges = [[frozenset(p) for p in itertools.combinations(f, 2)] for f in tris]
    total = [S(0)]

    def ok():
        for es in tri_edges:
            if all(x in col for x in es) and not adm2(*(col[x] for x in es)):
                return False
        return True

    def rec(i):
        if i == len(free):
            total[0] += weight(tets, tris, edges, col)
            return
        for x in range(cut + 1):
            col[free[i]] = x
            if ok():
                rec(i + 1)
            del col[free[i]]

    rec(0)
    return total[0]


def spanning_trees(verts, edges):
    n = len(verts)
    for T in itertools.combinations(edges, n - 1):
        parent = {v: v for v in verts}

        def find(v):
            while parent[v] != v:
                v = parent[v]
            return v
        good = True
        for e in T:
            a, b = sorted(e)
            ra, rb = find(a), find(b)
            if ra == rb:
                good = False
                break
            parent[ra] = rb
        if good:
            yield frozenset(T)


def exchanges(T, tris):
    """Trees reachable from T by one triangle exchange (uv, vw in T, uw not: swap uv for uw)."""
    out = set()
    for f in tris:
        for u, v, w in itertools.permutations(f):
            e, g, h = frozenset((u, v)), frozenset((v, w)), frozenset((u, w))
            if e in T and g in T and h not in T:
                out.add((T - {e}) | {h})
    return out


def main():
    # 1. S^3: boundary of the 4-simplex 01234, then a 1-4 move on 0123 with new vertex 5.
    tets = [t for t in itertools.combinations(range(5), 4) if t != (0, 1, 2, 3)]
    tets += [(0, 1, 2, 5), (0, 1, 3, 5), (0, 2, 3, 5), (1, 2, 3, 5)]
    edges, tris = edges_of(tets), tris_of(tets)
    trees = list(spanning_trees(range(6), edges))
    for cut in (1, 2):
        vals = {T: N(amplitude_gf(tets, T, cut), 40) for T in trees}
        distinct = sorted({round(float(v), 25) for v in vals.values()})
        print(f"S^3 (6 vertices), cut {cut}: {len(trees)} trees, distinct amplitudes: {distinct}")
    # connectivity of the trees under triangle exchanges
    seen, todo = {trees[0]}, [trees[0]]
    while todo:
        for T2 in exchanges(todo.pop(), tris):
            if T2 not in seen:
                seen.add(T2)
                todo.append(T2)
    print(f"  trees connected to the first by triangle exchanges: {len(seen)} of {len(trees)}")

    # 2. Solid torus: ring of three prisms over the triangles (a_i, b_i, c_i), i = 0, 1, 2.
    a, b, c = (lambda i: 3 * (i % 3)), (lambda i: 3 * (i % 3) + 1), (lambda i: 3 * (i % 3) + 2)
    tets = []
    for i in range(3):
        j = i + 1
        tets += [(a(i), b(i), c(i), a(j)), (b(i), c(i), a(j), b(j)), (c(i), a(j), b(j), c(j))]
    edges, tris = edges_of(tets), tris_of(tets)
    E = lambda u, v: frozenset((u, v))
    T1 = frozenset([E(a(i), b(i)) for i in range(3)] + [E(b(i), c(i)) for i in range(3)]
                   + [E(a(0), a(1)), E(a(1), a(2))])
    T3 = next(iter(exchanges(T1, tris)))           # one triangle exchange away from T1
    assert all(e in edges for T in (T1, T3) for e in T)
    print(f"solid torus: {len(edges)} edges, {len(tris)} triangles, {len(tets)} tetrahedra")
    # all trees connected to T1 by triangle exchanges
    comp, todo = {T1}, [T1]
    while todo:
        for Tn in exchanges(todo.pop(), tris):
            if Tn not in comp:
                comp.add(Tn)
                todo.append(Tn)
    print(f"  trees connected to T1 by triangle exchanges: {len(comp)}")
    # random spanning trees (Kruskal with random edge order), split by component
    rng = random.Random(1)
    sample = []
    while len(sample) < 40:
        order = edges[:]
        rng.shuffle(order)
        parent = {v: v for v in range(9)}

        def find(v):
            while parent[v] != v:
                v = parent[v]
            return v
        T = []
        for e in order:
            x, y = sorted(e)
            if find(x) != find(y):
                parent[find(x)] = find(y)
                T.append(e)
        sample.append(frozenset(T))
    for cut in (1, 2):
        inside, outside = set(), set()
        for T in [T1, T3] + sample:
            v = round(float(N(amplitude_gf(tets, T, cut), 40)), 20)
            (inside if T in comp else outside).add(v)
        n_out = sum(T not in comp for T in sample)
        print(f"  cut {cut}: amplitudes of trees connected to T1: {sorted(inside)}; "
              f"of {n_out} sampled trees not connected: {sorted(outside)}")


if __name__ == "__main__":
    main()
