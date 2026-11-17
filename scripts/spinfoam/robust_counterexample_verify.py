"""Independent verification of the counterexample to "robust sets stay robust under the 3-3 move".

Self-contained: it does not import `forcechain.py` or `robust_check.py`. The data is the pinned
counterexample of `robust_check.py` (a 4-sphere K with 20 simplices on 8 vertices, a set T of 23
triangles, the 3-3 move sigma = {3, 6, 7} -> tau = {0, 2, 4}). The checks use certificates, each
verified by a short routine that can be read and checked by hand:

1. K is a closed 4-manifold triangulation (every tetrahedron lies in exactly two simplices), and the
   move is a 3-3 move: the three simplices containing sigma are the simplices of the union minus a
   vertex of tau, and the new simplices are the union minus a vertex of sigma.
2. T is robust for K: for every tetrahedron t of K, a *list of forcing steps* (tetrahedron, triangle)
   without t is produced by a worklist search and then checked step by step: the tetrahedron is not t,
   it contains the triangle, and the other three triangles of the tetrahedron are in T or were forced
   before; at the end every triangle of K is reached.
3. T is not robust for K' (the complex after the move): for the tetrahedron t' = {0, 2, 3, 6} a set X of
   triangles is listed that is nonempty, disjoint from T and *blocking* for the tetrahedra of K' other
   than t' (no tetrahedron has exactly one of its triangles in X). Such a set cannot be reached by
   forcing: the triangles outside X contain T and are closed under the rule, so forcing from T never
   enters X.
The same is done for a 2-4 move (below): a 4-sphere with 30 simplices on 10 vertices, a set T of 34
triangles robust for K, the move that removes the tetrahedron {0,5,7,8} (shared by the simplices with
apexes 1 and 9) and adds the edge {1,9}, with the triangle {1,7,9} added to T; T plus that triangle is not
robust for K' (removing {0,5,8,9} stops the forcing).
Exit code 0 when all checks hold.
"""
import itertools
import sys

K = [[0, 1, 2, 3, 5], [0, 1, 2, 3, 6], [0, 1, 2, 5, 7], [0, 1, 2, 6, 7], [0, 1, 3, 4, 5], [0, 1, 3, 4, 6],
     [0, 1, 4, 5, 6], [0, 1, 5, 6, 7], [0, 2, 3, 5, 7], [0, 2, 3, 6, 7], [0, 3, 4, 5, 7], [0, 3, 4, 6, 7],
     [0, 4, 5, 6, 7], [1, 2, 3, 4, 5], [1, 2, 3, 4, 6], [1, 2, 4, 5, 6], [1, 2, 5, 6, 7], [2, 3, 4, 5, 7],
     [2, 3, 4, 6, 7], [2, 4, 5, 6, 7]]
T = [[0, 1, 3], [0, 1, 4], [0, 1, 7], [0, 2, 5], [0, 2, 6], [0, 3, 4], [0, 3, 5], [0, 3, 7], [0, 4, 5],
     [0, 4, 6], [0, 5, 6], [0, 6, 7], [1, 2, 4], [1, 2, 7], [1, 3, 5], [1, 3, 6], [1, 4, 5], [1, 6, 7],
     [2, 3, 6], [2, 3, 7], [2, 4, 7], [3, 4, 6], [5, 6, 7]]
SIGMA, TAU = (3, 6, 7), (0, 2, 4)
T_REMOVED = (0, 2, 3, 6)


def faces(simplices, k):
    out = set()
    for s in simplices:
        out.update(itertools.combinations(sorted(s), k))
    return out


def tri_of(tet):
    return [tuple(c) for c in itertools.combinations(tet, 3)]


def worklist_derivation(tets, tris, T):
    """A list of steps (tet, triangle) forcing every triangle from T, or None."""
    known = set(T)
    steps = []
    progress = True
    while progress:
        progress = False
        for t in tets:
            missing = [f for f in tri_of(t) if f not in known]
            if len(missing) == 1:
                steps.append((t, missing[0]))
                known.add(missing[0])
                progress = True
    return steps if tris <= known else None


def check_derivation(steps, tets_allowed, tris, T):
    known = set(T)
    for t, f in steps:
        assert t in tets_allowed and f in tri_of(t)
        assert all(g in known for g in tri_of(t) if g != f), "a step uses a triangle not yet known"
        known.add(f)
    return tris <= known


def main():
    Ks = [tuple(s) for s in K]
    Ts = {tuple(t) for t in T}
    tets = faces(Ks, 4)
    tris = faces(Ks, 3)
    # 1. closed manifold and the move
    count = {}
    for s in Ks:
        for t in itertools.combinations(s, 4):
            count[t] = count.get(t, 0) + 1
    assert set(count.values()) == {2}, "K is not closed"
    union = tuple(sorted(set(SIGMA) | set(TAU)))
    around = [s for s in Ks if set(SIGMA) <= set(s)]
    assert sorted(around) == sorted(tuple(sorted(set(union) - {b})) for b in TAU)
    assert not any(set(TAU) <= set(s) for s in Ks)
    assert SIGMA not in Ts
    K2 = [s for s in Ks if s not in around] + [tuple(sorted(set(union) - {a})) for a in SIGMA]
    count2 = {}
    for s in K2:
        for t in itertools.combinations(s, 4):
            count2[t] = count2.get(t, 0) + 1
    assert set(count2.values()) == {2}, "K' is not closed"
    tets2 = faces(K2, 4)
    tris2 = faces(K2, 3)
    # 2. T is robust for K
    n_steps = 0
    for t in sorted(tets):
        allowed = tets - {t}
        steps = worklist_derivation(sorted(allowed), tris, Ts)
        assert steps is not None, f"forcing fails without {t}"
        assert check_derivation(steps, allowed, tris, Ts)
        n_steps += len(steps)
    print("K: 20 simplices,", len(tets), "tetrahedra,", len(tris), "triangles; T has", len(Ts),
          "triangles; every one of the", len(tets), "removals of a tetrahedron still forces",
          "(", n_steps, "checked steps )")
    # 3. T is not robust for K': a blocking set avoiding T when t' is removed
    allowed2 = tets2 - {T_REMOVED}
    known = set(Ts)  # forcing closure from T under the allowed tetrahedra, to build X as the complement
    changed = True
    while changed:
        changed = False
        for t in allowed2:
            miss = [f for f in tri_of(t) if f not in known]
            if len(miss) == 1:
                known.add(miss[0])
                changed = True
    X = sorted(tris2 - known)
    assert X, "forcing succeeds without t'"
    Xs = set(X)
    assert not (Xs & Ts)
    for t in allowed2:
        assert sum(1 for f in tri_of(t) if f in Xs) != 1, f"X is not blocking at {t}"
    print("K': removing", T_REMOVED, "the forcing from T stops; the blocking set X of", len(X),
          "triangles is disjoint from T and has 0 or at least 2 triangles in every other tetrahedron:")
    print("  X =", X)
    print("OK")
    return 0


K24 = [[0, 1, 2, 3, 4], [0, 1, 2, 3, 6], [0, 1, 2, 4, 5], [0, 1, 2, 5, 6], [0, 1, 3, 4, 5], [0, 1, 3, 5, 8], [0, 1, 3, 6, 7], [0, 1, 3, 7, 8], [0, 1, 5, 6, 7], [0, 1, 5, 7, 8], [0, 2, 3, 4, 6], [0, 2, 4, 5, 6], [0, 3, 4, 5, 6], [0, 3, 5, 6, 9], [0, 3, 5, 8, 9], [0, 3, 6, 7, 9], [0, 3, 7, 8, 10], [0, 3, 7, 9, 10], [0, 3, 8, 9, 10], [0, 5, 6, 7, 9], [0, 5, 7, 8, 9], [0, 7, 8, 9, 10], [1, 2, 3, 4, 5], [1, 2, 3, 5, 6], [1, 3, 5, 6, 7], [1, 3, 5, 7, 8], [2, 3, 4, 5, 6], [3, 5, 6, 7, 9], [3, 5, 7, 8, 9], [3, 7, 8, 9, 10]]
T24 = [[0, 1, 2], [0, 1, 5], [0, 1, 8], [0, 2, 6], [0, 3, 4], [0, 3, 7], [0, 3, 10], [0, 4, 5], [0, 5, 7], [0, 5, 8], [0, 6, 9], [0, 8, 9], [1, 2, 3], [1, 2, 5], [1, 2, 6], [1, 3, 6], [1, 4, 5], [1, 6, 7], [2, 3, 4], [2, 4, 6], [2, 5, 6], [3, 4, 6], [3, 5, 6], [3, 6, 7], [3, 6, 9], [3, 7, 9], [3, 7, 10], [3, 8, 9], [3, 8, 10], [5, 7, 8], [5, 8, 9], [6, 7, 9], [7, 8, 9], [7, 9, 10]]
TET24, P24, Q24, A24 = (0, 5, 7, 8), 1, 9, 7
T_REMOVED24 = (0, 5, 8, 9)


def main24():
    Ks = [tuple(s) for s in K24]
    Ts = {tuple(t) for t in T24}
    tets, tris = faces(Ks, 4), faces(Ks, 3)

    def closed(simplices):
        count = {}
        for s in simplices:
            for t in itertools.combinations(s, 4):
                count[t] = count.get(t, 0) + 1
        return set(count.values()) == {2}

    assert closed(Ks), "K is not closed"
    around = [s for s in Ks if set(TET24) <= set(s)]
    assert sorted(around) == sorted(tuple(sorted(set(TET24) | {v})) for v in (P24, Q24)), "not a 2-4 move"
    assert (min(P24, Q24), max(P24, Q24)) not in faces(Ks, 2), "the edge {p, q} is already in K"
    K2 = [s for s in Ks if s not in around] + [tuple(sorted({P24, Q24} | (set(TET24) - {x}))) for x in TET24]
    assert closed(K2), "K' is not closed"
    tets2, tris2 = faces(K2, 4), faces(K2, 3)
    n_steps = 0
    for t in sorted(tets):
        allowed = tets - {t}
        steps = worklist_derivation(sorted(allowed), tris, Ts)
        assert steps is not None, f"forcing fails without {t}"
        assert check_derivation(steps, allowed, tris, Ts)
        n_steps += len(steps)
    print("2-4: K has", len(Ks), "simplices,", len(tets), "tetrahedra,", len(tris), "triangles; T has", len(Ts),
          "triangles; every one of the", len(tets), "removals still forces (", n_steps, "checked steps )")
    T2 = Ts | {tuple(sorted((P24, Q24, A24)))}
    allowed2 = tets2 - {T_REMOVED24}
    known = set(T2)
    changed = True
    while changed:
        changed = False
        for t in allowed2:
            miss = [f for f in tri_of(t) if f not in known]
            if len(miss) == 1:
                known.add(miss[0])
                changed = True
    X = sorted(tris2 - known)
    assert X, "forcing succeeds without t'"
    Xs = set(X)
    assert not (Xs & T2)
    for t in allowed2:
        assert sum(1 for f in tri_of(t) if f in Xs) != 1, f"X is not blocking at {t}"
    print("2-4: K' has", len(tets2), "tetrahedra; removing", T_REMOVED24, "the forcing from T plus {p, q, a} stops;",
          "blocking set X of", len(X), "triangles, disjoint from T plus {p, q, a}:")
    print("  X =", X)
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main() or main24())
