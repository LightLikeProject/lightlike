"""Numerical check (not a proof): a collapsible gauge set (IsGauge) on a closed 4-sphere triangulation
that does not force every triangle and gives a different finite-cutoff Ooguri state sum.

Complex: a triangulation of the 4-sphere with 24 4-simplices on 9 vertices (the boundary of the
5-simplex after random Pachner moves 1-5, 2-4, 3-3; every tetrahedron lies in exactly two simplices).
T: 25 triangles = E - V + 1 such that the vertices, edges and T collapse to a point (IsGauge).

Steps: (1) the complex is closed and T is collapsible; (2) the forcing closure of T (a tetrahedron with
three triangles in the set forces the fourth) leaves 24 of 62 triangles; (3) a second gauge set that
forces everything exists on the same complex, so its state sum is 1 (Lean: amplitudeGF_eq_one_of_forces);
(4) with doubled spins <= 2 on the triangles (spin <= 1), exactly two nonzero colourings are admissible
at every tetrahedron on the unforced triangles; each has a single virtual-spin choice per tetrahedron;
their weights (closed-form vertex of vertex_check.py) are 1 and 1.5, so the state sum of T is 3.5, not 1.
With doubled spins <= 1 the state sum of T is 1. Floating point, tolerance 1e-9.
"""
import itertools
import os
import random
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vertex_check as vc

SIMP = [(0, 1, 2, 3, 6), (0, 1, 2, 3, 7), (0, 1, 2, 4, 5), (0, 1, 2, 4, 7), (0, 1, 2, 5, 8), (0, 1, 2, 6, 8), (0, 1, 3, 4, 5), (0, 1, 3, 4, 7), (0, 1, 3, 5, 8), (0, 1, 3, 6, 8), (0, 2, 3, 4, 5), (0, 2, 3, 4, 7), (0, 2, 3, 5, 6), (0, 2, 5, 6, 8), (0, 3, 5, 6, 8), (1, 2, 3, 4, 6), (1, 2, 3, 4, 7), (1, 2, 4, 5, 8), (1, 2, 4, 6, 8), (1, 3, 4, 5, 6), (1, 3, 5, 6, 8), (1, 4, 5, 6, 8), (2, 3, 4, 5, 6), (2, 4, 5, 6, 8)]
T0 = [(0, 1, 4), (0, 1, 6), (0, 1, 7), (0, 2, 4), (0, 2, 6), (0, 3, 5), (0, 3, 7), (0, 4, 5), (0, 4, 7), (0, 5, 6), (0, 6, 8), (1, 2, 6), (1, 3, 8), (1, 4, 8), (1, 5, 6), (1, 6, 8), (2, 3, 5), (2, 3, 6), (2, 3, 7), (2, 6, 8), (3, 4, 5), (3, 5, 8), (3, 6, 8), (4, 5, 8), (4, 6, 8)]


def faces(simp, k):
    return {frozenset(c) for s in simp for c in itertools.combinations(sorted(s), k)}


def collapsible(X):
    X = set(X)
    while len(X) > 1:
        for s in sorted(X, key=lambda x: (len(x), sorted(x))):
            cof = [r for r in X if s < r]
            if len(cof) == 1 and len(cof[0]) == len(s) + 1:
                X.discard(s)
                X.discard(cof[0])
                break
        else:
            return False
    return len(X) == 1


def closure(simp, T):
    tets = faces(simp, 4)
    T = set(T)
    ch = True
    while ch:
        ch = False
        for t in tets:
            miss = [g for g in (frozenset(c) for c in itertools.combinations(sorted(t), 3))
                    if g not in T]
            if len(miss) == 1:
                T.add(miss[0])
                ch = True
    return T


def rand_gauge(simp, rng):
    """A random collapsible gauge set, built by reverse collapses (vertices, edges, triangles)."""
    V, E, Tr = faces(simp, 1), faces(simp, 2), faces(simp, 3)
    while True:
        verts = {next(iter(rng.choice(sorted(V, key=sorted))))}
        edges, T, stuck = set(), set(), False
        while len(edges) < len(E):
            opts = []
            for e in E - edges:
                a, b = tuple(e)
                if (a in verts) != (b in verts):
                    opts.append(('tree', e))
                elif a in verts and b in verts:
                    for t in Tr:
                        if e < t:
                            o = [frozenset(p) for p in itertools.combinations(sorted(t), 2)
                                 if frozenset(p) != e]
                            if all(f in edges for f in o):
                                opts.append(('tri', e, t))
            if not opts:
                stuck = True
                break
            o = rng.choice(opts)
            edges.add(o[1])
            if o[0] == 'tree':
                verts |= set(o[1])
            else:
                T.add(o[2])
        if not stuck:
            return frozenset(T)


def tri(a, b, c):
    return (a + b + c) % 2 == 0 and a <= b + c and b <= a + c and c <= a + b


def legs(t):
    w = sorted(t)
    return [frozenset(t - {w[q]}) for q in (0, 2, 1, 3)]


def main():
    simp = [tuple(s) for s in SIMP]
    V, E, Tr, Te = (faces(simp, k) for k in (1, 2, 3, 4))
    cnt = Counter(frozenset(t) for s in simp for t in itertools.combinations(sorted(s), 4))
    closed = all(v == 2 for v in cnt.values())
    T = {frozenset(t) for t in T0}
    isgauge = T <= Tr and len(T) == len(E) - len(V) + 1 and collapsible(V | E | T)
    U = sorted(Tr - closure(simp, T), key=sorted)
    print('closed', closed, '; IsGauge', isgauge, '; triangles', len(Tr), '; unforced', len(U))
    rng = random.Random(1)
    Tf = None
    for _ in range(200):
        c = rand_gauge(simp, rng)
        if closure(simp, c) >= Tr:
            Tf = c
            break
    print('forcing gauge set found on the same complex:', Tf is not None)
    tetl = [legs(t) for t in Te]
    idx = {u: i for i, u in enumerate(U)}
    results = {}
    for C in (1, 2):
        sols = []

        def val(g, asg):
            return asg.get(idx[g]) if g in idx else 0

        def en(i, asg):
            for tt in tetl:
                v = [val(g, asg) for g in tt]
                if None not in v and not any(tri(v[0], v[1], k) and tri(k, v[2], v[3])
                                             for k in range(2 * C + 1)):
                    return
            if i == len(U):
                sols.append(dict(asg))
                return
            for x in range(C + 1):
                asg[i] = x
                en(i + 1, asg)
                del asg[i]
        en(0, {})
        tot = 0.0
        for s in sols:
            col = {g: 0 for g in Tr}
            for u, i in idx.items():
                col[u] = s[i]
            w = 1.0
            for g in Tr:
                w *= col[g] + 1
            for tt in tetl:  # a single virtual-spin choice per tetrahedron, so the sum factorises
                v = [col[g] for g in tt]
                assert sum(1 for k in range(2 * C + 1)
                           if tri(v[0], v[1], k) and tri(k, v[2], v[3])) == 1
            for sm in simp:
                Jd = {frozenset((a, b)): col[frozenset(sm) - {sm[a], sm[b]}]
                      for a, b in itertools.combinations(range(5), 2)}
                ks = []
                for i in range(5):
                    wv = [x for x in range(5) if x != i]
                    sp = [Jd[frozenset((i, q))] for q in (wv[0], wv[2], wv[1], wv[3])]
                    ks.append([k for k in range(2 * C + 1)
                               if tri(sp[0], sp[1], k) and tri(k, sp[2], sp[3])])
                w *= sum(vc.amp_closed(Jd, list(K)) for K in itertools.product(*ks))
            tot += w
        results[C] = tot
        print('doubled cutoff', C, ': admissible colourings', len(sols),
              ', state sum of T =', round(tot, 9))
    ok = (closed and isgauge and Tf is not None and abs(results[1] - 1) < 1e-9
          and abs(results[2] - 3.5) < 1e-9)
    print('OK' if ok else 'FAIL')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
