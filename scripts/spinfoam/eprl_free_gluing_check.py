"""Order dependence of the EPRL (gamma = 1) state sum on the boundary of the 5-simplex: the library's gluing against the
basis-free gluing of the tetrahedra (numerical evidence, not a proof).

Doubled spins and projections throughout. Two ways of gluing the vertex amplitudes of the six 4-simplices of the boundary of the
5-simplex (`sphere6`) along the fifteen tetrahedra, for a fixed colouring of the triangles by spins:

* library gluing (`eprl_order_check.vertex`, the intrinsic vertex of `IntrinsicVertex.lean`): the vertex is the 15j symbol with
  positional labels, rewritten in the sorted basis of each tetrahedron by the transition matrices `nodeT`, which are built from
  `fourRecoupling` through the channel (0 2 | 1 3) of the legs; the sorted labels of a tetrahedron are summed in the two
  adjacent vertices.
* basis-free gluing (`free_vertex`): the node tensor of a tetrahedron is the intertwiner of its legs in the SORTED order (the
  same tensor from both adjacent 4-simplices, `vertex_check.fourj`), the five nodes of a vertex are contracted along the ten
  links with the bilinear form `eps(m, m') = (-1)^((j - m)/2) delta_{m', -m}` (first end = lower position, `vertex_check.cmat`),
  and the labels of a tetrahedron are summed. Because `sum_z iota_z (x) iota_z` is the projector onto the invariants, this does
  not depend on the choice of the intertwiner basis of a tetrahedron: only the orientation of the links can enter.

For 14 random admissible colourings (colours 0, 1 and one colour 2 on some) and 4 random relabellings of the six vertices each
it prints the ratio of the colouring's summand (face weights times the label sum) after and before the relabelling, for both
gluings, and the bone cutoffs of the fifteen edges. Run: .venv/bin/python -I scripts/spinfoam/eprl_free_gluing_check.py
(expects "OK"; the default run is a subset, 5 colourings x 2 relabellings and three edges; `--full` runs the 14 x 4 and the fifteen edges of
the note, about 30 minutes). Needs numpy.
"""
import itertools
import os
import random
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from eprl_order_check import SIMPS, TETS, TRIS, V6, vertex  # noqa: E402
from vertex_check import cmat, fourj  # noqa: E402

LET = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'


def face_weight(col):
    w = 1.0
    for f in TRIS:
        w *= col[f] + 1
    return w


def simplex_J(col, s):
    return tuple(tuple(col[tuple(v for v in s if v not in (s[p], s[q]))] if p != q else 0 for q in range(5))
                 for p in range(5))


def lib_summand(col):
    """Face weights times the sum over the sorted tetrahedron labels of the product of the six library vertices."""
    legs = {t: [col[tuple(v for v in t if v != t[k])] for k in range(4)] for t in TETS}
    inner = 0.0
    for zs in itertools.product(*[range(legs[t][0] + legs[t][1] + 1) for t in TETS]):
        zt = dict(zip(TETS, zs))
        w = 1.0
        for s in SIMPS:
            z = tuple(zt[tuple(v for v in s if v != s[a])] for a in range(5))
            w *= vertex(simplex_J(col, s), z, True)
            if w == 0.0:
                break
        inner += w
    return face_weight(col) * inner


def free_vertex(J):
    """Vertex tensor over the five sorted labels: sorted-leg intertwiners at the nodes, eps on the ten links."""
    names = {}

    def idx(n):
        if n not in names:
            names[n] = LET[len(names)]
        return names[n]
    ops, subs, out = [], [], []
    for a in range(5):
        nb = [b for b in range(5) if b != a]
        sp = [J[a][b] for b in nb]
        ops.append(np.stack([fourj(*sp, z) for z in range(sp[0] + sp[1] + 1)]))
        subs.append(idx(('z', a)) + ''.join(idx((a, b)) for b in nb))
        out.append(idx(('z', a)))
    for a in range(5):
        for b in range(a + 1, 5):
            ops.append(cmat(J[a][b]))
            subs.append(idx((a, b)) + idx((b, a)))
    return np.einsum(','.join(subs) + '->' + ''.join(out), *ops, optimize='greedy')


def free_summand(col):
    """Face weights times the label sum of the product of the six basis-free vertices."""
    names = {}

    def idx(n):
        if n not in names:
            names[n] = LET[len(names)]
        return names[n]
    ops, subs = [], []
    for s in SIMPS:
        ops.append(free_vertex(simplex_J(col, s)))
        subs.append(''.join(idx(tuple(u for u in s if u != s[a])) for a in range(5)))
    return face_weight(col) * float(np.einsum(','.join(subs) + '->', *ops, optimize='greedy'))


def admissible(col):
    return all(sum(col[tuple(v for v in t if v != t[k])] for k in range(4)) % 2 == 0 for t in TETS)


def relabel(col, sig):
    return {f: col[tuple(sorted(sig[v] for v in f))] for f in TRIS}


def bone(u, w):
    return {f: (1 if u in f and w in f else 0) for f in TRIS}


def cutoff_sum(summand, cut):
    free = [f for f in TRIS if cut[f] > 0]
    tot = 0.0
    for vals in itertools.product(*[range(cut[f] + 1) for f in free]):
        col = {f: 0 for f in TRIS}
        col.update(dict(zip(free, vals)))
        if admissible(col):
            tot += summand(col)
    return tot


def main():
    full = '--full' in sys.argv
    n_col, n_rel = (14, 4) if full else (5, 2)
    edges = list(itertools.combinations(range(6), 2)) if full else [(0, 1), (0, 2), (1, 4)]
    random.seed(5)
    rows, tries = [], 0
    while len(rows) < n_col and tries < 400:
        tries += 1
        e = {p: random.randint(0, 1) for p in itertools.combinations(V6, 2)}
        col = {f: (e[(f[0], f[1])] + e[(f[0], f[2])] + e[(f[1], f[2])]) % 2 for f in TRIS}
        if sum(col.values()) == 0:
            continue
        if random.random() < 0.3:
            col[random.choice(TRIS)] += 2
        if not admissible(col):
            continue
        s0 = lib_summand(col)
        if abs(s0) < 1e-9:
            continue
        f0 = free_summand(col)
        ratios = []
        for _ in range(n_rel):
            sig = list(V6)
            random.shuffle(sig)
            c2 = relabel(col, sig)
            ratios.append((lib_summand(c2) / s0, free_summand(c2) / f0))
        rows.append((sum(col.values()), s0, f0, ratios))
        print('sum of colours %2d  library %9.4f  free %9.4f  ratios (library, free): %s' % (
            rows[-1][0], s0, f0, ', '.join('(%.4f, %.4f)' % r for r in ratios)), flush=True)
    dev_free = max(abs(r[1] - 1.0) for row in rows for r in row[3])
    dev_lib = max(abs(abs(r[0]) - 1.0) for row in rows for r in row[3])
    print('max |free ratio - 1| = %.2e; max ||library ratio| - 1| = %.4f' % (dev_free, dev_lib))
    amps = {}
    for u, w in edges:
        amps[(u, w)] = (cutoff_sum(free_summand, bone(u, w)), cutoff_sum(lib_summand, bone(u, w)))
        print('bone cutoff of edge %s: free %.4f, library %.4f' % ((u, w), *amps[(u, w)]), flush=True)
    ok = dev_free < 1e-6 and dev_lib > 0.1 and all(abs(v[0] - 5.0) < 1e-6 for v in amps.values())
    print('OK' if ok else 'FAILED')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
