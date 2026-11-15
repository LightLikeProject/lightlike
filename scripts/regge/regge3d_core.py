"""Numerical check (not proof) of the algebraic core of the 3D convergence.

In normal coordinates at the midpoint of an edge, d^2(y, z) = |y-z|^2 - (1/3) K(y,z) |y^z|^2 + O(5).
For the Kuhn triangulation, perturb the squared edge lengths of the tetrahedra around each of the
7 edge types by -(eps/3) Rm(y,z,y,z) and differentiate the deficit at eps = 0. Claim: the sum over
the 7 edge types of |e| * d(deficit)/d(eps) equals R/2 for every algebraic curvature tensor of
dimension 3 (determined by the Ricci tensor). Control: weighting by |e|^2 or 1 breaks it.
"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # siblings, also under python -I
import itertools
import numpy as np
from regge3d_convergence import dihedral

def riem_from_ric(ric):
    R = np.trace(ric)
    g = np.eye(3)
    Rm = np.zeros((3, 3, 3, 3))
    for a, b, c, d in itertools.product(range(3), repeat=4):
        Rm[a, b, c, d] = (g[a, c] * ric[b, d] - g[a, d] * ric[b, c] - g[b, c] * ric[a, d]
                          + g[b, d] * ric[a, c] - R / 2 * (g[a, c] * g[b, d] - g[a, d] * g[b, c]))
    return Rm

def Q(Rm, y, z):
    return np.einsum('abcd,a,b,c,d->', Rm, y, z, y, z)  # = K(y,z) |y^z|^2

def star(edge):
    """Tetrahedra of the Kuhn triangulation of Z^3 containing the edge (0, edge)."""
    p, q = tuple(0 for _ in range(3)), tuple(edge)
    res = set()
    for c in itertools.product(range(-1, 2), repeat=3):
        for perm in itertools.permutations(range(3)):
            v = [np.array(c)]
            for k in perm:
                w = v[-1].copy(); w[k] += 1; v.append(w)
            vs = [tuple(int(t) for t in x) for x in v]
            if p in vs and q in vs:
                res.add(tuple(vs))
    return list(res)

def deficit(edge, Rm, eps):
    mid = np.array(edge) / 2
    ang = 0.0
    for vs in star(edge):
        pos = [np.array(v) - mid for v in vs]
        L2 = {}
        for i, j in itertools.combinations(range(4), 2):
            L2[(i, j)] = np.sum((pos[i] - pos[j]) ** 2) - eps / 3 * Q(Rm, pos[i], pos[j])
        ia, ib = vs.index((0, 0, 0)), vs.index(tuple(edge))
        o = [k for k in range(4) if k not in (ia, ib)]
        ang += dihedral(L2, ia, ib, o[0], o[1])
    return 2 * np.pi - ang

edges = [e for e in itertools.product((0, 1), repeat=3) if any(e)]

def coefficient(ric, w):
    Rm = riem_from_ric(ric)
    h = 1e-5
    tot = 0.0
    for e in edges:
        d = (deficit(e, Rm, h) - deficit(e, Rm, -h)) / (2 * h)
        tot += w(np.linalg.norm(e)) * d
    return tot

if __name__ == '__main__':
    rng = np.random.default_rng(1)
    for _ in range(3):
        A = rng.normal(size=(3, 3)); ric = A + A.T
        R = np.trace(ric)
        v = coefficient(ric, lambda l: l)
        c2 = coefficient(ric, lambda l: l * l); c1 = coefficient(ric, lambda l: 1.0)
        print('R/2 =', R / 2, '| sum |e| d =', v, '| control sum |e|^2 d =', c2, '| control sum d =', c1)
        assert abs(v - R / 2) < 1e-6 * (1 + abs(R)), 'FAILED: |e| weights do not give R/2'
        assert abs(c2 - R / 2) > 1e-3 and abs(c1 - R / 2) > 1e-3, 'FAILED: a wrong weight is not rejected'
    print('PASS core identity and wrong-weight controls')
