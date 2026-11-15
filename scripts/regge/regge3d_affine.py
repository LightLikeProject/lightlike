"""Numerical check (not proof): the algebraic core of the 3D convergence for a general chart.

In a chart the metric at a vertex is not the identity, so the Kuhn tetrahedra seen in an orthonormal
frame are the images A.T of the orthoscheme tetrahedra by a linear map A (with A^T A = g(m)).
Claim: sum over the 7 edge classes of |A e| d(deficit)/d(eps), with squared lengths perturbed by
-(eps/3) Rm(y,z,y,z) in the orthonormal frame, equals (R/2) |det A| for every invertible A.
Controls: the weights |A e|^2 and 1 break it.
"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # siblings, also under python -I
import itertools
import numpy as np
import regge3d_core as C
from regge3d_convergence import dihedral


def deficit_A(edge, A, Rm, eps):
    mid = np.array(edge) / 2
    ang = 0.0
    for vs in C.star(edge):
        pos = [A @ (np.array(v) - mid) for v in vs]
        L2 = {}
        for i, j in itertools.combinations(range(4), 2):
            L2[(i, j)] = np.sum((pos[i] - pos[j]) ** 2) - eps / 3 * C.Q(Rm, pos[i], pos[j])
        ia, ib = vs.index((0, 0, 0)), vs.index(tuple(edge))
        o = [k for k in range(4) if k not in (ia, ib)]
        ang += dihedral(L2, ia, ib, o[0], o[1])
    return 2 * np.pi - ang


def coefficient(A, ric, w):
    Rm = C.riem_from_ric(ric)
    h = 1e-5
    tot = 0.0
    for e in C.edges:
        d = (deficit_A(e, A, Rm, h) - deficit_A(e, A, Rm, -h)) / (2 * h)
        tot += w(np.linalg.norm(A @ np.array(e))) * d
    return tot


if __name__ == '__main__':
    rng = np.random.default_rng(3)
    for _ in range(3):
        A = np.eye(3) + 0.3 * rng.normal(size=(3, 3))
        M = rng.normal(size=(3, 3)); ric = M + M.T
        t = np.trace(ric) / 2 * abs(np.linalg.det(A))
        tgt = t; v = coefficient(A, ric, lambda l: l)
        c2 = coefficient(A, ric, lambda l: l * l); c1 = coefficient(A, ric, lambda l: 1.0)
        print('(R/2)|det A| =', tgt, '| sum |Ae| d =', v, '| control |Ae|^2:', c2, '| control 1:', c1)
        assert abs(v - tgt) < 1e-6 * (1 + abs(tgt)), 'FAILED: |Ae| weights do not give (R/2)|det A|'
        assert abs(c2 - tgt) > 1e-3 and abs(c1 - tgt) > 1e-3, 'FAILED: a wrong weight is not rejected'
    print('PASS affine core identity and wrong-weight controls')
