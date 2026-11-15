"""Numerical evidence (not proof): weighted Regge edge deficits in 3D converge to curvature.

Kuhn triangulation (6 tetrahedra per cube) of the grid of mesh s, edge lengths = geodesic
distances of the product metric H^2 x R: g = dx^2 + e^{2x} dy^2 + dz^2 (scalar curvature -2).
Compares  sum_e f(mid_e) * l_e * delta_e   with   (1/2) * int f R dV  (dV = e^x dx dy dz)
and, as a wrong-weight control, with the sum without the factor l_e (which scales like s^{-1}).
"""
import itertools
import sys
import numpy as np

def dist(p, q):
    """Geodesic distance in H^2 x R (upper half plane u = e^{-x})."""
    u1, u2 = np.exp(-p[0]), np.exp(-q[0])
    ch = 1 + ((u1 - u2) ** 2 + (p[1] - q[1]) ** 2) / (2 * u1 * u2)
    return np.sqrt(np.arccosh(ch) ** 2 + (p[2] - q[2]) ** 2)

def dihedral(L2, a, b, c, d):
    """Dihedral angle at edge ab of tetrahedron abcd from the squared lengths L2[(i,j)]."""
    def l2(i, j):
        return L2[(min(i, j), max(i, j))]
    # embed: a at 0, b on x-axis, c in the xy-plane, d in space
    ab = np.sqrt(l2(a, b))
    B = np.array([ab, 0, 0])
    cx = (l2(a, c) - l2(b, c) + l2(a, b)) / (2 * ab)
    C = np.array([cx, np.sqrt(max(l2(a, c) - cx ** 2, 0)), 0])
    dx_ = (l2(a, d) - l2(b, d) + l2(a, b)) / (2 * ab)
    dy_ = (l2(a, d) - l2(c, d) + l2(a, c) - 2 * dx_ * cx) / (2 * C[1]) if False else \
        (l2(a, d) - l2(c, d) + l2(a, c) - 2 * dx_ * C[0]) / (2 * C[1])
    D = np.array([dx_, dy_, np.sqrt(max(l2(a, d) - dx_ ** 2 - dy_ ** 2, 0))])
    # normals to the faces abc and abd, projected orthogonal to ab
    e = B / np.linalg.norm(B)
    vc = C - (C @ e) * e
    vd = D - (D @ e) * e
    return np.arccos(vc @ vd / np.linalg.norm(vc) / np.linalg.norm(vd))

def run(s, centre, rad):
    nmax = int(np.ceil(rad / s)) + 2
    base = np.round(np.array(centre) / s).astype(int)
    pts = {}
    def P(v):
        return (v[0] * s, v[1] * s, v[2] * s)
    edges = {}
    for c in itertools.product(range(-nmax, nmax), repeat=3):
        c = tuple(int(base[i] + c[i]) for i in range(3))
        for perm in itertools.permutations(range(3)):
            v = [np.array(c)]
            for k in perm:
                w = v[-1].copy(); w[k] += 1; v.append(w)
            vs = [tuple(int(t) for t in x) for x in v]
            for i, j in itertools.combinations(range(4), 2):
                key = tuple(sorted((vs[i], vs[j])))
                edges.setdefault(key, []).append(vs)
    total, total_wrong = 0.0, 0.0
    for (p, q), tets in edges.items():
        mid = [(p[i] + q[i]) * s / 2 for i in range(3)]
        r2 = sum((mid[i] - centre[i]) ** 2 for i in range(3))
        if r2 >= rad * rad * 0.9:
            continue
        f = np.exp(-1 / (1 - r2 / (rad * rad))) if r2 < rad * rad else 0.0
        if f == 0.0:
            continue
        # the edge must be interior: its link is a full cycle (all tets present)
        ang = 0.0
        for vs in tets:
            L2 = {(i, j): dist(P(vs[i]), P(vs[j])) ** 2 for i, j in itertools.combinations(range(4), 2)}
            ia, ib = vs.index(p), vs.index(q)
            others = [k for k in range(4) if k not in (ia, ib)]
            ang += dihedral(L2, ia, ib, others[0], others[1])
        l = dist(P(p), P(q))
        total += f * l * (2 * np.pi - ang)
        total_wrong += f * (2 * np.pi - ang)
    return total, total_wrong

def target(centre, rad, m=160):
    xs = np.linspace(-rad, rad, m)
    h = xs[1] - xs[0]
    X, Y, Z = np.meshgrid(xs + centre[0], xs + centre[1], xs + centre[2], indexing='ij')
    r2 = (X - centre[0]) ** 2 + (Y - centre[1]) ** 2 + (Z - centre[2]) ** 2
    f = np.where(r2 < rad ** 2, np.exp(-1 / np.maximum(1 - r2 / rad ** 2, 1e-12)), 0.0)
    return 0.5 * (-2.0) * np.sum(f * np.exp(X)) * h ** 3

if __name__ == '__main__':
    centre, rad = (0.2, 0.0, 0.0), 0.5
    tgt = target(centre, rad)
    print('target 1/2 int f R dV =', tgt)
    for s in [0.1, 0.05, 0.025]:
        t, w = run(s, centre, rad)
        print(f's={s}: sum l*delta = {t:.6f} (ratio {t / tgt:.4f}); wrong weight (no l) = {w:.4f}')
