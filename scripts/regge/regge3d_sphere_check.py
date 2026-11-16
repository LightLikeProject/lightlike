"""Numerical check (not proof): the Regge action of the Kuhn grid of mesh 1/N for the round 3-sphere.

The metric is g = 4/(1+|x|^2)^2 delta (the unit S^3 in stereographic coordinates), with scalar curvature R = 6
and sqrt(det g) = 8/(1+|x|^2)^3. Its geodesic distance is explicit: for the chord c with
c^2 = 4|x-y|^2 / ((1+|x|^2)(1+|y|^2)), d(x, y) = 2 arcsin(c/2). For each N the script computes, for the
seven edge classes and all hinges with lower corner z/N in [0,1)^3, the hinge length l and the deficit angle
delta = 2 pi - (sum of the dihedral angles of the tetrahedra around the hinge), with the dihedral angles
computed from the true geodesic squared lengths of the six edges (the formula of
Lightlike/Regge/Conv3/DihedralDeriv.lean: cos = Nn / sqrt(Pp1 Pp2)). The Regge action S_N = sum l delta
is compared with the limit L = integral over [0,1]^3 of (R/2) sqrt(det g) = integral of 24/(1+|x|^2)^3
(Lightlike.Regge.Conv3.regge3d_tendsto). Checks: S_N approaches L (the error halves each time N doubles,
the Richardson extrapolation 2 S_32 - S_16 is within 0.2% of L), and the wrong sign (-L) and the wrong factor (2 L) are far away.
The rate is an observation; the theorem proves convergence only.
Observation on the origin of the 1/N (MEASURED, N = 4, 8, 16, 32): let R_N be the Riemann sum
sum_k sum_z eps^3 d_k(eps (z + w_k/2)) of the limit class densities d_k (computed as l delta / eps^3 at
eps = 0.01, 0.005, Richardson-extrapolated) at the same hinge midpoints. Then N (R_N - L) = 6.55, 6.31, 6.19, 6.13
while S_N - R_N = -0.0682, -0.00666, -0.00059, -0.00003: the geometric error is far smaller than the
quadrature error, so the 1/N is the midpoint-of-edge sampling of the Riemann sum, not a first-order term
of the hinge expansion.
Usage: python3 scripts/regge/regge3d_sphere_check.py     (a few seconds)
"""
import itertools
import sys
import numpy as np

kv = np.array([(0, 0, 0), (1, 0, 0), (1, 1, 0), (1, 1, 1)], dtype=float)
perms = [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
hP = [0, 0, 0, 1, 1, 2]; hQ = [1, 2, 3, 2, 3, 3]; hR = [2, 1, 1, 0, 0, 0]; hS = [3, 3, 2, 3, 2, 1]
dirs = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1), (1, 1, 1)]


def kpos(s, h, a):
    kp = kv[a][list(perms[s])]
    return kp - (kv[hP[h]][list(perms[s])] + kv[hQ[h]][list(perms[s])]) / 2


def members(w):
    out = []
    for s in range(6):
        for h in range(6):
            if all(kv[hQ[h]][perms[s][i]] - kv[hP[h]][perms[s][i]] == w[i] for i in range(3)):
                out.append((s, h))
    return out


def dist(x, y):
    """Geodesic distance on the unit S^3 in stereographic coordinates (arrays of shape (..., 3))."""
    c2 = 4 * np.sum((x - y) ** 2, axis=-1) / ((1 + np.sum(x ** 2, axis=-1)) * (1 + np.sum(y ** 2, axis=-1)))
    return 2 * np.arcsin(np.sqrt(c2) / 2)


def dihedral(a, b, c, d, e, f):
    nn = (b + d - f) / 2 - (b + a - c) * (d + a - e) / (4 * a)
    p1 = b - (b + a - c) ** 2 / (4 * a)
    p2 = d - (d + a - e) ** 2 / (4 * a)
    return np.arccos(nn / np.sqrt(p1 * p2))


def regge_action(N):
    eps = 1.0 / N
    z = np.array(list(itertools.product(range(N), repeat=3)), dtype=float)
    total = 0.0
    for w in dirs:
        w = np.array(w, dtype=float)
        v = eps * (z + w / 2)
        ell = dist(v - eps * w / 2, v + eps * w / 2)
        angles = np.zeros(len(z))
        for (s, h) in members(w):
            P = [v + eps * kpos(s, h, a) for a in range(4)]
            L = [dist(P[i], P[j]) ** 2 for (i, j) in
                 [(hP[h], hQ[h]), (hP[h], hR[h]), (hQ[h], hR[h]), (hP[h], hS[h]), (hQ[h], hS[h]), (hR[h], hS[h])]]
            angles += dihedral(*L)
        total += float(np.sum(ell * (2 * np.pi - angles)))
    return total


def limit(n=48):
    x, wts = np.polynomial.legendre.leggauss(n)
    x = (x + 1) / 2; wts = wts / 2
    X, Y, Zc = np.meshgrid(x, x, x, indexing='ij')
    W = wts[:, None, None] * wts[None, :, None] * wts[None, None, :]
    return float(np.sum(W * 24.0 / (1 + X ** 2 + Y ** 2 + Zc ** 2) ** 3))


if __name__ == '__main__':
    L = limit()
    print('limit  integral of (R/2) sqrt(det g) over [0,1]^3 = %.8f' % L)
    errs = []; acts = {}
    for N in (4, 8, 16, 32):
        S = regge_action(N)
        acts[N] = S
        errs.append(abs(S - L))
        print('N = %2d   S_N = %.8f   S_N - L = %+.6f   relative %.3f%%' % (N, S, S - L, 100 * (S - L) / L))
    ratios = [errs[i - 1] / errs[i] for i in range(1, len(errs))]
    rich = 2 * acts[32] - acts[16]
    print('Richardson 2 S_32 - S_16 = %.6f   relative error %.3f%%' % (rich, 100 * (rich - L) / L))
    ok = all(1.7 < r < 2.4 for r in ratios) and abs(rich - L) < 0.002 * L
    # controls: the wrong sign and the wrong factor are far from the computed action
    ok = ok and abs(acts[32] + L) > 1.5 * L and abs(acts[32] - 2 * L) > 0.5 * L
    for i, r in enumerate(ratios):
        print('error ratio N=%d -> %d: %.2f' % (4 * 2 ** i, 4 * 2 ** (i + 1), r))
    print('OK' if ok else 'FAILED')
    sys.exit(0 if ok else 1)
