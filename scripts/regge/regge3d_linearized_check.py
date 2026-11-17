"""Numerical check (not proof): the second-order coefficient of the Regge action of the periodic Kuhn complex
of mesh 1/n for the squared lengths of Christiansen's Regge interpolant of a perturbation h of the Euclidean metric.

The squared length of an edge from x to y is L = integral over s in [0,1] of (y-x)^T (I + eps h)(x + s (y-x)) (y-x)
(Christiansen 2011, eq. (5)), for a smooth Z^3-periodic symmetric matrix field h. The Regge action S_n(eps) is the
sum over the 7 edge classes and all hinges of the cell grid of (hinge length) x (2 pi - sum of the dihedral angles of
the 6-fold star). S_n(0) = 0. The check compares Q_n = S_n''(0) (central second difference, eps = 0.02) with the
second variation of the Einstein-Hilbert functional
  E = d^2/d eta^2 at 0 of the integral over [0,1]^3 of (R/2) sqrt(det g_eta), g_eta = I + eta h
(a Riemann sum of a smooth periodic function, spectrally accurate), and prints Q_n - E, which decreases with n.
Controls: the sign-reversed and doubled values of E are far from Q_n.
Usage: python3 scripts/regge/regge3d_linearized_check.py
"""
import itertools
import sys
import numpy as np

kv = np.array([(0, 0, 0), (1, 0, 0), (1, 1, 0), (1, 1, 1)], dtype=float)
perms = [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
hP = [0, 0, 0, 1, 1, 2]; hQ = [1, 2, 3, 2, 3, 3]; hR = [2, 1, 1, 0, 0, 0]; hS = [3, 3, 2, 3, 2, 1]
dirs = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1), (1, 1, 1)]
TWO_PI = 2 * np.pi

# a fixed smooth periodic symmetric perturbation h_ij = A_ij cos(2 pi k_ij . x + phi_ij)
rng = np.random.default_rng(7)
A = rng.uniform(-0.5, 0.5, (3, 3)); A = (A + A.T) / 2
K = rng.integers(-1, 2, (3, 3, 3)).astype(float)
PH = rng.uniform(0, 2 * np.pi, (3, 3))
for i in range(3):
    for j in range(i):
        K[i, j] = K[j, i]; PH[i, j] = PH[j, i]


def hfield(x):
    """h(x) for points x of shape (...,3): returns (...,3,3), derivatives not needed here."""
    out = np.zeros(x.shape[:-1] + (3, 3))
    for i in range(3):
        for j in range(3):
            out[..., i, j] = A[i, j] * np.cos(TWO_PI * np.einsum('...k,k->...', x, K[i, j]) + PH[i, j])
    return out


def hderiv(x):
    """h, dh (index mu), ddh (mu, nu) of the same field."""
    h = hfield(x)
    dh = np.zeros(x.shape[:-1] + (3, 3, 3)); ddh = np.zeros(x.shape[:-1] + (3, 3, 3, 3))
    for i in range(3):
        for j in range(3):
            ph = TWO_PI * np.einsum('...k,k->...', x, K[i, j]) + PH[i, j]
            for m in range(3):
                dh[..., m, i, j] = -A[i, j] * np.sin(ph) * TWO_PI * K[i, j][m]
                for nn in range(3):
                    ddh[..., m, nn, i, j] = -A[i, j] * np.cos(ph) * TWO_PI ** 2 * K[i, j][m] * K[i, j][nn]
    return h, dh, ddh


GX, GW = np.polynomial.legendre.leggauss(6)
GX = (GX + 1) / 2; GW = GW / 2


def sqlen(p, q, eps):
    """Squared length of the edge p->q: integral of (q-p)^T (I + eps h)(p + s (q-p)) (q-p) ds."""
    d = q - p
    tot = np.sum(d * d, axis=-1)
    acc = 0.0
    for s, w in zip(GX, GW):
        hh = hfield(p + s * d)
        acc = acc + w * np.einsum('...i,...ij,...j->...', d, hh, d)
    return tot + eps * acc


def kpos(s, h, a):
    kp = kv[a][list(perms[s])]
    return kp - (kv[hP[h]][list(perms[s])] + kv[hQ[h]][list(perms[s])]) / 2


def members(w):
    return [(s, h) for s in range(6) for h in range(6)
            if all(kv[hQ[h]][perms[s][i]] - kv[hP[h]][perms[s][i]] == w[i] for i in range(3))]


def dihedral(a, b, c, d, e, f):
    nn = (b + d - f) / 2 - (b + a - c) * (d + a - e) / (4 * a)
    p1 = b - (b + a - c) ** 2 / (4 * a)
    p2 = d - (d + a - e) ** 2 / (4 * a)
    return np.arccos(np.clip(nn / np.sqrt(p1 * p2), -1, 1))


def regge_action(n, eps):
    mesh = 1.0 / n
    z = np.array(list(itertools.product(range(n), repeat=3)), dtype=float)
    total = 0.0
    for w in dirs:
        w = np.array(w, dtype=float)
        v = mesh * (z + w / 2)
        ell = np.sqrt(sqlen(v - mesh * w / 2, v + mesh * w / 2, eps))
        ang = np.zeros(len(z))
        for (s, h) in members(w):
            P = [v + mesh * kpos(s, h, a) for a in range(4)]
            L = [sqlen(P[i], P[j], eps) for (i, j) in
                 [(hP[h], hQ[h]), (hP[h], hR[h]), (hQ[h], hR[h]), (hP[h], hS[h]), (hQ[h], hS[h]), (hR[h], hS[h])]]
            ang += dihedral(*L)
        total += float(np.sum(ell * (TWO_PI - ang)))
    return total


def density(x, eta):
    """(R/2) sqrt(det g) for g = I + eta h at points x (..., 3), from g, dg, ddg."""
    h, dh, ddh = hderiv(x)
    g = np.eye(3) + eta * h
    dg = eta * dh            # dg[..., m, i, j] = d_m g_ij
    ddg = eta * ddh          # ddg[..., m, n, i, j]
    gi = np.linalg.inv(g)
    Gl = 0.5 * (np.einsum('...nls->...lns', dg) + np.einsum('...sln->...lns', dg) - dg)  # Gamma_{l,ns}
    # Gl[..., l, n, s] = 0.5 (d_n g_ls + d_s g_ln - d_l g_ns)
    Gl = 0.5 * (np.einsum('...nls->...lns', dg) + np.einsum('...sln->...lns', dg) - np.einsum('...lns->...lns', dg))
    Gam = np.einsum('...rl,...lns->...rns', gi, Gl)
    dGl = 0.5 * (np.einsum('...mnls->...mlns', ddg) + np.einsum('...msln->...mlns', ddg)
                 - np.einsum('...mlns->...mlns', ddg))      # d_m Gamma_{l,ns}
    dgi = -np.einsum('...ra,...mab,...bl->...mrl', gi, dg, gi)
    dGam = np.einsum('...mrl,...lns->...mrns', dgi, Gl) + np.einsum('...rl,...mlns->...mrns', gi, dGl)
    # Riemann^r_{s m n} = d_m Gam^r_{ns} - d_n Gam^r_{ms} + Gam^r_{ma} Gam^a_{ns} - Gam^r_{na} Gam^a_{ms}
    Riem = (np.einsum('...mrns->...rsmn', dGam) - np.einsum('...nrms->...rsmn', dGam)
            + np.einsum('...rma,...ans->...rsmn', Gam, Gam) - np.einsum('...rna,...ams->...rsmn', Gam, Gam))
    Ric = np.einsum('...rsrn->...sn', Riem)
    R = np.einsum('...sn,...sn->...', gi, Ric)
    return R / 2 * np.sqrt(np.linalg.det(g))


def eh_second_variation(m=24, eta=1e-3):
    x1 = (np.arange(m) + 0.5) / m
    X = np.stack(np.meshgrid(x1, x1, x1, indexing='ij'), axis=-1)
    f = lambda e: density(X, e).mean()
    return (f(eta) + f(-eta) - 2 * f(0.0)) / eta ** 2


def fierz_pauli(m=24):
    """The explicit Fierz-Pauli form of the second variation, integral over the torus of
    -1/4 d_l h_mn d_l h_mn + 1/2 d_m h_mn d_l h_ln - 1/2 d_m h_mn d_n tr h + 1/4 d_l tr h d_l tr h"""
    x1 = (np.arange(m) + 0.5) / m
    X = np.stack(np.meshgrid(x1, x1, x1, indexing='ij'), axis=-1)
    h, dh, ddh = hderiv(X)          # dh[..., l, m, n] = d_l h_mn
    tr = np.einsum('...lmm->...l', dh)           # d_l tr h
    div = np.einsum('...mmn->...n', dh)          # d_m h_mn
    L = (-0.25 * np.einsum('...lmn,...lmn->...', dh, dh) + 0.5 * np.einsum('...n,...n->...', div, div)
         - 0.5 * np.einsum('...n,...n->...', div, tr) + 0.25 * np.einsum('...l,...l->...', tr, tr))
    return float(L.mean())


if __name__ == '__main__':
    E = eh_second_variation()
    FP = fierz_pauli()
    print('Fierz-Pauli form of the second variation = %.6f (matches E: %s)' % (FP, abs(FP - E) < 1e-3 * abs(E)))
    if abs(FP - E) >= 1e-3 * abs(E):
        print('FAILED'); sys.exit(1)
    print('EH second variation  d^2/deta^2 of the integral of (R/2) sqrt(det g) = %.6f' % E)
    eps = 0.02
    diffs = []
    for n in (4, 8, 16, 32):
        S0 = regge_action(n, 0.0)
        Q = (regge_action(n, eps) + regge_action(n, -eps) - 2 * S0) / eps ** 2
        diffs.append(Q - E)
        print('n = %2d   S_n(0) = %+.2e   Q_n = S_n\'\'(0) = %.6f   Q_n - E = %+.6f' % (n, S0, Q, Q - E))
    ratios = [abs(diffs[i - 1] / diffs[i]) for i in range(1, len(diffs))]
    print('error ratios (n -> 2n): ' + ', '.join('%.2f' % r for r in ratios) + '  (observation: about 4, i.e. O(1/n^2))')
    ok = all(r > 2.5 for r in ratios) and abs(diffs[-1]) < 0.03 * abs(E)
    Qn = diffs[-1] + E
    ok = ok and abs(Qn + E) > 1.5 * abs(E) and abs(Qn - 2 * E) > 0.5 * abs(E)
    print('OK' if ok else 'FAILED')
    sys.exit(0 if ok else 1)
