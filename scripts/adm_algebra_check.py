"""Numerical cross-check of the constraint algebra of Lightlike/Canonical (NUMERICAL EVIDENCE, not a proof).

Dimension d = 2, Gaussian test data on a grid, the bracket of Lightlike/Canonical/ADM.lean
(`admBracket F G Fpi Gpi = dF[(Gpi,0)] - dG[(Fpi,0)]`, Gateaux derivatives by central differences):

  1. {H[N],H[M]} = D[Y], Y^i = h^{ij} (N d_j M - M d_j N), with the kinetic coefficient 1/(d-1);
  2. {D[xi],H[N]} = H[xi^k d_k N];
  control: with the coefficient 1/2 of dimension three, used in dimension two, the bracket of item 1
  differs from D[Y] (about 2.68 against 4.97), so the kinetic coefficient is not a convention.

Run: python3 -I scripts/adm_algebra_check.py   (a few seconds; numpy only)
"""
import sys

import numpy as np

L, n, d = 8.0, 321, 2
xs = np.linspace(-L, L, n)
dx = xs[1] - xs[0]
x, y = np.meshgrid(xs, xs, indexing="ij")
g = np.exp(-(x**2 + y**2) / 6)


def mat(a, b, c, e):
    m = np.zeros((n, n, 2, 2))
    m[..., 0, 0], m[..., 0, 1], m[..., 1, 0], m[..., 1, 1] = a, b, c, e
    return m


h0 = mat(1 + 0.3 * g, 0.2 * g * x, 0.2 * g * x, 1 + 0.25 * g * y**2)
pi = mat(g * (1 + x), g * y / 3, g * y / 3, g * (2 - y))
N = g * (1 + x / 5)
M = g * (1 + y / 3 + x * y / 7)
xi = np.stack([g * (1 + 0.3 * y), g * (0.5 - 0.2 * x)], -1)
inner = slice(10, -10)


def D(f, k):
    return np.gradient(f, dx, axis=k, edge_order=2)


def scalar_curvature(h):
    hi = np.linalg.inv(h)
    dh = [D(h, k) for k in range(2)]
    G = np.zeros((n, n, 2, 2, 2))
    for i in range(2):
        for j in range(2):
            for k in range(2):
                G[..., i, j, k] = 0.5 * sum(
                    hi[..., i, l] * (dh[j][..., l, k] + dh[k][..., l, j] - dh[l][..., j, k]) for l in range(2))

    def riem(r, s, m, nn):
        return (D(G[..., r, nn, s], m) - D(G[..., r, m, s], nn)
                + sum(G[..., r, m, l] * G[..., l, nn, s] - G[..., r, nn, l] * G[..., l, m, s] for l in range(2)))

    ric = np.zeros((n, n, 2, 2))
    for s in range(2):
        for nn in range(2):
            ric[..., s, nn] = sum(riem(r, s, r, nn) for r in range(2))
    return np.einsum("...sn,...sn->...", hi, ric)


def run(coef):
    def ham(h, p, Nf):
        sq = np.sqrt(np.linalg.det(h))
        hp = np.einsum("...ab,...bc->...ac", h, p)
        kin = (np.einsum("...ab,...ba->...", hp, hp) - coef * np.einsum("...aa->...", hp) ** 2) / sq
        return Nf * (kin - sq * scalar_curvature(h))

    def gpi(h, p, Nf):
        sq = np.sqrt(np.linalg.det(h))
        hp = np.einsum("...ab,...bc->...ac", h, p)
        hph = np.einsum("...ab,...bc->...ac", hp, h)
        tr = np.einsum("...aa->...", hp)
        return Nf[..., None, None] * (2 * hph - 2 * coef * tr[..., None, None] * h) / sq[..., None, None]

    def dH(Nf, k, eps=1e-4):
        return (ham(h0 + eps * k, pi, Nf) - ham(h0 - eps * k, pi, Nf)) / (2 * eps)

    def lie(Y, h):
        out = np.zeros_like(h)
        for i in range(2):
            for j in range(2):
                out[..., i, j] = sum(Y[..., k] * D(h[..., i, j], k) + h[..., k, j] * D(Y[..., k], i)
                                     + h[..., i, k] * D(Y[..., k], j) for k in range(2))
        return out

    integ = lambda f: f[inner, inner].sum() * dx * dx
    B = dH(N, gpi(h0, pi, M)) - dH(M, gpi(h0, pi, N))
    hi = np.linalg.inv(h0)
    Y = np.stack([sum(hi[..., i, j] * (N * D(M, j) - M * D(N, j)) for j in range(2)) for i in range(2)], -1)
    dy = integ(np.einsum("...ij,...ij->...", pi, lie(Y, h0)))
    lhs4 = integ(np.einsum("...ij,...ij->...", pi, lie(xi, gpi(h0, pi, N))) - dH(N, lie(xi, h0)))
    dN = np.stack([D(N, 0), D(N, 1)], -1)
    rhs4 = integ(ham(h0, pi, (xi * dN).sum(-1)))
    return integ(B), dy, lhs4, rhs4


b, dy, l4, r4 = run(1.0 / (d - 1))
print(f"coefficient 1/(d-1): {{H,H}} = {b:.4f}, D[Y] = {dy:.4f};  {{D,H}} = {l4:.4f}, H[xi.dN] = {r4:.4f}")
bw, dyw, _, _ = run(0.5)
print(f"control, coefficient 1/2 in d = 2: {{H,H}} = {bw:.4f}, D[Y] = {dyw:.4f}")
ok = abs(b - dy) < 0.01 * abs(dy) and abs(l4 - r4) < 0.01 * abs(r4) and abs(bw - dyw) > 0.2 * abs(dyw)
print("adm_algebra_check:", "OK" if ok else "FAILED")
sys.exit(0 if ok else 1)
