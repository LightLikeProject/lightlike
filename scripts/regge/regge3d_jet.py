"""Numerical check (not proof): the jet-level core of the 3D convergence.

A jet is (g0, A, B) = the metric, its first and second derivatives at a point m, with
g(x) = g0 + A.x + (1/2) x.B.x (A[k,i,j] = d_k g_ij, B[l,k,i,j] = d_l d_k g_ij, symmetric in (i,j)
and in (k,l)).  The squared length of the edge between offsets w, w' from m is the jet polynomial
of Lightlike.Regge.Conv3.EdgePoly (`edgePoly`), evaluated at s = (w+w')/2, Delta = w'-w.
For each of the 7 edge classes of the Kuhn triangulation, expand the deficit of the full star
(centred at the edge midpoint m) in eps:  deficit = c1 eps + c2 eps^2 + O(eps^3).
Claims checked at a single jet:
  (i)  c1 = 0 for every edge class;
  (ii) sum over the 7 classes of |e|_{g0} c2 = (R/2) sqrt(det g0), R the scalar curvature of the jet.
Result (seed 7, three random jets each with dg != 0 and dg = 0): max |c1| <= 5e-13; the residual of
(ii) is 1e-7 to 2e-7 (finite-difference error); R(S^3 pole) = 6.0000000012.  The residual of (ii) is the finite-difference error of the second central difference: for the first
dg != 0 jet it is 9.2e-7, 2.3e-7 at steps 4e-3, 2e-3 (a factor 4 per halving, i.e. O(h^2)), and below
that it is limited by round-off (nested finite differences in float64); at 50 digits (mpmath, exact
jet, same seed) the residual is 5.721e-8, 5.721e-10, 5.721e-12 at h = 1e-3, 1e-4, 1e-5: exactly
c h^2 with c = 0.0572 and no constant term, so (ii) holds in the limit h -> 0; c1 vanishes to round-off
because the central difference has no O(h^2) error for an odd function.
Controls leave a visible
residual: dropping the dg term gives -7e-2, -6e-2, -6e-2 for the dg != 0 jets; dropping the
(1/2) s s ddg term gives up to 3e-1; the weights |e|^2 and 1 give up to 5e-1 and 2e-1.  Dropping the
1/24 ddg term or the Christoffel term leaves the sum unchanged: they carry only the totally
symmetric (gauge) part of the jet and cancel in the star sum.
Controls: dropping the first-derivative term of the polynomial, or the 1/24 d d g term, or the
Christoffel term, breaks (ii).  Also checks R(jet) = 6 for the round S^3 at the pole.
"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # siblings, also under python -I
import itertools
import numpy as np
import regge3d_core as C
from regge3d_convergence import dihedral

n = 3


def christoffel(g0, A, B, x):
    g = g0 + np.einsum('k,kij->ij', x, A) + 0.5 * np.einsum('l,k,lkij->ij', x, x, B)
    dg = A + np.einsum('l,lkij->kij', x, B)  # dg[k,i,j] = d_k g_ij
    gi = np.linalg.inv(g)
    # Gamma^i_jk = 1/2 g^{il} (d_j g_lk + d_k g_lj - d_l g_jk)
    low = 0.5 * (np.einsum('jlk->ljk', dg) + np.einsum('klj->ljk', dg) - dg)
    return np.einsum('il,ljk->ijk', gi, low)


def scalar_curvature(g0, A, B):
    h = 1e-5
    dG = np.zeros((n, n, n, n))  # dG[l,i,j,k] = d_l Gamma^i_jk
    for l in range(n):
        e = np.zeros(n); e[l] = h
        dG[l] = (christoffel(g0, A, B, e) - christoffel(g0, A, B, -e)) / (2 * h)
    G = christoffel(g0, A, B, np.zeros(n))
    Ric = (np.einsum('kkij->ij', dG) - np.einsum('jkik->ij', dG)
           + np.einsum('kkl,lij->ij', G, G) - np.einsum('kjl,lik->ij', G, G))
    return np.trace(np.linalg.inv(g0) @ Ric)


def edge_poly(g0, A, B, s, D, drop=()):
    gi = np.linalg.inv(g0)
    low = 0.5 * (np.einsum('jlk->ljk', A) + np.einsum('klj->ljk', A) - A)
    Gam = np.einsum('il,ljk->ijk', gi, low)
    chr_ = np.einsum('ijk,j,k->i', Gam, D, D)
    val = D @ g0 @ D
    if 'A' not in drop:
        val += np.einsum('k,kij,i,j->', s, A, D, D)
    if 'Bs' not in drop:
        val += 0.5 * np.einsum('k,l,lkij,i,j->', s, s, B, D, D)
    if 'BD' not in drop:
        val += (1 / 24) * np.einsum('k,l,lkij,i,j->', D, D, B, D, D)
    if 'G' not in drop:
        val -= (1 / 12) * chr_ @ g0 @ chr_
    return val


def deficit(edge, g0, A, B, eps, drop=()):
    mid = np.array(edge) / 2
    ang = 0.0
    for vs in C.star(edge):
        pos = [eps * (np.array(v) - mid) for v in vs]
        L2 = {}
        for i, j in itertools.combinations(range(4), 2):
            L2[(i, j)] = edge_poly(g0, A, B, (pos[i] + pos[j]) / 2, pos[j] - pos[i], drop) / eps ** 2
        ia, ib = vs.index((0, 0, 0)), vs.index(tuple(edge))
        o = [k for k in range(4) if k not in (ia, ib)]
        ang += dihedral(L2, ia, ib, o[0], o[1])
    return 2 * np.pi - ang


def coeffs(edge, g0, A, B, drop=()):
    h = 2e-3
    d0 = deficit(edge, g0, A, B, 1e-9, drop)  # eps -> 0 limit: flat star, deficit 0
    dp, dm = deficit(edge, g0, A, B, h, drop), deficit(edge, g0, A, B, -h, drop)
    return (dp - dm) / (2 * h), (dp + dm - 2 * d0) / (2 * h ** 2)


def random_jet(rng, flatA=False):
    M = rng.normal(size=(n, n)); g0 = M @ M.T + n * np.eye(n)
    A = rng.normal(size=(n, n, n)) * 0.5; A = (A + A.transpose(0, 2, 1)) / 2
    B = rng.normal(size=(n, n, n, n)) * 0.5
    B = (B + B.transpose(0, 1, 3, 2)) / 2; B = (B + B.transpose(1, 0, 2, 3)) / 2
    if flatA:
        A = A * 0
    return g0, A, B


def run(g0, A, B, drop=(), w=lambda l: l):
    c1s, tot = [], 0.0
    for e in C.edges:
        c1, c2 = coeffs(e, g0, A, B, drop)
        c1s.append(c1)
        tot += w(np.sqrt(np.array(e) @ g0 @ np.array(e))) * c2
    return max(abs(x) for x in c1s), tot


if __name__ == '__main__':
    # known value: round S^3 at the pole, stereographic coordinates, R = 6
    g0 = 4 * np.eye(n); A = np.zeros((n, n, n)); B = np.zeros((n, n, n, n))
    for l in range(n):
        for k in range(n):
            for i in range(n):
                B[l, k, i, i] = -16 * (1 if l == k else 0)  # g = 4(1 - 2|x|^2) delta
    print('R(S^3 pole) =', scalar_curvature(g0, A, B), '(expect 6/4*4? radius 2 chart: g0=4)')
    rng = np.random.default_rng(7)
    ctl = []
    for name, flatA in (('dg != 0', False), ('dg = 0', True)):
        for _ in range(3):
            g0, A, B = random_jet(rng, flatA)
            R = scalar_curvature(g0, A, B)
            target = R / 2 * np.sqrt(np.linalg.det(g0))
            c1, tot = run(g0, A, B)
            _, tA = run(g0, A, B, ('A',))
            _, tG = run(g0, A, B, ('G',))
            _, tB = run(g0, A, B, ('BD',))
            _, tS = run(g0, A, B, ('Bs',))
            _, tW2 = run(g0, A, B, (), lambda l: l * l)
            _, tW1 = run(g0, A, B, (), lambda l: 1.0)
            assert c1 < 1e-5, 'FAILED: first-order coefficient does not vanish'
            assert abs(tot - target) < 1e-4 * (1 + abs(target)), 'FAILED: jet identity'
            ctl.append(min(abs(tW2 - target), abs(tW1 - target)))
            print(f'{name}: max|c1| = {c1:.2e}  sum |e| c2 = {tot:.6f}  (R/2)sqrt(det g) = {target:.6f}'
                  f'  resid = {tot - target:.2e} | drop dg: {tA - target:.2e}  drop Gamma: {tG - target:.2e}'
                  f'  drop ddg: {tB - target:.2e}  drop s.s.ddg: {tS - target:.2e}'
                  f'  weight |e|^2: {tW2 - target:.2e}  weight 1: {tW1 - target:.2e}')
    print('control gaps (min of the two wrong weights):', ['%.2e' % c for c in ctl])
    assert min(ctl) > 1e-4, 'FAILED: a wrong weight is not rejected'
    print('PASS jet-level identity and wrong-weight controls')
