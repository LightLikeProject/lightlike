"""Numerical check (not a proof) of the coherent states and coherent intertwiners of
Lightlike/Spin4/Haar.lean, Coherent.lean, CoherentIntertwiner.lean, CoherentTwoValent.lean and
CoherentSuppression.lean, built independently of the Lean construction.

Conventions as in the library: doubled spin n = 2j, basis e_a = |j, j - a> (Condon-Shortley), the
spin-1/2 representation is the defining one, |j, g> = D^j(g) e_0, and the normal of g is the Bloch
vector (2 Re(conj(a) b), 2 Im(conj(a) b), |a|^2 - |b|^2) of its first column (a, b).

Haar integrals over SU(2) use Euler angles g = Rz(alpha) Ry(beta) Rz(gamma), density
sin(beta)/(16 pi^2) on [0,2pi) x [0,pi] x [0,4pi), with uniform grids in alpha, gamma and
Gauss-Legendre nodes in cos(beta). This is exact for the trigonometric polynomials that occur.
D^j(g) = exp(-i alpha Jz) exp(-i beta Jy) exp(-i gamma Jz) from the textbook spin matrices.

Checks (float64, tolerance 1e-10 unless stated):
 1. Schur averaging: int D A D^H = tr(A)/(n+1) for random A (Lean: matInt_spinMat_conj); the
    resolution of the identity (n+1) int |j,g><j,g| = 1 (resolution_cohState); int D^j = 0 for
    j > 0 (matInt_spinMat_eq_zero).
 2. the overlap |<j,g|j,h>|^2 = ((1 + nu.nu')/2)^(2j) for random g, h (normSq_inner_cohState).
 3. group averaging P = int rho(g) equals the orthogonal projection onto the common kernel of the
    total angular momentum, computed by linear algebra without any integral (avgP_conjTranspose,
    avgP_mul_avgP, isInvariantN_avgP_mulVec), for 3 and 4 links.
 4. the overlap formula of coherent intertwiners
    <i(g), i(h)> = int prod_a ((g_a^H k h_a)_00)^(J_a) dk
    for random g, h (inner_cohInt); the resolution of the identity on the invariant subspace,
    prod_a (J_a+1) E|i(g)><i(g)| = P, by Monte Carlo over Haar-random g for four spin-1/2 links
    (invariant subspace of rank 2), every entry within 5 standard errors (resolution_cohInt).
 5. two links: ||i(g1,g2)||^2 = ((1 - nu1.nu2)/2)^(2j)/(2j+1) for random normals
    (norm_sq_cohInt_two). Four links of spin j, from the group integral
    ||i||^2 = int prod_a <nu_a| k |nu_a>^(2j) dk (inner_cohInt with g = h; checked against the
    exact projector for 2j <= 4):
    - equal normals (maximally non-closing) give 0;
    - closing normals (regular tetrahedron): ||i||^2 approaches the stationary-phase value
      2 (4 pi/j)^(3/2) / (16 pi^2 sqrt(det H)), H = sum_a (1 - nu_a nu_a^T), from the two critical
      points k = +-1 (Livine-Speziale 2007; Conrady-Freidel 2009);
    - non-closing normals (one normal of the tetrahedron tilted, N = sum_a nu_a != 0): the ratio
      to the closing norm decreases geometrically in j, at the stationary-phase rate
      exp(-N^T H^-1 N / 2) per unit of 2j to leading order in |N|: the offset of the measured rate
      shrinks as the tilt shrinks.
 6. the bound proven at any valence (CoherentSuppression.lean): for the tilted tetrahedron,
    ||i||^2 <= min_i exp(-2j N_i^2 / (4 * 4)) <= exp(-2j |N|^2 / (12 * 4)) for 2j <= 40
    (normSq_cohInt_le_exp_axis, normSq_cohInt_le_exp), and a global rotation of all normals
    leaves ||i||^2 unchanged (cohInt_mul_left).
Controls, which must FAIL: the overlap formula for the non-coherent state |1, 0>; Schur averaging
with the Haar density sin(beta) replaced by 1; the resolution without the factor prod_a (J_a+1);
the closing asymptotics with the critical point k = -1 dropped; the suppression rate with H^-1
replaced by 1; a bound with twice the stationary-phase rate, exp(-2j N^T H^-1 N), on the ratio of
the tilted to the closed norm.

Usage: .venv/bin/python -I scripts/spin4/coherent_check.py
"""
import itertools
import sys

import numpy as np

rng = np.random.default_rng(20261107)
TOL = 1e-10
failures, controls_passed = [], []


def check(name, ok):
    print(("ok    " if ok else "FAIL  ") + name)
    if not ok:
        failures.append(name)


def control(name, ok):
    print(("control fails as required  " if not ok else "CONTROL PASSED (bad)  ") + name)
    if ok:
        controls_passed.append(name)


def mm(*Ms):
    out = Ms[0]
    for M in Ms[1:]:
        out = np.einsum("ij,jk->ik", out, M)
    return out


def spin_ops(n):
    j = n / 2
    m = j - np.arange(n + 1)
    Jz = np.diag(m).astype(complex)
    Jp = np.zeros((n + 1, n + 1), complex)
    for a in range(1, n + 1):  # J+ e_a = sqrt(j(j+1) - m(m+1)) e_{a-1}
        Jp[a - 1, a] = np.sqrt(j * (j + 1) - m[a] * (m[a] + 1))
    Jy = (Jp - Jp.conj().T) / (2j)
    Jx = (Jp + Jp.conj().T) / 2
    return Jx, Jy, Jz


def expm_herm(H, t):
    w, V = np.linalg.eigh(H)
    return mm(V, np.diag(np.exp(-1j * t * w)), V.conj().T)


def D(n, euler):
    al, be, ga = euler
    _, Jy, Jz = spin_ops(n)
    return mm(expm_herm(Jz, al), expm_herm(Jy, be), expm_herm(Jz, ga))


def su2(euler):
    return D(1, euler)


def quadrature(M=18, K=18):
    al = 2 * np.pi * np.arange(M) / M
    ga = 4 * np.pi * np.arange(2 * M) / (2 * M)
    x, w = np.polynomial.legendre.leggauss(K)
    be = np.arccos(x)
    pts, wts = [], []
    for a, (b, wb), c in itertools.product(al, zip(be, w), ga):
        pts.append((a, b, c))
        wts.append(wb / 2 / (M * 2 * M))  # normalised: weights sum to 1
    return pts, np.array(wts)


def random_euler():
    return (rng.uniform(0, 2 * np.pi), np.arccos(rng.uniform(-1, 1)), rng.uniform(0, 4 * np.pi))


def bloch(g):
    a, b = g[0, 0], g[1, 0]
    ab = np.conj(a) * b
    return np.array([2 * ab.real, 2 * ab.imag, abs(a) ** 2 - abs(b) ** 2])


def coh(n, euler):
    return D(n, euler)[:, 0]


PTS, WTS = quadrature()

# ---------------------------------------------------------------- 1. Schur averaging
for n in [1, 2, 3, 4]:
    A = rng.normal(size=(n + 1, n + 1)) + 1j * rng.normal(size=(n + 1, n + 1))
    avg = sum(w * mm(D(n, p), A, D(n, p).conj().T) for p, w in zip(PTS, WTS))
    check(f"Schur averaging, n={n}",
          np.abs(avg - np.trace(A) / (n + 1) * np.eye(n + 1)).max() < TOL)
    res = (n + 1) * sum(w * np.outer(coh(n, p), coh(n, p).conj()) for p, w in zip(PTS, WTS))
    check(f"resolution of the identity, n={n}", np.abs(res - np.eye(n + 1)).max() < TOL)
    avgD = sum(w * D(n, p) for p, w in zip(PTS, WTS))
    check(f"int D^j = 0, n={n}", np.abs(avgD).max() < TOL)
# control: wrong Haar density (sin beta replaced by 1: drop the Gauss-Legendre change of variables)
n = 2
A = rng.normal(size=(n + 1, n + 1))
xs = np.linspace(0, np.pi, 18)
wrong = sum(mm(D(n, (a, b, c)), A, D(n, (a, b, c)).conj().T)
            for a in np.linspace(0, 2 * np.pi, 6, endpoint=False) for b in xs
            for c in np.linspace(0, 4 * np.pi, 12, endpoint=False)) / (6 * 18 * 12)
control("Schur averaging with density 1 instead of sin(beta)",
        np.abs(wrong - np.trace(A) / (n + 1) * np.eye(n + 1)).max() < TOL)

# ---------------------------------------------------------------- 2. overlaps
worst = 0.0
for n in [1, 2, 3, 5]:
    for _ in range(20):
        e1, e2 = random_euler(), random_euler()
        lhs = abs(np.vdot(coh(n, e1), coh(n, e2))) ** 2
        rhs = ((1 + bloch(su2(e1)) @ bloch(su2(e2))) / 2) ** n
        worst = max(worst, abs(lhs - rhs))
check(f"|<j,g|j,h>|^2 = ((1+nu.nu')/2)^(2j) (max dev {worst:.1e})", worst < TOL)
# control: the non-coherent state |1,0> of spin 1
e1, e2 = random_euler(), random_euler()
v1, v2 = D(2, e1)[:, 1], D(2, e2)[:, 1]
control("overlap formula for the non-coherent state |1,0>",
        abs(abs(np.vdot(v1, v2)) ** 2 - ((1 + bloch(su2(e1)) @ bloch(su2(e2))) / 2) ** 2) < TOL)


# ---------------------------------------------------------------- 3. group averaging
def rho(spins, euler):
    out = np.ones((1, 1), complex)
    for n in spins:
        out = np.kron(out, D(n, euler))
    return out


def exact_projector(spins):
    """Orthogonal projection onto the kernel of the total angular momentum (no integrals)."""
    dim = int(np.prod([n + 1 for n in spins]))
    ops = []
    for k in range(3):
        tot = np.zeros((dim, dim), complex)
        for i, n in enumerate(spins):
            pieces = [np.eye(m + 1) for m in spins]
            pieces[i] = spin_ops(n)[k]
            op = np.ones((1, 1), complex)
            for P in pieces:
                op = np.kron(op, P)
            tot += op
        ops.append(tot)
    C = sum(mm(o.conj().T, o) for o in ops)
    w, V = np.linalg.eigh(C)
    ker = V[:, w < 1e-9]
    return mm(ker, ker.conj().T)


for spins in [(1, 1, 2), (1, 1, 1, 1), (2, 2, 2, 2), (1, 2, 2, 3)]:
    P = sum(w * rho(spins, p) for p, w in zip(PTS, WTS))
    Pex = exact_projector(spins)
    rank = round(np.trace(Pex).real)
    check(f"P = int rho = projection onto invariants, spins {spins}, rank {rank}",
          np.abs(P - Pex).max() < 1e-9)


# ---------------------------------------------------------------- 4. coherent intertwiners
def coh_int(spins, eulers, P):
    v = np.ones(1, complex)
    for n, e in zip(spins, eulers):
        v = np.kron(v, coh(n, e))
    return np.einsum("ij,j->i", P, v)


worst = 0.0
for spins in [(1, 1, 2), (2, 2, 2, 2)]:
    Pex = exact_projector(spins)
    for _ in range(5):
        g = [random_euler() for _ in spins]
        h = [random_euler() for _ in spins]
        lhs = np.vdot(coh_int(spins, g, Pex), coh_int(spins, h, Pex))
        rhs = sum(w * np.prod([(mm(su2(ga).conj().T, su2(k), su2(ha))[0, 0]) ** n
                               for n, ga, ha in zip(spins, g, h)]) for k, w in zip(PTS, WTS))
        worst = max(worst, abs(lhs - rhs))
check(f"overlap formula of coherent intertwiners (max dev {worst:.1e})", worst < 1e-9)
# resolution of the identity on the invariant subspace, Monte Carlo
spins = (1, 1, 1, 1)
Pex = exact_projector(spins)
S = 40000
fac = np.prod([n + 1 for n in spins])
acc, acc2 = np.zeros_like(Pex), np.zeros(Pex.shape)
for _ in range(S):
    v = coh_int(spins, [random_euler() for _ in spins], Pex)
    X = fac * np.outer(v, v.conj())
    acc += X
    acc2 += np.abs(X) ** 2
est = acc / S
se = np.sqrt(np.maximum(acc2 / S - np.abs(est) ** 2, 0) / S)  # standard error of each entry
dev = np.abs(est - Pex)
zmax = (dev / np.maximum(se, 1e-12)).max()
check(f"resolution on the invariant subspace, rank {round(np.trace(Pex).real)}, Monte Carlo {S} "
      f"samples (max dev {dev.max():.1e}, at most {zmax:.1f} standard errors <= 5)", zmax <= 5)
zwrong = (np.abs(est / fac - Pex) / np.maximum(se, 1e-12)).max()
control("resolution without the factor prod_a (J_a+1), within 5 standard errors", zwrong <= 5)

# ---------------------------------------------------------------- 5. norms and closure
worst = 0.0
for n in [1, 2, 3, 6]:
    P2 = exact_projector((n, n))
    for _ in range(20):
        e1, e2 = random_euler(), random_euler()
        lhs = np.linalg.norm(coh_int((n, n), [e1, e2], P2)) ** 2
        rhs = ((1 - bloch(su2(e1)) @ bloch(su2(e2))) / 2) ** n / (n + 1)
        worst = max(worst, abs(lhs - rhs))
check(f"two links: ||i||^2 = ((1-nu1.nu2)/2)^(2j)/(2j+1) (max dev {worst:.1e})", worst < TOL)


def euler_of_normal(nu):
    """An element of SU(2) whose normal is the unit vector nu."""
    th = np.arccos(np.clip(nu[2], -1, 1))
    ph = np.arctan2(nu[1], nu[0])
    return (ph, th, 0.0)


tet = np.array([[0, 0, 1], [2 * np.sqrt(2) / 3, 0, -1 / 3],
                [-np.sqrt(2) / 3, np.sqrt(2 / 3), -1 / 3],
                [-np.sqrt(2) / 3, -np.sqrt(2 / 3), -1 / 3]])
tilt = tet.copy()
tilt[0] = np.array([np.sin(0.4), 0, np.cos(0.4)])
same = np.array([[0, 0, 1]] * 4)
check("closure: regular tetrahedron normals sum to 0, tilted ones do not",
      np.abs(tet.sum(0)).max() < 1e-12 and np.abs(tilt.sum(0)).max() > 0.1)
exact = {}
for n in [1, 2, 3, 4]:
    P4 = exact_projector((n, n, n, n))
    for name, nus in [("closed", tet), ("tilted", tilt), ("equal", same)]:
        v = coh_int((n,) * 4, [euler_of_normal(nu) for nu in nus], P4)
        exact[(name, n)] = np.linalg.norm(v) ** 2
check("four links: equal (maximally non-closing) normals give 0",
      all(exact[("equal", n)] < TOL for n in [1, 2, 3, 4]))


def su2_grid(M, K):
    """The entries of g = Rz(alpha) Ry(beta) Rz(gamma) on the quadrature grid, and the weights."""
    al = 2 * np.pi * np.arange(M) / M
    ga = 4 * np.pi * np.arange(2 * M) / (2 * M)
    x, w = np.polynomial.legendre.leggauss(K)
    A, B, C = np.meshgrid(al, np.arccos(x), ga, indexing="ij")
    W = np.broadcast_to(w[None, :, None] / 2 / (M * 2 * M), A.shape).ravel()
    A, B, C = A.ravel(), B.ravel(), C.ravel()
    c, s = np.cos(B / 2), np.sin(B / 2)
    k = [[np.exp(-0.5j * (A + C)) * c, -np.exp(-0.5j * (A - C)) * s],
         [np.exp(0.5j * (A - C)) * s, np.exp(0.5j * (A + C)) * c]]
    return k, W, (A, B, C)


k, W, (A, B, C) = su2_grid(3, 3)
check("closed-form SU(2) entries on the grid agree with D^(1/2)",
      max(np.abs(np.array(k)[:, :, i] - su2((A[i], B[i], C[i]))).max()
          for i in range(len(W))) < TOL)


def norm_integral(nus, n):
    """||i||^2 = int prod_a <nu_a| k |nu_a>^n dk (inner_cohInt with g = h), exact quadrature."""
    k, W, _ = su2_grid(2 * n + 6, 2 * n + 6)
    f = np.ones_like(W, complex)
    for nu in nus:
        s = su2(euler_of_normal(nu))[:, 0]
        f *= sum(np.conj(s[a]) * k[a][b] * s[b] for a in range(2) for b in range(2)) ** n
    return (W * f).sum()


CONFIGS = [("closed", tet), ("tilted", tilt), ("equal", same)]
worst = max(abs(norm_integral(nus, n) - exact[(name, n)])
            for n in [1, 2, 3, 4] for name, nus in CONFIGS)
check(f"four links: group integral = exact projector norm for 2j <= 4 (max dev {worst:.1e})",
      worst < TOL)
NS = list(range(1, 41))
closed = {n: norm_integral(tet, n).real for n in NS}
tilted = {n: norm_integral(tilt, n).real for n in NS}


def hess(nus):
    return sum(np.eye(3) - np.outer(v, v) for v in nus)


def asym_closed(n, crit=2):
    """Stationary-phase value of the closing norm, from `crit` critical points k = +-1, j = n/2."""
    dH = np.linalg.det(hess(tet))
    return crit * (4 * np.pi / (n / 2)) ** 1.5 / (16 * np.pi ** 2 * np.sqrt(dH))


print("      2j   ||i||^2 closed   / asymptotic   tilted/closed")
for n in [1, 2, 4, 8, 16, 32, 40]:
    print(f"      {n:2d}   {closed[n]:.4e}       {closed[n] / asym_closed(n):.4f}       "
          f"{tilted[n] / closed[n]:.4f}")
off = [abs(closed[n] / asym_closed(n) - 1) for n in [8, 16, 24, 32, 40]]
check(f"four links, closing normals: ||i||^2 / stationary-phase value -> 1 (offset at 2j=40: "
      f"{off[-1]:.3f} < 0.02, decreasing)",
      off[-1] < 0.02 and all(a > b for a, b in zip(off, off[1:])))
control("closing asymptotics with the critical point k = -1 dropped, within 2% at 2j=40",
        abs(closed[40] / asym_closed(40, crit=1) - 1) < 0.02)
ratio = [tilted[n] / closed[n] for n in NS]
check("four links, tilted normals: tilted/closed decreases strictly in j, from 1 to below 0.3",
      all(a > b for a, b in zip(ratio, ratio[1:])) and ratio[0] < 1 and ratio[-1] < 0.3)


def rate_offset(nus, n, Hinv=True):
    """|ln q / ln q* - 1| for the measured rate q = r_n / r_(n-1) of r = tilted/closed and the
    stationary-phase rate q* = exp(-N^T H^-1 N / 2) (or exp(-|N|^2 / 2) with H^-1 replaced by 1)."""
    N = nus.sum(0)
    q = (norm_integral(nus, n).real / norm_integral(tet, n).real) / \
        (norm_integral(nus, n - 1).real / norm_integral(tet, n - 1).real)
    lq = -N @ np.linalg.solve(hess(nus), N) / 2 if Hinv else -N @ N / 2
    return abs(np.log(q) / lq - 1)


offsets = []
for t in [0.4, 0.2, 0.1]:
    nus = tet.copy()
    nus[0] = np.array([np.sin(t), 0, np.cos(t)])
    offsets.append(rate_offset(nus, 60))
print("      rate offset |ln q/ln q* - 1| at 2j=60 for tilts 0.4, 0.2, 0.1: "
      + ", ".join(f"{o:.2e}" for o in offsets))
check("four links: suppression rate = exp(-N^T H^-1 N/2) per unit of 2j to leading order in |N| "
      "(offset < 0.025 at tilt 0.4, shrinking with the tilt)",
      offsets[0] < 0.025 and offsets[0] > offsets[1] > offsets[2])
control("suppression rate with H^-1 replaced by 1, within 0.025 at tilt 0.4",
        rate_offset(tilt, 60, Hinv=False) < 0.025)

# ---------------------------------------------------------------- 6. the proven bound, any valence
def proven_bounds(nus, n):
    """The bounds of normSq_cohInt_le_exp_axis (best axis) and normSq_cohInt_le_exp, K_a = 1."""
    N, S = nus.sum(0), len(nus)
    return min(np.exp(-n * N[i] ** 2 / (4 * S)) for i in range(3)), np.exp(-n * N @ N / (12 * S))


ok = all(tilted[n] <= proven_bounds(tilt, n)[0] + TOL
         and proven_bounds(tilt, n)[0] <= proven_bounds(tilt, n)[1] + TOL for n in NS)
check("four links, tilted normals: ||i||^2 <= exp(-2j N_i^2/16) <= exp(-2j |N|^2/48), 2j <= 40",
      ok)
b_axis, b_all = proven_bounds(tilt, NS[-1])
print(f"      2j={NS[-1]}: tilted ||i||^2 = {tilted[NS[-1]]:.2e}, best-axis bound {b_axis:.3f}, "
      f"|N|^2 bound {b_all:.3f}")
Q, _ = np.linalg.qr(rng.normal(size=(3, 3)))
Q = Q * np.sign(np.linalg.det(Q))
worst = max(abs(norm_integral(tilt @ Q.T, n) - norm_integral(tilt, n)) for n in range(1, 11))
check(f"four links: a global rotation of the normals leaves ||i||^2 unchanged (max dev "
      f"{worst:.1e}, 2j <= 10)", worst < TOL)
lq2 = -tilt.sum(0) @ np.linalg.solve(hess(tilt), tilt.sum(0))
control("tilted/closed <= exp(-2j N^T H^-1 N) (twice the stationary-phase rate) for 2j <= 40",
        all(tilted[n] / closed[n] <= np.exp(n * lq2) for n in NS))

print()
if failures:
    print(f"{len(failures)} check(s) FAILED: {failures}")
if controls_passed:
    print(f"{len(controls_passed)} control(s) passed but must fail: {controls_passed}")
sys.exit(1 if failures or controls_passed else 0)
