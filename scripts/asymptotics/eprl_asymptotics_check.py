"""Numerical check (not a proof) of the statement of the large-spin asymptotics of the coherent 15j
integral and of the Euclidean EPRL vertex in Lightlike/Asymptotics/EPRL/Amplitude.lean,
ReggeState.lean and Lightlike/Asymptotics/EPRL/Formula.lean, and of the gluing, stationarity, suppression and critical-point
results proved there (Gluing.lean, Lightlike/Asymptotics/EPRL/Decay.lean, GluingSolutions.lean, Normals.lean, Lightlike/Asymptotics/EPRL/Critical.lean),
built independently of the Lean files with numpy.

Sources: Barrett, Dowdall, Fairbairn, Gomes, Hellmann, J. Math. Phys. 50 (2009) 112504,
arXiv:0902.1170, Theorem 1 (BDFGH); Barrett, Fairbairn, Hellmann, arXiv:0912.4907, eq. (16) (BFH).

Conventions as in Lean. The ten edges of K5 are ordered 01, 02, 03, 04, 12, 13, 14, 23, 24, 34.
Spins are doubled (n_e = 2 j_e). The propagator of the edge e = ab is
    P_e(X) = ((g_ab eps)^H X_a^H X_b g_ba)_00 = <X_a g_ab eps e0, X_b g_ba e0>,  eps = [[0,-1],[1,0]],
and the coherent 15j integral is coh15j(n, g) = int_{SU(2)^5} prod_e P_e^{n_e} (Haar probability
measure on each factor). The Regge state of a 4-simplex sigma (Lean: reggeState) is
g_ab = Q_a^H m_e d(Theta_e), g_ba = Q_b^H m_e eps, with Q_a the quaternion matrix of the outward unit
normal N_a of the tetrahedron opposite a, m_e the lift of the unit vector b_e of Q_a Q_b^H = c + i b.sigma
(Lean: liftSU2, alpha = sqrt((1 + v2)/2)), d(t) = diag(e^{it/2}, e^{-it/2}) and Theta_e the exterior
dihedral angle. The critical points with X_4 = 1 are U+_a = Q_4^H Q_a and U-_a = 1 (Lean: critPlus,
critMinus). The Hessian (Lean: hessAmp) is H = F(X)^-1 d^2_theta F(chart X theta)|_0 in the chart
X_a exp((i/2) theta_a . sigma), a = 0..3, X_4 fixed, and the amplitude of a critical point is
det(-H)^(-1/2) in the branch of Lean's invSqrtDet: the product of the principal roots mu^(-1/2) over
the eigenvalues mu of -H. For matrices of size 3 and more this is in general not the principal root
of det(-H); check 3 compares the two. The formula (Lean: Coh15jAsymptoticFormula) reads
    coh15j(lam n) = (2 pi/lam)^6 2^4/(4 pi)^8 (e^{i lam Phi} A+ + e^{-i lam Phi} A-) + O(lam^-7),
    Phi = sum_e (n_e/2) Theta_e (Lean: reggeAction).

Checks, which must pass:
 1. the Regge state, on the regular simplex of Lightlike/Asymptotics/EPRL/Formula.lean (Lean: regSimplex) and two random
    simplices: Theta_e = arccos(N_a . N_b) equals pi minus the interior dihedral angle computed from
    the vertices alone (projection onto the plane orthogonal to the triangle); on the regular
    simplex Theta = pi - arccos(1/4) and all triangle areas are sqrt(3)/2 (Lean:
    reggeAngle_regular, triArea_regular); closure sum_b area_ab bloch(g_ab) = 0 at every node;
    at U+ and U- (spins proportional to the areas) |F| = 1, F = e^{+-i Phi}, and the gradient
    vanishes; the propagators do not change when m_e is replaced by m_e d(chi);
 2. sign flips: F(eps_a U) = F(U) for all 16 sign patterns eps in {+-1}^4 when the spin sum at every
    node is even (Lean: the parity hypothesis), so each critical point comes with 2^4 copies in the
    gauge X_4 = 1; the Haar measure is a probability measure and fixing X_4 = 1 does not change the
    integral (exact quadrature, all five factors integrated, at lam = 1, 2);
 3. the Hessian at the instances of Lightlike/Asymptotics/EPRL/Formula.lean (Lean: regular_coh15j_hyps with n_e = 3 and
    regular_eprl_hyps with gamma = 1/2, (n, m) = (3, 1)): H is symmetric; F^-1 d^2 F equals
    d^2 log F at U+-; H scales linearly in n; det(-H+-) is recorded with its distance from 0
    (|det|, smallest singular value, smallest eigenvalue of Re(-H), which is positive, so
    det(-H) != 0 at these instances); the branch: for M = (1 + 2i) I_3 the script's invSqrtDet is
    (1 + 2i)^(-3/2), the factorised Gaussian value, which is minus the principal root of det M (Lean:
    cpow_det_diagonal_wrong_branch); at U+- of the regular simplex (n = 1 and n = 3), of the two
    random simplices and of 60 further random simplices (a third of them nearly flat) the
    eigenvalue arguments of -H sum to less than pi in absolute value, so there invSqrtDet equals the
    principal root of det(-H), and check 5 tests the common value;
 4. the constant 2^4/(4 pi)^8, derived independently: in the graph chart
    v -> X_a (sqrt(1 - |v|^2) + i v . sigma) the Haar probability density is 1/(2 pi^2 sqrt(1 - |v|^2))
    (normalisation checked by quadrature), the Hessian H_v computed by finite differences equals
    4 H_theta, and 2^4 (2 pi^2)^-4 det(-H_v)^(-1/2) equals 2^4 (4 pi)^-8 det(-H_theta)^(-1/2);
 5. the formula against the exact integral: coh15j(mu . 1) at the regular simplex for
    mu = 1..MU+1 (mu = 3 lam covers the Lean instance n_e = 3), computed exactly by product
    quadrature on SU(2) (Gauss-Legendre in |alpha|^2, uniform in the two phases, exact for the
    polynomial degree at each node; a finer rule gives the same value to rounding and a too coarse
    one does not), with X_4 = 1 and the K4 network of the other four nodes
    contracted over the binomial bases of the edge spaces. The exact values are real. A
    least-squares fit of mu^6 coh15j = 2 Re(e^{i mu Phi} (a + b/mu)) on windows of six consecutive
    mu gives the leading coefficient a; the ratio r = a / ((2 pi)^6 2^4 (4 pi)^-8 A+) must satisfy
    |r - 1| < 0.03 on the last window (mu = MU-4..MU+1) and be closer to 1 there than on the window
    8..13. The 1/mu term models the O(lam^-7) remainder; its coefficient b is printed;
 6. the EPRL formula (Lean: EPRLAsymptoticFormula) at gamma = 1/2, (n, m) = (3, 1): n - m = gamma (n + m);
    the four-term leading term equals the product of the two 15j leading terms (phases
    +-S and +-gamma S with S = Phi(n + m)) to 1e-10 of one term, so by Fubini the EPRL statement follows from
    two instances of the 15j statement; the exact EPRL integral is the product of two exact 15j
    values;
 7. non-vacuity: lam^12 |EPRL leading term| and lam^6 |15j leading term| do not tend to 0: their
    maxima over the windows [200 k, 200 (k + 1)), k = 0..19, are all at least half of the overall
    maximum;
 8. gluing and stationarity (Gluing.lean, Lightlike/Asymptotics/EPRL/Decay.lean): at 2000 random points with random SU(2) data
    |P_e| <= 1 and |P_e|^2 = (1 + nu(X_a g_ab eps) . nu(X_b g_ba))/2 (Lean: norm_prop_le,
    normSq_prop); at 20 random gluing points (g_ba = X_b^H X_a g_ab eps d(phi_e), random spins
    1..4) |F| = 1 and the finite-difference gradient of theta -> F(chart X theta) at 0 equals
    F (i/2) (sum_e n_e nu_e)_k, with nu_e = nu(g_ab) at the node a and nu(g_ba) at the node b
    (Lean: coordDeriv_cohAmp_chart_of_glued); the gradient is not small there, since these points
    do not close; there the closure vectors rotated by X_a, sum_e n_e nu(X_a g_ab), add up to 0
    over the five nodes and have the lengths of the unrotated ones, so closure at the nodes 0..3
    gives closure at the node 4 (Lean: closure_last_of_glued); the twisted data g_ab = h_e,
    g_ba = h_e eps of Gluing.lean give F = 1 at X = 1, without eps F = 0; the triangle 012 is
    stationary there and all spins 1 is not (Lean: triangle_stationary,
    twistData_one_not_stationary); for g = 1 and spins 1 on the triangle 014
    (Lean: oneData) the maximum of |F| is 3 sqrt(3)/8 < 1: it is attained when the Bloch vectors of
    X_0, X_1, X_4 lie at 120 degrees in a plane, and no point of a random sample of 20000 exceeds
    it, so the integral decays like (3 sqrt(3)/8)^lam (Lean: coh15j_oneData_decay);
 9. the critical set of the Regge state (Lightlike/Asymptotics/EPRL/Critical.lean), a sampled search, not a proof: on the
    regular simplex and six random simplices any three normals are independent (Lean:
    linearIndependent_outNormal_three) and U+, U- lie in different classes (Lean:
    critical_classes_disjoint); Levenberg-Marquardt on the 30 gluing equations in the chart with
    X_4 = 1, from 120 (regular) or 40 (random) random starts, converges only to points with
    X_a = +-U+_a for every a or X_a = +-U-_a for every a, finds both classes, and |F| = 1 there with
    the areas as spins (Lean: reggeState_critical_iff, glued_iff_two_classes).
Controls, which must FAIL:
 (a) the formula without the sign-flip count 2^4, against the exact integral (check 5);
 (b) the formula with the graph-chart density (2 pi^2)^-4 and the theta-chart Hessian (check 5);
 (c) a wrong phase convention: the Regge state without d(Theta_e), with the formula unchanged
     (check 5);
 (d) spins not proportional to the areas (n_01 = 3, all others 1): U+ is not stationary (check 1);
 (e) the sign-flip invariance with an odd spin sum at a node (check 2);
 (f) the principal root of det M in place of invSqrtDet for M = (1 + 2i) I_3, against the
     factorised Gaussian value (check 3);
 (g) the derivative formula at the gluing points with the rotated normals nu(X_a g_ab), nu(X_b g_ba)
     in place of nu(g_ab), nu(g_ba) (check 8);
 (h) the derivative formula at points that are not glued (check 8);
 (i) the sum over the five nodes of the rotated closure vectors at points that are not glued
     (check 8);
 (j) the mixed point X_0 = U-_0, X_a = U+_a otherwise, as a gluing point with |F| = 1 (check 9);
 (k) the wrong-order point X_a = (U+_a)^H as a gluing point with |F| = 1 (check 9);
 (l) a degenerate simplex (vertex 4 in the hyperplane of 0123): independence of any three normals
     (check 9).
The script exits with code 0 only if every check passes and every control fails.

Usage: python3 -I scripts/asymptotics/eprl_asymptotics_check.py
"""
import sys
from math import comb

import numpy as np

MU = 19          # exact values for mu = 1..MU+1
failures = []
controls_passed = []

SX = np.array([[0, 1], [1, 0]], complex)
SY = np.array([[0, -1j], [1j, 0]])
SZ = np.array([[1, 0], [0, -1]], complex)
SIG = [SX, SY, SZ]
EPS = np.array([[0, -1], [1, 0]], complex)
EDGES = [(a, b) for a in range(5) for b in range(a + 1, 5)]


def check(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + (f"  [{detail}]" if detail else ""))
    if not ok:
        failures.append(name)


def control(name, ok, detail=""):
    print(("control FAILS as expected: " if not ok else "control PASSED (bad): ") + name +
          (f"  [{detail}]" if detail else ""))
    if ok:
        controls_passed.append(name)


def herm(M):
    return M.conj().T


def quat(v):
    return np.array([[v[0] + 1j * v[1], v[2] + 1j * v[3]], [-v[2] + 1j * v[3], v[0] - 1j * v[1]]])


def lift(v):
    """Lean: liftSU2."""
    if v[2] == -1:
        return EPS.copy()
    al = np.sqrt((1 + v[2]) / 2)
    be = (v[0] + 1j * v[1]) / (2 * al)
    return np.array([[al, -np.conj(be)], [be, al]])


def bloch(g):
    a, b = g[0, 0], g[1, 0]
    return np.array([2 * (np.conj(a) * b).real, 2 * (np.conj(a) * b).imag, abs(a) ** 2 - abs(b) ** 2])


def dmat(t):
    return np.diag([np.exp(1j * t / 2), np.exp(-1j * t / 2)])


# ---------------------------------------------------------------- geometry and the Regge state
def normals(P):
    out = []
    for a in range(5):
        o = [P[b] for b in range(5) if b != a]
        nv = np.linalg.svd(np.array([x - o[0] for x in o[1:]]))[2][-1]
        if np.dot(nv, P[a] - o[0]) > 0:
            nv = -nv
        out.append(nv / np.linalg.norm(nv))
    return out


def area(P, a, b):
    t = [P[c] for c in range(5) if c not in (a, b)]
    u, v = t[1] - t[0], t[2] - t[0]
    return 0.5 * np.sqrt(np.dot(u, u) * np.dot(v, v) - np.dot(u, v) ** 2)


def interior_dihedral(P, a, b):
    T = [P[c] for c in range(5) if c not in (a, b)]
    B = np.array([T[1] - T[0], T[2] - T[0]]).T

    def proj(v):
        return v - B @ np.linalg.lstsq(B, v, rcond=None)[0]
    u, w = proj(P[b] - T[0]), proj(P[a] - T[0])
    return np.arccos(np.dot(u, w) / np.linalg.norm(u) / np.linalg.norm(w))


def regge_state(P, phases=True, twist=None):
    """Lean: reggeState. `twist` multiplies every m_e by d(chi_e) on the right."""
    N = normals(P)
    Qs = [quat(x) for x in N]
    g, Th = [], []
    for e, (a, b) in enumerate(EDGES):
        M = Qs[a] @ herm(Qs[b])
        w = np.array([M[0, 1].imag, M[0, 1].real, M[0, 0].imag])
        m = lift(w / np.linalg.norm(w))
        if twist is not None:
            m = m @ dmat(twist[e])
        t = np.arccos(np.clip(N[a] @ N[b], -1, 1))
        Th.append(t)
        d = dmat(t) if phases else np.eye(2)
        g.append((herm(Qs[a]) @ m @ d, herm(Qs[b]) @ m @ EPS))
    return N, Qs, g, np.array(Th)


def prop(g, X, e):
    a, b = EDGES[e]
    return (herm(g[e][0] @ EPS) @ herm(X[a]) @ X[b] @ g[e][1])[0, 0]


def amp(g, X, n):
    return np.prod([prop(g, X, e) ** n[e] for e in range(10)])


def log_amp(g, X, n):
    return sum(n[e] * np.log(prop(g, X, e)) for e in range(10))


def expsu2(t):
    r = np.linalg.norm(t)
    if r == 0:
        return np.eye(2, dtype=complex)
    u = t / r
    return np.cos(r / 2) * np.eye(2) + 1j * np.sin(r / 2) * sum(u[k] * SIG[k] for k in range(3))


def graph(v):
    return np.sqrt(1 - v @ v) * np.eye(2) + 1j * sum(v[k] * SIG[k] for k in range(3))


def chart(X, th, local=expsu2):
    """Lean: chart (theta_a = th[3a : 3a + 3], X_4 fixed)."""
    return [X[a] @ local(th[3 * a:3 * a + 3]) for a in range(4)] + [X[4]]


def hessian(f, h=1e-4):
    I = np.eye(12)
    Hm = np.zeros((12, 12), complex)
    for i in range(12):
        for j in range(i, 12):
            Hm[i, j] = Hm[j, i] = (f(h * I[i] + h * I[j]) - f(h * I[i] - h * I[j])
                                   - f(-h * I[i] + h * I[j]) + f(-h * I[i] - h * I[j])) / (4 * h * h)
    return Hm


def gradient(f, h=1e-5):
    I = np.eye(12)
    return np.array([(f(h * I[i]) - f(-h * I[i])) / (2 * h) for i in range(12)])


def hess_amp(g, X, n, local=expsu2):
    """Lean: hessAmp, F(X)^-1 times the Hessian of F in the chart."""
    return hessian(lambda th: amp(g, chart(X, th, local), n)) / amp(g, X, n)


def inv_sqrt_det(M):
    """Lean: invSqrtDet, the product of the principal powers mu^(-1/2) over the eigenvalues."""
    return np.prod(np.linalg.eigvals(M).astype(complex) ** -0.5)


def principal_inv_sqrt_det(M):
    """The principal root det(M)^(-1/2), which is not Lean's invSqrtDet in general."""
    return np.linalg.det(M).astype(complex) ** -0.5


def arg_sum(M):
    """The sum of the arguments of the eigenvalues of M."""
    return np.angle(np.linalg.eigvals(M).astype(complex)).sum()


# ---------------------------------------------------------------- exact coherent 15j values
def haar_rule(L):
    """Product rule on SU(2), X = [[alpha, -conj beta], [beta, conj alpha]], alpha = sqrt(u) e^{i p},
    beta = sqrt(1 - u) e^{i q}, u uniform on [0, 1] and p, q uniform: exact for polynomials of
    degree <= L in the entries and their conjugates."""
    K, M = L // 4 + 1, L + 1
    u, wu = np.polynomial.legendre.leggauss(K)
    u, wu = (u + 1) / 2, wu / 2
    ph = 2 * np.pi * np.arange(M) / M
    U, P1, P2 = np.meshgrid(u, ph, ph, indexing="ij")
    W = np.broadcast_to(wu[:, None, None], U.shape) / M ** 2
    al, be = np.sqrt(U) * np.exp(1j * P1), np.sqrt(1 - U) * np.exp(1j * P2)
    X = np.empty(U.shape + (2, 2), complex)
    X[..., 0, 0], X[..., 0, 1], X[..., 1, 0], X[..., 1, 1] = al, -np.conj(be), be, np.conj(al)
    return X.reshape(-1, 2, 2), W.reshape(-1)


def coh_vec(u, N):
    """Components sqrt(C(N, k)) u0^(N-k) u1^k, so that <u, v>^N = sum_k conj(c_k(u)) c_k(v)."""
    k = np.arange(N + 1)
    c = np.sqrt(np.array([comb(N, int(x)) for x in k], float))
    return c[None, :] * u[:, 0:1] ** (N - k)[None, :] * u[:, 1:2] ** k[None, :]


def apply(X, v):
    return np.einsum("qij,j->qi", X, v)


def inner(u, v):
    return (np.conj(u) * v).sum(-1)


def node_tensor(a, n, zeta, omega, extra=0, fixed4=True):
    """int dX prod over the edges at a: closed legs to node 4 (if X_4 = 1) and open legs (binomial
    basis), conjugated on the antilinear side (a = source)."""
    L = sum(n[e] for e, (x, y) in enumerate(EDGES) if a in (x, y)) + extra
    X, W = haar_rule(L)
    fac = W.astype(complex)
    legs = []
    for e, (x, y) in enumerate(EDGES):
        if fixed4 and x == a and y == 4:
            fac = fac * inner(apply(X, zeta[e]), omega[e]) ** n[e]
        elif x == a:
            legs.append(np.conj(coh_vec(apply(X, zeta[e]), n[e])))
        elif y == a:
            legs.append(coh_vec(apply(X, omega[e]), n[e]))
    A = fac[:, None] * legs[0]
    for lg in legs[1:-1]:
        A = (A[:, :, None] * lg[:, None, :]).reshape(len(W), -1)
    with np.errstate(all="ignore"):   # the system BLAS can raise spurious flags in matmul
        T = A.T @ legs[-1]
    assert np.isfinite(T).all()
    return T.reshape([lg.shape[1] for lg in legs])


def coh15j_exact(n, g, extra=0):
    """Lean: coh15j, with X_4 = 1 (Haar invariance); K4 contraction of nodes 0..3."""
    zeta = [g[e][0] @ EPS[:, 0] for e in range(10)]
    omega = [g[e][1][:, 0] for e in range(10)]
    T = [node_tensor(a, n, zeta, omega, extra) for a in range(4)]
    # legs: node 0 (01, 02, 03), node 1 (01, 12, 13), node 2 (02, 12, 23), node 3 (03, 13, 23)
    return np.einsum("abc,ade,bdf,cef->", *T)


def coh15j_full(n, g):
    """All five factors integrated (no gauge fixing)."""
    zeta = [g[e][0] @ EPS[:, 0] for e in range(10)]
    omega = [g[e][1][:, 0] for e in range(10)]
    T = [node_tensor(a, n, zeta, omega, fixed4=False) for a in range(5)]
    # node 0 (01,02,03,04), 1 (01,12,13,14), 2 (02,12,23,24), 3 (03,13,23,34), 4 (04,14,24,34)
    return np.einsum("abcd,aefg,behi,cfhj,dgij->", *T)


# ---------------------------------------------------------------- the simplices
T_REG = (1 - np.sqrt(5)) / 4
P_REG = [np.eye(4)[i] for i in range(4)] + [T_REG * np.ones(4)]
rng = np.random.default_rng(2)
P_RAND = [[rng.normal(size=4) for _ in range(5)] for _ in range(2)]
ONE = [1] * 10
C15 = (2 * np.pi) ** 6 * 2 ** 4 / (4 * np.pi) ** 8


def crit_points(Qs):
    return [herm(Qs[4]) @ Qs[a] for a in range(5)], [np.eye(2, dtype=complex)] * 5


# ---------------------------------------------------------------- 1. the Regge state
print("1. the Regge state")
for label, P in [("regular", P_REG)] + [(f"random {k}", p) for k, p in enumerate(P_RAND)]:
    N, Qs, g, Th = regge_state(P)
    A = [area(P, *e) for e in EDGES]
    dd = max(abs(Th[e] - (np.pi - interior_dihedral(P, *EDGES[e]))) for e in range(10))
    check(f"[{label}] Theta = pi - interior dihedral angle", dd < 1e-12, f"err {dd:.1e}")
    if label == "regular":
        check("[regular] Theta = pi - arccos(1/4), areas sqrt(3)/2",
              np.abs(Th - (np.pi - np.arccos(0.25))).max() < 1e-12 and
              np.abs(np.array(A) - np.sqrt(3) / 2).max() < 1e-12, f"Theta = {Th[0]:.6f}")
    clo = max(np.linalg.norm(sum(A[e] * bloch(g[e][0 if EDGES[e][0] == a else 1])
                                 for e in range(10) if a in EDGES[e])) for a in range(5))
    check(f"[{label}] closure at every node", clo < 1e-12, f"max defect {clo:.1e}")
    Up, Um = crit_points(Qs)
    Phi = sum(A[e] / 2 * Th[e] for e in range(10))
    for name, U, s in (("U+", Up, 1), ("U-", Um, -1)):
        F = amp(g, U, A)
        G = gradient(lambda th: log_amp(g, chart(U, th), A))
        check(f"[{label}] {name}: |F| = 1, F = e^({'+' if s > 0 else '-'}i Phi), grad = 0",
              abs(abs(F) - 1) < 1e-12 and abs(F - np.exp(1j * s * Phi)) < 1e-12 and
              np.linalg.norm(G) < 1e-8, f"|F| - 1 = {abs(F) - 1:.1e}, |grad| = {np.linalg.norm(G):.1e}")
    _, _, g2, _ = regge_state(P, twist=rng.uniform(0, 2 * np.pi, 10))
    X = [quat(v / np.linalg.norm(v)) for v in rng.normal(size=(5, 4))]
    dev = max(abs(prop(g, X, e) - prop(g2, X, e)) for e in range(10))
    check(f"[{label}] propagators independent of the phase of m_e", dev < 1e-12, f"{dev:.1e}")

N, Qs, g_reg, Th = regge_state(P_REG)
Up, Um = crit_points(Qs)
n_bad = [3] + [1] * 9
Gb = gradient(lambda th: log_amp(g_reg, chart(Up, th), n_bad))
control("(d) spins not proportional to the areas: U+ stationary", np.linalg.norm(Gb) < 1e-8,
        f"|grad| = {np.linalg.norm(Gb):.2f}")

# ---------------------------------------------------------------- 2. sign flips, gauge fixing
print("2. sign flips and the gauge X_4 = 1")
X = [quat(v / np.linalg.norm(v)) for v in rng.normal(size=(5, 4))]
X[4] = np.eye(2, dtype=complex)


def flips(n):
    F0 = amp(g_reg, X, n)
    return max(abs(amp(g_reg, [(-1) ** ((s >> a) & 1) * X[a] for a in range(4)] + [X[4]], n) - F0)
               for s in range(16))


check("F(eps U) = F(U) for the 16 sign patterns, even node sums", flips([3] * 10) < 1e-12)
control("(e) the same with an odd node sum (n_01 = 2, others 1)", flips([2] + [1] * 9) < 1e-12)
for mu in (1, 2):
    a5 = coh15j_full([mu] * 10, g_reg)
    a4 = coh15j_exact([mu] * 10, g_reg)
    check(f"mu = {mu}: integral over SU(2)^5 = integral with X_4 = 1", abs(a5 - a4) < 1e-14,
          f"{a5.real:.12f} vs {a4.real:.12f}")
Xq, Wq = haar_rule(8)
mom = [np.sum(Wq), np.sum(Wq * abs(Xq[:, 0, 0]) ** 2), np.sum(Wq * abs(Xq[:, 0, 0]) ** 4),
       abs(np.sum(Wq * Xq[:, 0, 0] ** 2))]
check("quadrature: total mass 1, E|alpha|^2 = 1/2, E|alpha|^4 = 1/3, E alpha^2 = 0",
      np.allclose(mom, [1, 1 / 2, 1 / 3, 0], atol=1e-14))

# ---------------------------------------------------------------- 3. the Hessian
print("3. the Hessian and det(-H)")
H1p, H1m = hess_amp(g_reg, Up, ONE), hess_amp(g_reg, Um, ONE)
L1p = hessian(lambda th: log_amp(g_reg, chart(Up, th), ONE))
check("H symmetric; F^-1 d^2 F = d^2 log F at U+", np.abs(H1p - H1p.T).max() < 1e-6 and
      np.abs(H1p - L1p).max() < 1e-6, f"{np.abs(H1p - L1p).max():.1e}")
H3p, H3m = hess_amp(g_reg, Up, [3] * 10), hess_amp(g_reg, Um, [3] * 10)
check("H(3 n) = 3 H(n)", np.abs(H3p - 3 * H1p).max() < 1e-5 and np.abs(H3m - 3 * H1m).max() < 1e-5)
for name, Hm in (("n = 3, U+", H3p), ("n = 3, U-", H3m), ("n = 1, U+", H1p), ("n = 1, U-", H1m)):
    d = np.linalg.det(-Hm)
    smin = np.linalg.svd(-Hm, compute_uv=False).min()
    emin = np.linalg.eigvalsh(-(Hm + Hm.conj().T).real / 2).min()
    check(f"det(-H) at {name}: Re(-H) positive definite, det far from 0", emin > 0.05 and smin > 0.05,
          f"det = {d.real:.6g}{d.imag:+.6g}i, |det| = {abs(d):.6g}, min singular value {smin:.4f}, "
          f"min eig Re(-H) {emin:.4f}")
H_RAND = []
for label, P in [(f"random {k}", p) for k, p in enumerate(P_RAND)]:
    _, Qr, gr, _ = regge_state(P)
    Ar = [area(P, *e) for e in EDGES]
    for name, U in zip(("U+", "U-"), crit_points(Qr)):
        Hm = hess_amp(gr, U, Ar)
        H_RAND.append((f"{label} {name}", Hm))
        emin = np.linalg.eigvalsh(-(Hm + Hm.conj().T).real / 2).min()
        check(f"[{label}] {name}: Re(-H) positive definite (spins = areas)", emin > 1e-3,
              f"min eig {emin:.4f}, |det| = {abs(np.linalg.det(-Hm)):.4g}")
M3 = (1 + 2j) * np.eye(3)
G3 = (1 + 2j) ** -0.5 * (1 + 2j) ** -0.5 * (1 + 2j) ** -0.5
check("invSqrtDet((1 + 2i) I_3) = (1 + 2i)^(-3/2), the factorised Gaussian value",
      abs(inv_sqrt_det(M3) - G3) < 1e-12, f"sum of arguments {arg_sum(M3):.4f} > pi")
control("(f) the principal root of det M for M = (1 + 2i) I_3", abs(principal_inv_sqrt_det(M3) - G3)
        < 1e-12, f"principal / invSqrtDet = {principal_inv_sqrt_det(M3) / inv_sqrt_det(M3):+.4f}")
for name, Hm in [("regular n = 1, U+", H1p), ("regular n = 1, U-", H1m), ("regular n = 3, U+", H3p),
                 ("regular n = 3, U-", H3m)] + H_RAND:
    s = arg_sum(-Hm)
    q = inv_sqrt_det(-Hm) / principal_inv_sqrt_det(-Hm)
    check(f"[{name}] invSqrtDet(-H) = principal root of det(-H)", abs(s) < np.pi and abs(q - 1) < 1e-9,
          f"sum of arguments {s:+.4f}")
rng_b = np.random.default_rng(11)
smax, agree = 0.0, 0
for k in range(60):
    P = [rng_b.normal(size=4) for _ in range(5)]
    P[4] = P[3] + [1.0, 0.3, 0.05][k % 3] * (P[4] - P[3])
    _, Qr, gr, _ = regge_state(P)
    Ar = [area(P, *e) for e in EDGES]
    for U in crit_points(Qr):
        M = -hess_amp(gr, U, Ar)
        smax = max(smax, abs(arg_sum(M)))
        agree += abs(inv_sqrt_det(M) / principal_inv_sqrt_det(M) - 1) < 1e-9
check("60 random simplices: invSqrtDet(-H) = principal root of det(-H) at all 120 critical points",
      agree == 120 and smax < np.pi, f"max |sum of arguments| {smax:.4f}")
Ap, Am = inv_sqrt_det(-H1p), inv_sqrt_det(-H1m)
check("A- = conj(A+) at the regular simplex (n = 1)", abs(Am - np.conj(Ap)) < 1e-5 * abs(Ap),
      f"A+ = {Ap:.6f}")

# ---------------------------------------------------------------- 4. the constant
print("4. the constant 2^4/(4 pi)^8 from the graph chart")
r = np.linspace(0, 1, 200001)[:-1]
r = (r[1:] + r[:-1]) / 2
mass = 2 * np.sum(4 * np.pi * r ** 2 / np.sqrt(1 - r ** 2)) / (len(r) + 1) / (2 * np.pi ** 2)
# the substitution r = sin s removes the endpoint singularity
s = (np.arange(100000) + 0.5) * (np.pi / 2) / 100000
mass2 = 2 * np.sum(4 * np.pi * np.sin(s) ** 2) * (np.pi / 2) / 100000 / (2 * np.pi ** 2)
check("graph-chart density 1/(2 pi^2 sqrt(1 - |v|^2)) has total mass 1 (two hemispheres)",
      abs(mass2 - 1) < 1e-9, f"mass {mass2:.12f} (midpoint in r: {mass:.4f})")
Hv = hess_amp(g_reg, Up, ONE, local=graph)
check("H_v = 4 H_theta", np.abs(Hv - 4 * H1p).max() < 1e-4, f"{np.abs(Hv - 4 * H1p).max():.1e}")
Cv = 2 ** 4 * (2 * np.pi ** 2) ** -4 * inv_sqrt_det(-Hv)
Ct = 2 ** 4 * (4 * np.pi) ** -8 * Ap
check("2^4 (2 pi^2)^-4 det(-H_v)^-1/2 = 2^4 (4 pi)^-8 det(-H_theta)^-1/2", abs(Cv / Ct - 1) < 1e-5,
      f"ratio {abs(Cv / Ct):.8f}")

# ---------------------------------------------------------------- 5. against the exact integral
print(f"5. the formula against the exact integral, mu = 1..{MU + 1}")
Phi1 = Th.sum() / 2
_, _, g_nophase, _ = regge_state(P_REG, phases=False)
exact = {mu: coh15j_exact([mu] * 10, g_reg) for mu in range(1, MU + 2)}
exact_np = {mu: coh15j_exact([mu] * 10, g_nophase) for mu in range(1, MU + 2)}
check("exact values are real", max(abs(v.imag) for v in exact.values()) <
      1e-12 * max(abs(v) for v in exact.values()))
ex2 = coh15j_exact([6] * 10, g_reg, extra=8)
ex3 = coh15j_exact([6] * 10, g_reg, extra=-12)
check("quadrature exactness: a finer rule gives the same value, a too coarse one does not (mu = 6)",
      abs(ex2 - exact[6]) < 1e-11 * abs(exact[6]) and abs(ex3 - exact[6]) > 1e-3 * abs(exact[6]),
      f"relative differences {abs(ex2 - exact[6]) / abs(exact[6]):.1e}, "
      f"{abs(ex3 - exact[6]) / abs(exact[6]):.1e}")


def fit(vals, const, A, mu0, w=6):
    """Least-squares fit of mu^6 coh15j(mu) = 2 Re(e^{i mu Phi} (a + b/mu)) on mu0..mu0+w-1;
    returns r = a / (const A), b / (const A) and the relative residual."""
    M, y = [], []
    for k in range(mu0, mu0 + w):
        c, s_ = 2 * np.cos(k * Phi1), -2 * np.sin(k * Phi1)
        M.append([c, s_, c / k, s_ / k])
        y.append(k ** 6 * vals[k].real)
    x, *_ = np.linalg.lstsq(np.array(M), np.array(y), rcond=None)
    res = np.linalg.norm(np.array(M) @ x - y) / np.linalg.norm(y)
    return complex(x[0], x[1]) / (const * A), complex(x[2], x[3]) / (const * A), res


LAST = MU - 4    # the last window is LAST..MU+1


def converges(vals, const, A):
    r8, r_last = fit(vals, const, A, 8)[0], fit(vals, const, A, LAST)[0]
    return abs(r_last - 1) < 0.03 and abs(r_last - 1) < abs(r8 - 1), r8, r_last


for mu in (1, 3, 6, 9, 12, 15, 18, MU + 1):
    print(f"   mu = {mu:2d}: mu^6 coh15j = {mu ** 6 * exact[mu].real:+.6f}, mu^6 leading term "
          f"{C15 * 2 * (np.exp(1j * mu * Phi1) * Ap).real:+.6f}")
for mu0 in (2, 4, 6, 8, 10, 12, LAST):
    r, b, res = fit(exact, C15, Ap, mu0)
    print(f"   window {mu0}..{mu0 + 5}: r = {r:.4f}, |r - 1| = {abs(r - 1):.4f}, b = {b:.3f}, "
          f"relative residual {res:.1e}")
ok, r8, rl = converges(exact, C15, Ap)
check("the leading coefficient of the exact integral is the formula's (|r - 1| < 0.03, decreasing)",
      ok, f"|r - 1| = {abs(r8 - 1):.4f} (window 8..13), {abs(rl - 1):.4f} (window {LAST}..{MU + 1})")
ok, r8, rl = converges(exact, C15 / 2 ** 4, Ap)
control("(a) the formula without the sign-flip count 2^4", ok, f"|r - 1| = {abs(rl - 1):.2f}")
ok, r8, rl = converges(exact, C15 * (4 * np.pi) ** 8 / (2 * np.pi ** 2) ** 4, Ap)
control("(b) graph-chart density with the theta-chart Hessian", ok, f"|r - 1| = {abs(rl - 1):.2f}")
ok, r8, rl = converges(exact_np, C15, Ap)
control("(c) the Regge state without the phases d(Theta)", ok, f"|r - 1| = {abs(rl - 1):.2f}")

# ---------------------------------------------------------------- 6. EPRL
print("6. the EPRL formula, gamma = 1/2, (n, m) = (3, 1)")
gam, n_s, m_s = 0.5, 3, 1
check("n - m = gamma (n + m)", n_s - m_s == gam * (n_s + m_s))
A3p, A3m = inv_sqrt_det(-H3p), inv_sqrt_det(-H3m)
S = (n_s + m_s) * Phi1
dev = 0
for lam in range(1, 400):
    l15 = [(2 * np.pi / lam) ** 6 * 2 ** 4 / (4 * np.pi) ** 8 *
           (np.exp(1j * lam * k * Phi1) * Bp + np.exp(-1j * lam * k * Phi1) * Bm)
           for k, Bp, Bm in ((n_s, A3p, A3m), (m_s, Ap, Am))]
    l4 = (2 * np.pi / lam) ** 12 * 2 ** 8 / (4 * np.pi) ** 16 * (
        np.exp(1j * lam * S) * A3p * Ap + np.exp(-1j * lam * S) * A3m * Am +
        np.exp(1j * lam * gam * S) * A3p * Am + np.exp(-1j * lam * gam * S) * A3m * Ap)
    scale = (2 * np.pi / lam) ** 12 * 2 ** 8 / (4 * np.pi) ** 16 * abs(A3p * Ap)
    dev = max(dev, abs(l4 - l15[0] * l15[1]) / scale)
check("four-term leading term = product of the two 15j leading terms", dev < 1e-10,
      f"max deviation {dev:.1e} relative to the size of one term")
for lam in (1, 2, 3, 4, 5, 6):
    ex = exact[3 * lam] * exact[lam]
    l4 = (2 * np.pi / lam) ** 12 * 2 ** 8 / (4 * np.pi) ** 16 * (
        np.exp(1j * lam * S) * A3p * Ap + np.exp(-1j * lam * S) * A3m * Am +
        np.exp(1j * lam * gam * S) * A3p * Am + np.exp(-1j * lam * gam * S) * A3m * Ap)
    print(f"   lam = {lam}: lam^12 eprlCoh = {lam ** 12 * ex.real:+.4e}, leading {lam ** 12 * l4.real:+.4e}")

# ---------------------------------------------------------------- 7. non-vacuity
print("7. the leading terms do not tend to 0")
lam = np.arange(1, 4001)
L15 = np.abs(C15 * (np.exp(1j * lam * n_s * Phi1) * A3p + np.exp(-1j * lam * n_s * Phi1) * A3m))
L4 = np.abs(C15 ** 2 * (np.exp(1j * lam * S) * A3p * Ap + np.exp(-1j * lam * S) * A3m * Am +
                        np.exp(1j * lam * gam * S) * A3p * Am + np.exp(-1j * lam * gam * S) * A3m * Ap))
for name, Lv in (("lam^6 |15j leading term|, n = 3", L15), ("lam^12 |EPRL leading term|", L4)):
    w = Lv.reshape(20, 200).max(axis=1)
    check(name + ": every window maximum >= half the overall maximum", w.min() >= 0.5 * Lv.max(),
          f"window maxima in [{w.min():.4g}, {w.max():.4g}]")

# ---------------------------------------------------------------- 8. gluing and stationarity
print("8. gluing, stationarity at gluing points, suppression without gluing")


def rand_su2(r):
    v = r.normal(size=4)
    return quat(v / np.linalg.norm(v))


def normal_sum(g, n, a):
    """Lean: sum_e n_e nodeNormal g a e."""
    s = np.zeros(3)
    for e, (p, q) in enumerate(EDGES):
        if p == a:
            s = s + n[e] * bloch(g[e][0])
        elif q == a:
            s = s + n[e] * bloch(g[e][1])
    return s


def rotated_sum(g, n, a, X):
    """Control (g): the normals of the frames X_a g_ab, X_b g_ba instead of g_ab, g_ba."""
    s = np.zeros(3)
    for e, (p, q) in enumerate(EDGES):
        if p == a:
            s = s + n[e] * bloch(X[p] @ g[e][0])
        elif q == a:
            s = s + n[e] * bloch(X[q] @ g[e][1])
    return s


def deriv_formula(F, sums):
    return np.array([F * 0.5j * sums[a][k] for a in range(4) for k in range(3)])


rng8 = np.random.default_rng(8)
dev_le, dev_sq = -np.inf, 0.0
for _ in range(2000):
    g = [(rand_su2(rng8), rand_su2(rng8)) for _ in range(10)]
    X = [rand_su2(rng8) for _ in range(5)]
    for e, (a, b) in enumerate(EDGES):
        p = prop(g, X, e)
        dev_le = max(dev_le, abs(p) - 1)
        dev_sq = max(dev_sq, abs(abs(p) ** 2 - (1 + bloch(X[a] @ g[e][0] @ EPS) @ bloch(X[b] @ g[e][1])) / 2))
check("2000 random points: |P_e| <= 1, |P_e|^2 = (1 + nu(X_a g_ab eps) . nu(X_b g_ba))/2",
      dev_le < 1e-12 and dev_sq < 1e-12, f"max |P| - 1 = {dev_le:.2e}, identity error {dev_sq:.1e}")

dev_d, gmin, dev_w, dev_u = 0.0, np.inf, np.inf, np.inf
dev_c, dev_cu = 0.0, np.inf
for _ in range(20):
    X = [rand_su2(rng8) for _ in range(5)]
    n = rng8.integers(1, 5, size=10)
    g = []
    for e, (a, b) in enumerate(EDGES):
        h = rand_su2(rng8)
        g.append((h, herm(X[b]) @ X[a] @ h @ EPS @ dmat(rng8.uniform(0, 4 * np.pi))))
    F = amp(g, X, n)
    grad = gradient(lambda th: amp(g, chart(X, th), n))
    dev_d = max(dev_d, abs(abs(F) - 1), np.abs(grad - deriv_formula(F, [normal_sum(g, n, a) for a in range(4)])).max())
    gmin = min(gmin, np.abs(grad).max())
    dev_w = min(dev_w, np.abs(grad - deriv_formula(F, [rotated_sum(g, n, a, X) for a in range(4)])).max())
    rot = [rotated_sum(g, n, a, X) for a in range(5)]
    dev_c = max(dev_c, np.abs(sum(rot)).max(),
                max(abs(np.linalg.norm(rot[a]) - np.linalg.norm(normal_sum(g, n, a))) for a in range(5)))
    gu = [(rand_su2(rng8), rand_su2(rng8)) for _ in range(10)]
    dev_cu = min(dev_cu, np.abs(sum(rotated_sum(gu, n, a, X) for a in range(5))).max())
    Fu = amp(gu, X, n)
    gradu = gradient(lambda th: amp(gu, chart(X, th), n))
    dev_u = min(dev_u, np.abs(gradu - deriv_formula(Fu, [normal_sum(gu, n, a) for a in range(4)])).max() / abs(Fu))
check("20 random gluing points: |F| = 1, grad F = F (i/2) (sum_e n_e nu_e)_k, gradient not small",
      dev_d < 1e-6 and gmin > 0.1, f"max error {dev_d:.1e}, smallest max |grad| {gmin:.3g}")
check("20 random gluing points: the rotated closure vectors add up to 0 over the five nodes, "
      "rotation keeps their lengths (closure at node 4 from closure at 0..3)", dev_c < 1e-12,
      f"max error {dev_c:.1e}")
control("(i) the rotated closure vectors at points that are not glued add up to 0", dev_cu < 1e-3,
        f"smallest max |sum| {dev_cu:.3g}")
control("(g) derivative formula with the rotated normals nu(X_a g_ab)", dev_w < 1e-3,
        f"smallest max error {dev_w:.3g}")
control("(h) derivative formula at points that are not glued (error / |F|)", dev_u < 1e-3,
        f"smallest relative error {dev_u:.3g}")

one = np.eye(2, dtype=complex)
X1 = [one] * 5
g_tw1 = [(one, one @ EPS)] * 10
g_tri = [(EPS if e == 1 else one, (EPS if e == 1 else one) @ EPS) for e in range(10)]
n_tri = [1, 1, 0, 0, 1, 0, 0, 0, 0, 0]
grad_tri = gradient(lambda th: amp(g_tri, chart(X1, th), n_tri))
grad_tw1 = gradient(lambda th: amp(g_tw1, chart(X1, th), [1] * 10))
F_un = amp([(one, one)] * 10, X1, [1] * 10)
check("twisted data at X = 1: F = 1, without eps F = 0; triangle 012 stationary, all spins 1 not",
      abs(amp(g_tri, X1, n_tri) - 1) < 1e-14 and abs(amp(g_tw1, X1, [1] * 10) - 1) < 1e-14 and
      abs(F_un) < 1e-14 and np.abs(grad_tri).max() < 1e-9 and np.abs(grad_tw1).max() > 1,
      f"max |grad| {np.abs(grad_tri).max():.1e} (triangle), {np.abs(grad_tw1).max():.4g} (all spins 1)")

g_one = [(one, one)] * 10
n_014 = [1, 0, 0, 1, 0, 0, 1, 0, 0, 0]
q_max = 3 * np.sqrt(3) / 8
vs = [np.array([np.sin(t), 0, np.cos(t)]) for t in (0, 2 * np.pi / 3, 4 * np.pi / 3)]
X120 = [lift(vs[0]), lift(vs[1]), one, one, lift(vs[2])]
F120 = abs(amp(g_one, X120, n_014))
F_samp = max(abs(amp(g_one, [rand_su2(rng8) for _ in range(5)], n_014)) for _ in range(20000))
check("g = 1, spins 1 on 014: |F| = 3 sqrt(3)/8 at 120 degrees, no sampled point above it",
      abs(F120 - q_max) < 1e-12 and F_samp <= q_max + 1e-12,
      f"|F| at 120 degrees {F120:.6f}, sampled max {F_samp:.6f}, 3 sqrt(3)/8 = {q_max:.6f}")


# ---------------------------------------------------------------- 9. the critical set of a Regge state
print("9. the critical set of the Regge state: two gauge classes")


def glue_res(g, X):
    """The gluing defects nu(X_a g_ab eps) - nu(X_b g_ba) of the ten edges (Lean: frameSrc, frameTgt)."""
    return np.concatenate([bloch(X[a] @ g[e][0] @ EPS) - bloch(X[b] @ g[e][1])
                           for e, (a, b) in enumerate(EDGES)])


def solve_glue(g, Y, iters=80, h=1e-7):
    """Levenberg-Marquardt on the 30 gluing equations in the chart Y_a exp((i/2) theta_a . sigma),
    a = 0..3, with X_4 = 1."""
    one = np.eye(2, dtype=complex)
    Y = list(Y)
    r = glue_res(g, Y + [one])
    lam = 1e-3
    for _ in range(iters):
        if np.linalg.norm(r) < 1e-14:
            break
        J = np.zeros((30, 12))
        for k in range(12):
            t = np.zeros(12)
            t[k] = h
            J[:, k] = (glue_res(g, chart(Y + [one], t)) - glue_res(g, chart(Y + [one], -t))) / (2 * h)
        # einsum, not matmul: the BLAS matmul of some numpy builds raises spurious warnings here
        step = -np.linalg.solve(np.einsum('ik,il->kl', J, J) + lam * np.eye(12), np.einsum('ik,i->k', J, r))
        Y2 = chart(Y + [one], step)[:4]
        r2 = glue_res(g, Y2 + [one])
        if np.linalg.norm(r2) < np.linalg.norm(r):
            Y, r, lam = Y2, r2, lam / 3
        else:
            lam *= 5
    return Y, np.linalg.norm(r)


def class_dist(X, U):
    """max_a min(|X_a - U_a|, |X_a + U_a|): distance from the class X_a = +-U_a (X_4 = 1)."""
    return max(min(np.abs(X[a] - U[a]).max(), np.abs(X[a] + U[a]).max()) for a in range(5))


def indep3(N):
    """The smallest singular value of [N_a, N_b, N_c] over all triples of distinct nodes."""
    return min(np.linalg.svd(np.array([N[a], N[b], N[c]]), compute_uv=False)[-1]
               for a in range(5) for b in range(a + 1, 5) for c in range(b + 1, 5))


rng9 = np.random.default_rng(9)
P_MORE = [[rng9.normal(size=4) for _ in range(5)] for _ in range(4)]
for label, P, starts in ([("regular", P_REG, 120)] +
                         [(f"random {k}", p, 40) for k, p in enumerate(P_RAND + P_MORE)]):
    N, Qs, g, Th = regge_state(P)
    A = [area(P, *e) for e in EDGES]
    Up, Um = crit_points(Qs)
    s3 = indep3(N)
    sep = class_dist(Up, Um)
    check(f"[{label}] any three normals independent, U+ and U- in different classes",
          s3 > 1e-3 and sep > 1e-3, f"smallest singular value {s3:.3g}, class distance {sep:.3g}")
    found = {"+": 0, "-": 0}
    other, worst = 0, 0.0
    for _ in range(starts):
        X, res = solve_glue(g, [rand_su2(rng9) for _ in range(4)])
        if res > 1e-10:
            continue
        X = X + [np.eye(2, dtype=complex)]
        dp, dm = class_dist(X, Up), class_dist(X, Um)
        if min(dp, dm) > 1e-6:
            other += 1
            continue
        found["+" if dp < dm else "-"] += 1
        worst = max(worst, abs(abs(amp(g, X, A)) - 1), min(dp, dm))
    check(f"[{label}] {starts} solver runs: every gluing point is +-U+ or +-U- node by node, "
          "both classes are found, |F| = 1 there",
          other == 0 and found["+"] > 0 and found["-"] > 0 and worst < 1e-6,
          f"class + {found['+']}, class - {found['-']}, other {other}, max error {worst:.1e}")

N, Qs, g_reg, Th = regge_state(P_REG)
Up, Um = crit_points(Qs)
A = [area(P_REG, *e) for e in EDGES]
X_mix = [Um[0]] + Up[1:]
X_cnj = [herm(u) for u in Up]
res_mix, res_cnj = np.linalg.norm(glue_res(g_reg, X_mix)), np.linalg.norm(glue_res(g_reg, X_cnj))
control("(j) the mixed point X_0 = U-_0, X_a = U+_a otherwise, is a gluing point with |F| = 1",
        res_mix < 1e-8 or abs(abs(amp(g_reg, X_mix, A)) - 1) < 1e-8,
        f"defect {res_mix:.3g}, |F| = {abs(amp(g_reg, X_mix, A)):.4f}")
control("(k) the wrong-order point X_a = (U+_a)^H is a gluing point with |F| = 1",
        res_cnj < 1e-8 or abs(abs(amp(g_reg, X_cnj, A)) - 1) < 1e-8,
        f"defect {res_cnj:.3g}, |F| = {abs(amp(g_reg, X_cnj, A)):.4f}")
P_flat = P_REG[:4] + [np.array([0.25, 0.25, 0.25, 0.25])]
N_flat = normals(P_flat)
control("(l) a degenerate simplex (vertex 4 in the hyperplane of 0123): any three normals "
        "independent", indep3(N_flat) > 1e-3, f"smallest singular value {indep3(N_flat):.1e}, "
        f"rank of the five normals {np.linalg.matrix_rank(np.array(N_flat), tol=1e-9)}")

print()
if failures or controls_passed:
    print("FAILED:", failures + [f"control passed: {c}" for c in controls_passed])
    sys.exit(1)
print("OK")
