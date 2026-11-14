"""Numerical check (not a proof) of the EPRL kinematics in Lightlike/Spin4/EPRL.lean,
Intertwiner4.lean and Fusion.lean, built independently of the Lean construction: from SymPy's
Clebsch-Gordan coefficients (sympy.physics.quantum.cg.CG, Condon-Shortley phases) and its 9j
symbols (sympy.physics.wigner.wigner_9j).

Doubled spins n = 2j as in the library; basis index a <-> magnetic number m = n/2 - a.
EPRL labels for 0 < gamma < 1: n = (1 + gamma) J / 2, m = (1 - gamma) J / 2.

Checks (CG and 9j coefficients exact in SymPy, matrix products in float64, tolerance 1e-12):
 1. the EPRL map Y (top Clebsch-Gordan component of j+ (x) j-) is an isometry with the closed
    form sqrt(C(n,a) C(m,b) / C(n+m,a+b)) (Lean: eprlMap_isometry, eprlMap_apply);
 2. weak simplicity: Y^H (K - gamma L) Y = 0 for E, F, H (Lean: eprl_weak_simplicity), and the
    master constraint Y^H M Y = (1 - gamma^2) j (Lean: eprl_master_constraint);
 3. the fusion coefficients f(z; x, y) = <i+_x (x) i-_y, (Y1 (x) Y2) i_z (Y3 (x) Y4)^H>, from the
    definition in Fusion.lean (Hom-form intertwiners i_z = C C^H / sqrt(z+1)), against the
    published formula of Alesci, Bianchi, Magliaro, Perini, "Asymptotics of LQG fusion
    coefficients", Class. Quantum Grav. 27 (2010) 095016, arXiv:0809.3718, eqs. (7)-(8):
        f_ABMP = (-1)^(j1-j2+j3-j4) sqrt((2i+1)(2iL+1)(2iR+1) prod_a (2j_a+1)) q(j1,j2) q(j3,j4),
        q(j1,j2) = {j1- iL j2-; j1+ iR j2+; j1 i j2}   (j- = |1-gamma| j/2, iL with the j-),
    in doubled units i = z/2, iR = x/2 (self-dual), iL = y/2. Expected: f = (-1)^(j1-j2+j3-j4)
    f_ABMP (their sign belongs to their orientation conventions; the 9j arrangement is a
    symmetry). Also the published properties of the monochromatic case j1 = j2 = j3 = j4
    (ABMP, below eq. (9)): f >= 0, and f = 0 when iL + iR + i is odd;
 4. sum_{x,y} f(z; x, y)^2 <= 1 (Lean: sum_normSq_fusion_le); f(0; 0, 0) = 2/3 for four links
    j = 3/2, gamma = 1/3 (Lean: fusion_third); the fusion matrix has full rank (injectivity) when
    sum n_a is even (Lean: eprlIntertwiner_injective), and the Spin(4) side is empty for
    gamma = 1/2, doubled spins (4, 4, 4, 8) (Lean: not_injective_without_parity).
 5. the bridge to the all-outgoing intertwiners (Lean: fourJ_eq_ivec):
    fourJ(J; z)(J1-2a1, J2-2a2, 2b3-J3, 2b4-J4) = (-1)^(J2+J4+a1+a2) i_z((a1,a2),(b3,b4)),
    with fourJ = sqrt(z+1) sum_mu (-1)^((z-mu)/2) (J1 J2 z; m1 m2 mu)(z J3 J4; -mu m3 m4)
    built from SymPy's 3j symbols (Lightlike/Recoupling/Intertwiner.lean).
 6. the recoupling coefficient lambda = tr(C_xyz^H W)/(z+1), W = (C_x (x) C_y)^H (Y1 (x) Y2) C_z
    (Fusion.lean), equals sqrt((x+1)(y+1)(J1+1)(J2+1)) {n1 n2 x; m1 m2 y; J1 J2 z}
    (Lean: eprlRecoupling_eq_nineJSym), for every admissible label set with n_a <= 3, m_a <= 2;
    the fusion coefficients of check 3 are then the product of two such 9j symbols
    (Lean: fusion_eq_nineJSym).
 7. the row/column form of the 9j symbol (Lean: Lightlike.Recoupling.nineJSym_eq_sum_threeJ, DLMF
    34.6.1): {9j} = sum_mu (row 3j symbols) (column 3j symbols), from SymPy's 3j symbols, against
    SymPy's wigner_9j.
Controls, which must FAIL: the 9j formula with x and y exchanged (checks 3 and 6), weak
simplicity for the Barrett-Crane labels n = m (check 2), the 9j formula of check 6 with the wrong
simplicity spins J_a = |n_a - m_a| in place of n_a + m_a, and the row/column form with the third
column's projections reversed (check 7). The script exits with code 0 only if every check passes
and every control fails.

Usage: .venv/bin/python -I scripts/spin4/eprl_check.py
"""
import itertools
import sys
from math import comb

import numpy as np
from sympy import Matrix, Rational, S, sqrt, N
from sympy.physics.quantum.cg import CG
from sympy.physics.wigner import wigner_3j, wigner_9j

DIGITS = 40
TOL = 1e-12
failures = []
controls_failed = []


def mm(*Ms):
    """Matrix product via einsum (numpy 2.0.2 on macOS raises spurious FP flags in complex
    matmul)."""
    out = Ms[0]
    for M in Ms[1:]:
        out = np.einsum("ij,jk->ik", out, M)
    return out


def num(x):
    return complex(N(x, DIGITS))


def cg_matrix(n1, n2, z):
    """C^{n1 n2}_z: rows (a1, a2) -> a1*(n2+1)+a2, columns l (state |z/2, z/2 - l>)."""
    rows = []
    for a1 in range(n1 + 1):
        for a2 in range(n2 + 1):
            row = []
            for l in range(z + 1):
                c = CG(Rational(n1, 2), Rational(n1, 2) - a1, Rational(n2, 2), Rational(n2, 2) - a2,
                       Rational(z, 2), Rational(z, 2) - l).doit()
                row.append(c)
            rows.append(row)
    return Matrix(rows)


def to_np(M):
    return np.array([[num(M[i, j]) for j in range(M.cols)] for i in range(M.rows)],
                    dtype=np.complex128)


def tri(a, b, c):
    return (a + b + c) % 2 == 0 and c <= a + b and a <= b + c and b <= a + c


def channel(j1, j2, j3, j4):
    return [z for z in range(j1 + j2 + 1) if tri(j1, j2, z) and tri(j3, j4, z)]


def check(name, ok):
    print(("ok    " if ok else "FAIL  ") + name)
    if not ok:
        failures.append(name)


def control(name, ok):
    print(("control fails as required  " if not ok else "CONTROL PASSED (bad)  ") + name)
    if ok:
        controls_failed.append(name)


# ---------------------------------------------------------------- 1. the EPRL map
def eprl_map(n, m):
    return cg_matrix(n, m, n + m)


for n, m in [(1, 1), (2, 1), (3, 1), (4, 2), (3, 2)]:
    Y = eprl_map(n, m)
    ok_iso = (Y.H * Y - Matrix.eye(n + m + 1)).applyfunc(lambda e: e.simplify()) == \
        Matrix.zeros(n + m + 1)
    ok_closed = True
    for a in range(n + 1):
        for b in range(m + 1):
            for c in range(n + m + 1):
                v = sqrt(Rational(comb(n, a) * comb(m, b), comb(n + m, c))) if a + b == c else 0
                if (Y[a * (m + 1) + b, c] - v).simplify() != 0:
                    ok_closed = False
    check(f"Y_({n},{m}) isometry", ok_iso)
    check(f"Y_({n},{m}) closed form", ok_closed)


# ---------------------------------------------------------------- 2. simplicity
def gens(n):
    """E, F, H of spin n/2 in the basis e_a: E e_{a+1} = sqrt((a+1)(n-a)) e_a, H e_a = (n-2a) e_a."""
    E = np.zeros((n + 1, n + 1))
    for a in range(n):
        E[a, a + 1] = np.sqrt((a + 1) * (n - a))
    H = np.diag([n - 2 * a for a in range(n + 1)]).astype(float)
    return E, E.T.copy(), H


def simplicity(n, m, gamma):
    """Max |Y^H (K - gamma L) Y| over E, F, H, and the master constraint scalar."""
    Y = to_np(eprl_map(n, m))
    En, Fn, Hn = gens(n)
    Em, Fm, Hm = gens(m)
    In, Im = np.eye(n + 1), np.eye(m + 1)
    S_ = {}
    for key, (Xn, Xm) in {"E": (En, Em), "F": (Fn, Fm), "H": (Hn, Hm)}.items():
        Jp, Jm = np.kron(Xn, Im), np.kron(In, Xm)
        S_[key] = (Jp - Jm) - gamma * (Jp + Jm)
    worst = max(np.abs(mm(Y.conj().T, S_[k], Y)).max() for k in S_)
    M = 0.5 * (mm(S_["E"], S_["F"]) + mm(S_["F"], S_["E"])) + 0.25 * mm(S_["H"], S_["H"])
    YMY = mm(Y.conj().T, M, Y)
    return worst, YMY


for gamma, J in [(Rational(1, 2), 4), (Rational(1, 3), 3), (Rational(1, 3), 6),
                 (Rational(1, 5), 5), (Rational(3, 5), 5)]:
    n, m = int((1 + gamma) * J / 2), int((1 - gamma) * J / 2)
    worst, YMY = simplicity(n, m, float(gamma))
    check(f"weak simplicity gamma={gamma} J={J} labels ({n},{m})", worst < 1e-12)
    target = float((1 - gamma ** 2) * J / 2)
    check(f"master constraint = (1-gamma^2) j = {target}",
          np.abs(YMY - target * np.eye(J + 1)).max() < 1e-12)
# control: Barrett-Crane labels n = m with gamma = 1/2
worst, _ = simplicity(2, 2, 0.5)
control("weak simplicity for Barrett-Crane labels (2,2), gamma = 1/2", worst < 1e-12)


# ---------------------------------------------------------------- 3. fusion coefficients
def hom_ivec(j1, j2, j3, j4, z):
    return mm(to_np(cg_matrix(j1, j2, z)), to_np(cg_matrix(j3, j4, z)).conj().T) / np.sqrt(z + 1)


def eprl_pair(n1, m1, n2, m2):
    """(Y1 (x) Y2) with rows regrouped as ((a1, a2), (b1, b2))."""
    Y1, Y2 = to_np(eprl_map(n1, m1)), to_np(eprl_map(n2, m2))
    K = np.kron(Y1, Y2)  # rows ((a1, b1), (a2, b2))
    out = np.zeros_like(K)
    for a1, b1, a2, b2 in itertools.product(range(n1 + 1), range(m1 + 1), range(n2 + 1),
                                            range(m2 + 1)):
        src = ((a1 * (m1 + 1) + b1) * (n2 + 1) + a2) * (m2 + 1) + b2
        dst = (a1 * (n2 + 1) + a2) * ((m1 + 1) * (m2 + 1)) + b1 * (m2 + 1) + b2
        out[dst] = K[src]
    return out


def fusion_table(ns, ms):
    n1, n2, n3, n4 = ns
    m1, m2, m3, m4 = ms
    J = [a + b for a, b in zip(ns, ms)]
    Y12, Y34 = eprl_pair(n1, m1, n2, m2), eprl_pair(n3, m3, n4, m4)
    table = {}
    for z in channel(*J):
        lift = mm(Y12, hom_ivec(*J, z), Y34.conj().T)
        for x in channel(n1, n2, n3, n4):
            for y in channel(m1, m2, m3, m4):
                E = np.kron(hom_ivec(n1, n2, n3, n4, x), hom_ivec(m1, m2, m3, m4, y))
                table[(z, x, y)] = np.sum(E.conj() * lift)
    return table


def fusion_9j(ns, ms, z, x, y, swap=False):
    J = [a + b for a, b in zip(ns, ms)]
    h = lambda k: Rational(k, 2)
    xx, yy = (y, x) if swap else (x, y)
    try:
        w12 = wigner_9j(h(ns[0]), h(ns[1]), h(xx), h(ms[0]), h(ms[1]), h(yy), h(J[0]), h(J[1]),
                        h(z))
        w34 = wigner_9j(h(ns[2]), h(ns[3]), h(xx), h(ms[2]), h(ms[3]), h(yy), h(J[2]), h(J[3]),
                        h(z))
    except ValueError:  # an inadmissible triad: the (wrong) formula is undefined
        return float("nan")
    pref = sqrt(S((x + 1) * (y + 1) * (z + 1) * (J[0] + 1) * (J[1] + 1) * (J[2] + 1) *
                  (J[3] + 1)))
    return num(pref * w12 * w34)


def fusion_abmp(ns, ms, z, x, y):
    """ABMP eqs. (7)-(8); iR = x/2 (self-dual labels n), iL = y/2 (anti-self-dual labels m)."""
    J = [a + b for a, b in zip(ns, ms)]
    h = lambda k: Rational(k, 2)
    try:
        q12 = wigner_9j(h(ms[0]), h(y), h(ms[1]), h(ns[0]), h(x), h(ns[1]), h(J[0]), h(z), h(J[1]))
        q34 = wigner_9j(h(ms[2]), h(y), h(ms[3]), h(ns[2]), h(x), h(ns[3]), h(J[2]), h(z), h(J[3]))
    except ValueError:
        return float("nan")
    sign = (-1) ** ((J[0] - J[1] + J[2] - J[3]) // 2)
    pref = sqrt(S((z + 1) * (y + 1) * (x + 1) * (J[0] + 1) * (J[1] + 1) * (J[2] + 1) *
                  (J[3] + 1)))
    return sign * num(pref * q12 * q34)


cases = [  # (gamma, doubled spins J)
    (Rational(1, 3), (3, 3, 3, 3)),
    (Rational(1, 2), (4, 4, 4, 4)),
    (Rational(1, 3), (3, 3, 6, 6)),
    (Rational(1, 3), (3, 6, 3, 6)),
    (Rational(1, 5), (5, 5, 5, 5)),
]
for gamma, J in cases:
    ns = tuple(int((1 + gamma) * j / 2) for j in J)
    ms = tuple(int((1 - gamma) * j / 2) for j in J)
    table = fusion_table(ns, ms)
    worst = max(abs(v - fusion_9j(ns, ms, *k)) for k, v in table.items())
    check(f"fusion = 9j formula, gamma={gamma}, J={J} ({len(table)} coefficients, "
          f"max dev {worst:.1e})", worst < TOL)
    sgn = (-1) ** ((J[0] - J[1] + J[2] - J[3]) // 2)
    worst_abmp = max(abs(v - sgn * fusion_abmp(ns, ms, *k)) for k, v in table.items())
    check(f"fusion = (-1)^(j1-j2+j3-j4) x ABMP eqs. (7)-(8), gamma={gamma}, J={J} "
          f"(max dev {worst_abmp:.1e})", worst_abmp < TOL)
    if len(set(J)) == 1:
        check(f"monochromatic J={J}: f >= 0 and f = 0 for (x+y+z)/2 odd (ABMP)",
              all(v.real > -TOL and abs(v.imag) < TOL for v in table.values()) and
              all(abs(v) < TOL for (z, x, y), v in table.items() if ((x + y + z) // 2) % 2 == 1))
    devs = [abs(v - fusion_9j(ns, ms, *k, swap=True)) for k, v in table.items()]
    control(f"9j formula with x <-> y, gamma={gamma}, J={J}",
            all(d == d and d < TOL for d in devs))
    # 4. Bessel, rank
    zs = channel(*J)
    pairs = sorted({(x, y) for (_, x, y) in table})
    bessel = max(sum(abs(table[(z, x, y)]) ** 2 for (x, y) in pairs) for z in zs)
    check(f"Bessel max_z sum |f|^2 = {bessel:.6f} <= 1", bessel <= 1 + 1e-12)
    F = np.array([[table[(z, x, y)] for z in zs] for (x, y) in pairs])
    even = sum(ns) % 2 == 0
    rank = np.linalg.matrix_rank(F, tol=1e-9) if pairs else 0
    check(f"rank of fusion matrix {rank} = dim {len(zs)} (sum n even: {even})",
          rank == len(zs) if even else True)
    if J == (3, 3, 3, 3):
        check("f(0; 0, 0) = 2/3 for j = 3/2, gamma = 1/3", abs(table[(0, 0, 0)] - 2 / 3) < TOL)

# the case excluded by Kaminski-Kisielowski-Lewandowski 2012: gamma = 1/2, J = (4, 4, 4, 8)
ns, ms = (3, 3, 3, 6), (1, 1, 1, 2)
check("gamma=1/2, J=(4,4,4,8): SU(2) channel {4, 6, 8}", channel(4, 4, 4, 8) == [4, 6, 8])
check("gamma=1/2, J=(4,4,4,8): no Spin(4) intertwiners (sum n = 15 odd)",
      channel(*ns) == [])

# ---------------------------------------------------------------- 5. bridge to fourJ
def three_j(j1, j2, j3, m1, m2, m3):
    h = lambda k: Rational(k, 2)
    try:
        return wigner_3j(h(j1), h(j2), h(j3), h(m1), h(m2), h(m3))
    except ValueError:
        return S(0)


def four_j(j1, j2, j3, j4, k, m1, m2, m3, m4):
    tot = S(0)
    for mu in range(-k, k + 1):
        tot += (-1) ** ((k - mu) // 2) * three_j(j1, j2, k, m1, m2, mu) * \
            three_j(k, j3, j4, -mu, m3, m4)
    return sqrt(k + 1) * tot


worst = 0.0
for J in [(1, 1, 1, 1), (2, 2, 2, 2), (1, 2, 1, 2), (2, 1, 3, 2), (3, 3, 2, 2)]:
    J1, J2, J3, J4 = J
    for z in channel(*J):
        iv = hom_ivec(*J, z)
        for a1, a2, b3, b4 in itertools.product(range(J1 + 1), range(J2 + 1), range(J3 + 1),
                                                range(J4 + 1)):
            lhs = num(four_j(J1, J2, J3, J4, z, J1 - 2 * a1, J2 - 2 * a2, 2 * b3 - J3, 2 * b4 - J4))
            rhs = (-1) ** (J2 + J4 + a1 + a2) * iv[a1 * (J2 + 1) + a2, b3 * (J4 + 1) + b4]
            worst = max(worst, abs(lhs - rhs))
check(f"fourJ = (-1)^(J2+J4+a1+a2) i_z with flipped incoming links (max dev {worst:.1e})",
      worst < TOL)


# ---------------------------------------------------------------- 6. lambda as a 9j symbol
def recoupling(n1, m1, n2, m2, x, y, z):
    J1, J2 = n1 + m1, n2 + m2
    Cx, Cy = to_np(cg_matrix(n1, n2, x)), to_np(cg_matrix(m1, m2, y))
    Cz, Cxyz = to_np(cg_matrix(J1, J2, z)), to_np(cg_matrix(x, y, z))
    W = mm(np.kron(Cx, Cy).conj().T, eprl_pair(n1, m1, n2, m2), Cz)
    return np.trace(mm(Cxyz.conj().T, W)) / (z + 1)


def nine_j(*js):
    h = lambda k: Rational(k, 2)
    try:
        return wigner_9j(*(h(j) for j in js))
    except ValueError:  # an inadmissible triad
        return S(0)


worst = worst_swap = worst_wrong = 0.0
cases = 0
for n1, m1, n2, m2 in itertools.product(range(4), range(3), range(4), range(3)):
    J1, J2 = n1 + m1, n2 + m2
    for x, y, z in itertools.product(range(n1 + n2 + 1), range(m1 + m2 + 1),
                                     range(J1 + J2 + 1)):
        if not (tri(n1, n2, x) and tri(m1, m2, y) and tri(J1, J2, z)):
            continue
        lam = recoupling(n1, m1, n2, m2, x, y, z)
        rhs = num(sqrt(S((x + 1) * (y + 1) * (J1 + 1) * (J2 + 1))) *
                  nine_j(n1, n2, x, m1, m2, y, J1, J2, z))
        worst = max(worst, abs(lam - rhs))
        swap = num(sqrt(S((x + 1) * (y + 1) * (J1 + 1) * (J2 + 1))) *
                   nine_j(n1, n2, y, m1, m2, x, J1, J2, z))
        worst_swap = max(worst_swap, abs(lam - swap))
        K1, K2 = abs(n1 - m1), abs(n2 - m2)
        wrong = num(sqrt(S((x + 1) * (y + 1) * (K1 + 1) * (K2 + 1))) *
                    nine_j(n1, n2, x, m1, m2, y, K1, K2, z))
        worst_wrong = max(worst_wrong, abs(lam - wrong))
        cases += 1
check(f"lambda = sqrt((x+1)(y+1)(J1+1)(J2+1)) {{n1 n2 x; m1 m2 y; J1 J2 z}} ({cases} label sets, "
      f"max dev {worst:.1e})", worst < TOL)
control("lambda 9j formula with x <-> y", worst_swap < TOL)
control("lambda 9j formula with the wrong simplicity spins |n - m|", worst_wrong < TOL)


# ---------------------------------------------------------------- 7. 9j row/column form
def nine_j_rows_columns(j, reverse=False):
    """sum over mu of (row 3j symbols)(column 3j symbols), DLMF 34.6.1 in doubled spins."""
    tot = S(0)
    ranges = [range(-j[i][k], j[i][k] + 1, 2) for i in range(3) for k in range(3)]
    for mus in itertools.product(*ranges):
        mu = [mus[0:3], mus[3:6], mus[6:9]]
        if any(sum(mu[i]) != 0 for i in range(3)):
            continue
        rows = three_j(*j[0], *mu[0]) * three_j(*j[1], *mu[1]) * three_j(*j[2], *mu[2])
        if rows == 0:
            continue
        s3 = -1 if reverse else 1
        cols = (three_j(j[0][0], j[1][0], j[2][0], mu[0][0], mu[1][0], mu[2][0]) *
                three_j(j[0][1], j[1][1], j[2][1], mu[0][1], mu[1][1], mu[2][1]) *
                three_j(j[0][2], j[1][2], j[2][2], s3 * mu[0][2], s3 * mu[1][2], s3 * mu[2][2]))
        tot += rows * cols
    return tot


# Doubled spins. {1 1 1; 1 1 1; 1 1 1} = 0 (odd column sum under exchange); (2,2,0),(1,1,0),(3,3,0)
# is the node j = 3/2, gamma = 1/3 of Lightlike/Spin4/EPRLTests.lean, {1 1 0; 1/2 1/2 0; 3/2 3/2 0}
# = sqrt(6)/12.
samples = [((1, 1, 2), (1, 1, 0), (2, 2, 2)), ((2, 1, 1), (1, 2, 3), (1, 3, 2)),
           ((2, 2, 2), (2, 2, 2), (2, 2, 2)), ((2, 2, 0), (1, 1, 0), (3, 3, 0)),
           ((3, 1, 2), (2, 2, 2), (1, 3, 2)), ((2, 1, 3), (2, 1, 1), (2, 2, 2)),
           ((4, 2, 2), (2, 2, 2), (2, 2, 0))]
worst = worst_rev = 0.0
for j in samples:
    ref = num(nine_j(*j[0], *j[1], *j[2]))
    worst = max(worst, abs(num(nine_j_rows_columns(j)) - ref))
    worst_rev = max(worst_rev, abs(num(nine_j_rows_columns(j, reverse=True)) - ref))
check(f"9j = sum_mu (rows)(columns) of 3j symbols, {len(samples)} spin sets "
      f"(max dev {worst:.1e})", worst < TOL)
control("9j row/column form with the third column's projections reversed", worst_rev < TOL)

print()
if failures:
    print(f"{len(failures)} check(s) FAILED: {failures}")
if controls_failed:
    print(f"{len(controls_failed)} control(s) passed but must fail: {controls_failed}")
sys.exit(1 if failures or controls_failed else 0)
