"""Numerical check (not a proof) of the Euclidean EPRL vertex amplitude in
Lightlike/Spin4/Vertex.lean and the values in Lightlike/Spin4/VertexTests.lean, built
independently of the Lean construction from SymPy's Clebsch-Gordan coefficients
(sympy.physics.quantum.cg.CG), 3j symbols (wigner_3j) and 9j symbols (wigner_9j), all exact.

Doubled spins and projections as in the library. The ten edges of K5 are ordered
01, 02, 03, 04, 12, 13, 14, 23, 24, 34; vertex a has legs to a+1, a+2, a+3, a+4 (mod 5), coupled as
(J1 J2) z (J3 J4); edge ab (a < b) carries the projection mu at a and -mu at b and the sign
(-1)^((j - mu)/2) (Lean: k5Legs, k5Spins, k5Contract4).

Route A, the definition (Lean: eprlVertex, eprlNode):
    A_v = sum_{mu, nu} prod_e eps(n_e, mu_e) eps(m_e, nu_e) prod_a N_a(mu, nu),
    N_a = sum_{x, y} f_a(z_a; x, y) iota(n; x)(mu) iota(m; y)(nu),
with the fusion coefficients f(z; x, y) = <i+_x (x) i-_y, (Y1 (x) Y2) i_z (Y3 (x) Y4)^H> computed
from matrices (Hom-form intertwiners i_z = C C^H / sqrt(z+1), Y the top Clebsch-Gordan component,
Fusion.lean) and the all-outgoing intertwiners
    iota(j; k)(m) = sqrt(k+1) sum_mu (-1)^((k-mu)/2) (j1 j2 k; m1 m2 mu)(k j3 j4; -mu m3 m4)
(Lightlike/Recoupling/Intertwiner.lean).
Route B, the 9j form (Lean: eprlVertex_eq_vertexNineJ, vertexNineJ):
    A_v = sum_{x, y} prod_a sqrt((x+1)(y+1)(z+1) prod_k (J_k+1)) {n1 n2 x; m1 m2 y; J1 J2 z}
          {n3 n4 x; m3 m4 y; J3 J4 z} * S(n; x) * S(m; y),
with J = n + m and the SU(2) 4-simplex contraction S (Lean: fifteenJSimplex) of the same 3j
intertwiners.

Checks:
 1. route A = route B on a set of configurations (EPRL labels for gamma = 1/3 and 1/2, and labels
    that are not EPRL labels of any gamma); the vertex is real (Lean: eprlVertex_im);
 2. exact values (Lean: VertexTests.lean): all spins 0 gives 1 (eprlVertex_zero); the 4-cycle
    0-3-1-4-0 with (n, m) = (1, 0), z = (0, 1, 0, 1, 0) gives 1/2, the SU(2) value of
    fifteenJSimplex_cycle (eprlVertex_zero_right); the 4-cycle with gamma = 1/3,
    (n, m) = (2, 1), J = 3, z = (0, 3, 0, 3, 0) gives 2/27;
 3. the selection rule: an odd sum of self-dual spins at a vertex gives 0
    (eprlVertex_eq_zero_of_not_even_left);
 4. the self-dual/anti-self-dual symmetry A_v(n, m) = A_v(m, n) holds numerically (not stated
    in Lean).
Controls, which must FAIL: the 9j form with the wrong simplicity spins J = |n - m| in place of
n + m (with the boundary labels z = J'), compared with the EPRL value of check 2 (Lean:
vertexNineJ_wrong_simplicity); route A with one edge sign dropped (the wrong pairing of the two ends
of an edge), compared with route B.
The script exits with code 0 only if every check passes and every control fails.

Usage: .venv/bin/python -I scripts/spin4/vertex_check.py
"""
import itertools
import sys
from functools import lru_cache

from sympy import Matrix, Rational, S, sqrt, nsimplify, simplify
from sympy.physics.quantum.cg import CG
from sympy.physics.wigner import wigner_3j, wigner_9j

failures = []
controls_passed = []

EDGES = [(a, b) for a in range(5) for b in range(a + 1, 5)]
EIDX = {e: k for k, e in enumerate(EDGES)}


def check(name, ok):
    print(("ok    " if ok else "FAIL  ") + name)
    if not ok:
        failures.append(name)


def control(name, ok):
    print(("control fails as required  " if not ok else "CONTROL PASSED (bad)  ") + name)
    if ok:
        controls_passed.append(name)


def tri(a, b, c):
    return (a + b + c) % 2 == 0 and c <= a + b and a <= b + c and b <= a + c


def channel(j1, j2, j3, j4):
    return [z for z in range(j1 + j2 + 1) if tri(j1, j2, z) and tri(j3, j4, z)]


def legs(a):
    """The edges at vertex a in the order a+1, a+2, a+3, a+4 (mod 5), with orientation +1 when
    the edge leaves a."""
    out = []
    for t in (1, 2, 3, 4):
        b = (a + t) % 5
        out.append((EIDX[(min(a, b), max(a, b))], 1 if a < b else -1))
    return out


# ---------------------------------------------------------------- intertwiners and fusion
@lru_cache(maxsize=None)
def cg_matrix(n1, n2, z):
    rows = []
    for a1 in range(n1 + 1):
        for a2 in range(n2 + 1):
            rows.append([CG(Rational(n1, 2), Rational(n1, 2) - a1, Rational(n2, 2),
                            Rational(n2, 2) - a2, Rational(z, 2), Rational(z, 2) - l).doit()
                         for l in range(z + 1)])
    return Matrix(rows)


def hom_ivec(j1, j2, j3, j4, z):
    return cg_matrix(j1, j2, z) * cg_matrix(j3, j4, z).H / sqrt(z + 1)


def kron(A, B):
    return Matrix(A.rows * B.rows, A.cols * B.cols,
                  lambda i, j: A[i // B.rows, j // B.cols] * B[i % B.rows, j % B.cols])


def eprl_pair(n1, m1, n2, m2):
    """(Y1 (x) Y2) with rows regrouped as ((a1, a2), (b1, b2)) (Lean: eprlPair)."""
    K = kron(cg_matrix(n1, m1, n1 + m1), cg_matrix(n2, m2, n2 + m2))
    out = Matrix.zeros(K.rows, K.cols)
    for a1, b1, a2, b2 in itertools.product(range(n1 + 1), range(m1 + 1), range(n2 + 1),
                                            range(m2 + 1)):
        src = ((a1 * (m1 + 1) + b1) * (n2 + 1) + a2) * (m2 + 1) + b2
        dst = (a1 * (n2 + 1) + a2) * ((m1 + 1) * (m2 + 1)) + b1 * (m2 + 1) + b2
        out[dst, :] = K[src, :]
    return out


@lru_cache(maxsize=None)
def fusion(ns, ms, z, x, y):
    """f(z; x, y) from its definition in Fusion.lean."""
    J = tuple(a + b for a, b in zip(ns, ms))
    lift = eprl_pair(ns[0], ms[0], ns[1], ms[1]) * hom_ivec(*J, z) * \
        eprl_pair(ns[2], ms[2], ns[3], ms[3]).H
    E = kron(hom_ivec(*ns, x), hom_ivec(*ms, y))
    return simplify(sum(E[i, j].conjugate() * lift[i, j]
                        for i in range(E.rows) for j in range(E.cols)))


@lru_cache(maxsize=None)
def three_j(j1, j2, j3, m1, m2, m3):
    h = lambda k: Rational(k, 2)
    if (j1 - m1) % 2 or (j2 - m2) % 2 or (j3 - m3) % 2:
        return S(0)
    try:
        return wigner_3j(h(j1), h(j2), h(j3), h(m1), h(m2), h(m3))
    except ValueError:
        return S(0)


@lru_cache(maxsize=None)
def four_j(js, k, ms):
    j1, j2, j3, j4 = js
    m1, m2, m3, m4 = ms
    tot = S(0)
    for mu in range(-k, k + 1):
        tot += (-1) ** ((k - mu) // 2) * three_j(j1, j2, k, m1, m2, mu) * \
            three_j(k, j3, j4, -mu, m3, m4)
    return sqrt(k + 1) * tot


@lru_cache(maxsize=None)
def nine_j(*js):
    h = lambda k: Rational(k, 2)
    try:
        return wigner_9j(*(h(j) for j in js))
    except ValueError:
        return S(0)


def eps(j, mu):
    return (-1) ** ((j - mu) // 2)


def projs(j):
    return list(range(-j, j + 1, 2))


# ---------------------------------------------------------------- the K5 contraction
def contract(states, sign, node):
    """sum over edge states s_e in states[e] of prod_e sign(e, s_e) * prod_a node(a, leg states),
    with the leg state of an incoming edge negated. A state is a tuple of projections."""
    order = [(a, legs(a)) for a in range(5)]
    tot = S(0)
    for ss in itertools.product(*states):
        val = S(1)
        for e in range(10):
            val *= sign(e, ss[e])
        for a, lg in order:
            ls = [tuple(o * c for c in ss[e]) for e, o in lg]
            if any(sum(l[i] for l in ls) != 0 for i in range(len(ls[0]))):
                val = S(0)
                break
            v = node(a, ls)
            if v == 0:
                val = S(0)
                break
            val *= v
        tot += val
    return tot


def spins_at(j, a):
    return tuple(j[e] for e, _ in legs(a))


def simplex(j, i):
    """The SU(2) 4-simplex contraction (Lean: fifteenJSimplex)."""
    states = [[(mu,) for mu in projs(j[e])] for e in range(10)]
    return contract(states, lambda e, s: eps(j[e], s[0]),
                    lambda a, ls: four_j(spins_at(j, a), i[a], tuple(l[0] for l in ls)))


def vertex_def(n, m, z, drop_sign=None):
    """Route A: the definition of eprlVertex."""
    states = [[(mu, nu) for mu in projs(n[e]) for nu in projs(m[e])] for e in range(10)]

    def sign(e, s):
        if e == drop_sign:
            return S(1)
        return eps(n[e], s[0]) * eps(m[e], s[1])

    def node(a, ls):
        ns, ms = spins_at(n, a), spins_at(m, a)
        mu = tuple(l[0] for l in ls)
        nu = tuple(l[1] for l in ls)
        return sum(fusion(ns, ms, z[a], x, y) * four_j(ns, x, mu) * four_j(ms, y, nu)
                   for x in channel(*ns) for y in channel(*ms))
    return contract(states, sign, node)


def fusion_nine_j(ns, ms, Js, z, x, y):
    return sqrt((x + 1) * (y + 1) * (z + 1) * (Js[0] + 1) * (Js[1] + 1) * (Js[2] + 1) *
                (Js[3] + 1)) * nine_j(ns[0], ns[1], x, ms[0], ms[1], y, Js[0], Js[1], z) * \
        nine_j(ns[2], ns[3], x, ms[2], ms[3], y, Js[2], Js[3], z)


def vertex_nine_j(n, m, J, z):
    """Route B: vertexNineJ."""
    chans = [[(x, y) for x in channel(*spins_at(n, a)) for y in channel(*spins_at(m, a))]
             for a in range(5)]
    tot = S(0)
    for P in itertools.product(*chans):
        w = S(1)
        for a in range(5):
            w *= fusion_nine_j(spins_at(n, a), spins_at(m, a), spins_at(J, a), z[a], *P[a])
        if w == 0:
            continue
        tot += w * simplex(n, [p[0] for p in P]) * simplex(m, [p[1] for p in P])
    return tot


def boundary_ok(J, z):
    return all(z[a] in channel(*spins_at(J, a)) for a in range(5))


def lab(d):
    """Edge labels from a dict {edge index: value}."""
    return tuple(d.get(e, 0) for e in range(10))


CYCLE = [2, 3, 5, 6]  # edges 03, 04, 13, 14: the 4-cycle 0-3-1-4-0
TRIANGLE = [0, 1, 4]  # edges 01, 02, 12

configs = []
# all spins 0
configs.append(("all spins 0", lab({}), lab({}), (0,) * 5))
# self-dual cycle (n, m) = (1, 0)
configs.append(("cycle (1,0)", lab({e: 1 for e in CYCLE}), lab({}), (0, 1, 0, 1, 0)))
# gamma = 1/3 cycle (n, m) = (2, 1), J = 3
configs.append(("cycle gamma=1/3 (2,1)", lab({e: 2 for e in CYCLE}), lab({e: 1 for e in CYCLE}),
                (0, 3, 0, 3, 0)))
# gamma = 1/2 cycle (n, m) = (3, 1), J = 4
configs.append(("cycle gamma=1/2 (3,1)", lab({e: 3 for e in CYCLE}), lab({e: 1 for e in CYCLE}),
                (0, 4, 0, 4, 0)))
# a triangle 0-1-2 (legs in positions that need z = J at vertices 1 and 2)
configs.append(("triangle (1,1)", lab({e: 1 for e in TRIANGLE}), lab({e: 1 for e in TRIANGLE}),
                tuple(z for z in (0, 0, 0, 0, 0))))
# not EPRL labels of one gamma: the complete graph on vertices 0-3, (2, 1) on the triangle
# 01, 02, 12 and (2, 0) on 03, 13, 23
K4 = [0, 1, 2, 4, 5, 7]
configs.append(("K4 mixed (2,1)/(2,0)", lab({e: 2 for e in K4}), lab({e: 1 for e in TRIANGLE}),
                (0,) * 5))
# all ten edges (1, 0) and (0, 1): the full 4-simplex
configs.append(("all edges (1,0)", (1,) * 10, (0,) * 10, (2, 0, 2, 0, 2)))
configs.append(("all edges (0,1)", (0,) * 10, (1,) * 10, (2, 0, 2, 0, 2)))

results = {}
for name, n, m, z in configs:
    J = tuple(a + b for a, b in zip(n, m))
    if not boundary_ok(J, z):
        # pick the first admissible boundary
        chans = [channel(*spins_at(J, a)) for a in range(5)]
        if any(c == [] for c in chans):
            print(f"skip  {name}: no admissible boundary")
            continue
        z = tuple(c[0] for c in chans)
    A = nsimplify(simplify(vertex_def(n, m, z)))
    B = nsimplify(simplify(vertex_nine_j(n, m, J, z)))
    results[name] = (n, m, z, A)
    check(f"{name}, z = {z}: definition {A} = 9j form {B}", simplify(A - B) == 0)
    check(f"{name}: real", A.is_real)
    Asym = nsimplify(simplify(vertex_def(m, n, z)))
    check(f"{name}: A(n, m) = A(m, n) = {Asym}", simplify(A - Asym) == 0)

check("K4 mixed labels: nonzero", results["K4 mixed (2,1)/(2,0)"][3] != 0)
check("value: all spins 0 gives 1", results["all spins 0"][3] == 1)
check("value: self-dual cycle (1, 0) gives 1/2 (fifteenJSimplex_cycle)",
      results["cycle (1,0)"][3] == Rational(1, 2))
check("self-dual cycle = SU(2) contraction S(n; z)",
      simplify(results["cycle (1,0)"][3] - simplex(lab({e: 1 for e in CYCLE}), (0, 1, 0, 1, 0)))
      == 0)
check("value: gamma = 1/3 cycle gives 2/27",
      results["cycle gamma=1/3 (2,1)"][3] == Rational(2, 27))

# selection rule: odd sum of self-dual spins at vertex 0 (only edge 01 has n = 1, m = 1 elsewhere)
n_odd = lab({0: 1, 1: 2, 4: 1})
m_odd = lab({0: 0, 1: 0, 4: 0})
check("selection rule: odd self-dual sum gives 0", simplify(vertex_def(n_odd, m_odd, (0,) * 5)) == 0)

# ---------------------------------------------------------------- controls
n3, m3, z3, A3 = results["cycle gamma=1/3 (2,1)"]
Jw = tuple(abs(a - b) for a, b in zip(n3, m3))
zw = (0, 1, 0, 1, 0)
Aw = nsimplify(simplify(vertex_nine_j(n3, m3, Jw, zw)))
print(f"      wrong simplicity J = |n - m|, z = {zw}: {Aw}")
check("wrong simplicity value is 1/54", Aw == Rational(1, 54))
control("9j form with J = |n - m| reproduces the EPRL value", simplify(Aw - A3) == 0)
n2, m2, z2, A2 = results["cycle gamma=1/2 (3,1)"]
A2d = nsimplify(simplify(vertex_def(n2, m2, z2, drop_sign=2)))
control("route A with the sign of edge 03 dropped equals route B", simplify(A2d - A2) == 0)

if failures or controls_passed:
    print(f"\nFAILED: {len(failures)} checks, {len(controls_passed)} controls passed")
    sys.exit(1)
print("\nall checks pass, all controls fail")
