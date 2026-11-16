"""Numerical check (not a proof) of the node identity behind `eprlCohNode_eq` in
Lightlike/Asymptotics/EPRL/EprlCoherentNodeIdentity.lean.

For doubled leg spins n and m of one node and the same SU(2) elements g_l on both chiral halves it
checks, with the library's fusion coefficients `fusion` and all-outgoing 3j intertwiners `four_j`
of scripts/spin4/vertex_check.py (built independently of the Lean construction from SymPy's
Clebsch-Gordan and 9j symbols),

    sum_z c_z eprlNode(n, m, z)(mu, nu) = iota_n(g)(mu) * iota_m(g)(nu),   c_z = <iota(J; z), iota_J(g)>,

with J = n + m, iota_K(g) = P (tensor of coherent states) the Livine-Speziale intertwiner in the
projection basis kappa = K - 2k, and the Haar average computed by a Gauss-Legendre x uniform-grid
quadrature on SU(2) that is exact for the degree sum(K) of the integrand. Controls: a different g on
the anti-self-dual half must break the identity. Run from the repository root:
    .venv/bin/python -I scripts/spinfoam/eprl_node_check.py
"""
import sys, itertools, math
import numpy as np
sys.path.insert(0, "scripts/spin4")
import vertex_check as V

def su2(q):  # quaternion (a,b,c,d) -> [[a+ib, c+id],[-c+id, a-ib]]
    a, b, c, d = q
    return np.array([[a + 1j * b, c + 1j * d], [-c + 1j * d, a - 1j * b]])

def haar_nodes(deg):
    """Nodes and weights of a Haar-exact quadrature on SU(2) for polynomials of degree <= deg in the
    entries: alpha = sqrt(1-t) e^{i x}, beta = sqrt(t) e^{i y}, t in [0,1] with the uniform weight
    (Gauss-Legendre with N nodes, exact to degree 2N-1 in t, and entries of total degree deg give
    t-degree <= deg/2), x, y on uniform grids of M > deg points (exact for trigonometric degree
    < M)."""
    N = deg // 4 + 2
    M = deg + 2
    ts, ws = np.polynomial.legendre.leggauss(N)
    ts, ws = (ts + 1) / 2, ws / 2
    nodes, weights = [], []
    for t, w in zip(ts, ws):
        for i in range(M):
            for j in range(M):
                x, y = 2 * np.pi * i / M, 2 * np.pi * j / M
                al, be = np.sqrt(1 - t) * np.exp(1j * x), np.sqrt(t) * np.exp(1j * y)
                nodes.append(np.array([[al, be], [-np.conj(be), np.conj(al)]]))
                weights.append(w / (M * M))
    assert abs(sum(weights) - 1) < 1e-13
    return nodes, np.array(weights)

def cohvec(n, u):
    """components of the coherent state of spin n/2 with first column u, projection mu = n - 2k."""
    return np.array([math.sqrt(math.comb(n, k)) * u[0] ** (n - k) * u[1] ** k for k in range(n + 1)])

def iota_coh(Js, gs):
    G, W = haar_nodes(sum(Js))
    """projNode(cohInt J g)(kappa) as dict kappa -> value, kappa = J - 2k."""
    dims = [range(J + 1) for J in Js]
    T = {}
    for ks in itertools.product(*dims):
        tot = 0
        for X, w in zip(G, W):
            tot += w * np.prod([cohvec(Js[l], (X @ gs[l])[:, 0])[ks[l]] for l in range(4)])
        T[tuple(Js[l] - 2 * ks[l] for l in range(4))] = tot
    return T

rng = np.random.default_rng(1)
WRONG = False
def rand_su2():
    q = rng.normal(size=4); q /= np.linalg.norm(q); return su2(q)

def run(ns, ms, seed):
    gs = [rand_su2() for _ in range(4)]
    Js = tuple(a + b for a, b in zip(ns, ms))
    Tn, Tm, TJ = iota_coh(ns, gs), iota_coh(ms, gs if not WRONG else [rand_su2() for _ in range(4)]), iota_coh(Js, gs)
    zs = V.channel(*Js)
    xs, ys = V.channel(*ns), V.channel(*ms)
    kapJ = list(TJ)
    c = {}
    for z in zs:
        c[z] = sum(complex(V.four_j(Js, z, k)).conjugate() * TJ[k] for k in kapJ if sum(k) == 0)
    # check completeness: sum_z c_z iota_z = T_J
    err_c = max(abs(sum(c[z] * complex(V.four_j(Js, z, k)) for z in zs) - TJ[k]) for k in kapJ if sum(k) == 0)
    worst = 0; scale = 0
    for mu in Tn:
        for nu in Tm:
            if sum(mu) or sum(nu):
                continue
            lhs = 0
            for z in zs:
                for x in xs:
                    for y in ys:
                        f = complex(V.fusion(tuple(ns), tuple(ms), z, x, y))
                        lhs += c[z] * f * complex(V.four_j(ns, x, mu)) * complex(V.four_j(ms, y, nu))
            rhs = Tn[mu] * Tm[nu]
            worst = max(worst, abs(lhs - rhs)); scale = max(scale, abs(rhs))
    print(ns, ms, 'completeness err', err_c, 'node identity max|lhs-rhs|', worst, 'max|rhs|', scale)
    return worst < 1e-9 and scale > 1e-6

ok = run((1, 1, 1, 1), (1, 1, 1, 1), 1)
ok &= run((2, 2, 2, 2), (1, 1, 1, 1), 2)
ok &= run((1, 1, 2, 2), (1, 1, 1, 1), 3)
ok &= run((2, 1, 1, 2), (1, 1, 1, 1), 4)
WRONG = True
ctl = run((1, 1, 1, 1), (1, 1, 1, 1), 9)
print('control (different g on the anti-self-dual side) must FAIL:', 'fails as required' if not ctl else 'DID NOT FAIL')
ok &= not ctl
print('OK' if ok else 'MISMATCH')
sys.exit(0 if ok else 1)
