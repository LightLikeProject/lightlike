"""Numerical check (not a proof) of the building blocks of the gamma > 1 identification.

Doubled spins n = 2 j+, m = 2 j-, k = n - m, Y_low = the lowest Clebsch-Gordan component V_k -> V_n (x) V_m
(SymPy Clebsch-Gordan through scripts/spin4/vertex_check.cg_matrix, independent of the Lean construction).
Three exact checks, each with a printed design degree, and controls that must FAIL:

 0. leg amplitude: (<n,M| (x) <m,M'|) Y_low |k,g> = (-1)^m sqrt((k+1)/(n+1)) <M|g>^k <M|J M'>^m
    (control: the minus-sector point not J-conjugated; control: the sign (-1)^m dropped).
 1. edge resolution: <J u, v> = (n+1)(m+1) int dM dM' <J u|n,M;m,M'> <n,M;m,M'|v> on V_n (x) V_m, J = J_n (x) J_m
    (control: the Hermitian <u, v> in place of <J u, v>). Sphere integrals by the icosahedron (a 5-design).
 2. node: int_{Spin(4)} dG (x)_l [G Y_low |k, g_l>] = P_Spin4 Y_low^{(x)4} P_SU(2) (x)_l |k, g_l>, with the
    Haar integrals by the binary icosahedral group (an 11-design)  (control: the 8-element quaternion group, a
    3-design, too weak for n = 2 where the degree 4 n = 8 is needed).
The vertex-level identity follows from 0-2 by the resolution of identity and the contraction of the five
nodes (Lean); it is not evaluated here. Run from the repository root:
    .venv/bin/python -I scripts/spinfoam/eprl_high_check.py
"""
import sys, math, itertools
import numpy as np
sys.path.insert(0, "scripts/spin4")
import vertex_check as V

rng = np.random.default_rng(11)
fail = []
def check(name, ok):
    print(("ok   " if ok else "FAIL ") + name)
    if not ok: fail.append(name)
def control(name, still_passes):
    print(("ok   control fails as required: " if not still_passes else "FAIL control did not fail: ") + name)
    if still_passes: fail.append(name)

def cohvec(n, u):
    return np.array([math.sqrt(math.comb(n, i)) * u[0] ** (n - i) * u[1] ** i for i in range(n + 1)])
def spinor():
    v = rng.normal(size=2) + 1j * rng.normal(size=2); return v / np.linalg.norm(v)
def Jmap(u): return np.array([-np.conj(u[1]), np.conj(u[0])])
def su2_from_spinor(u):
    return np.array([[u[0], -np.conj(u[1])], [u[1], np.conj(u[0])]])
def D(n, g):
    """matrix with D cohvec(n,u) = cohvec(n, g u)"""
    a, b, c, d = g[0, 0], g[0, 1], g[1, 0], g[1, 1]
    M = np.zeros((n + 1, n + 1), dtype=complex)
    for i in range(n + 1):
        p = np.polynomial.polynomial.polypow(np.array([b, a]), n - i)   # (a u0 + b u1)^(n-i) in t = u1/u0 : coeffs of t^j: [b,a] means b + a t? use (a + b t)
        p = np.polynomial.polynomial.polymul(np.polynomial.polynomial.polypow(np.array([a, b]), n - i),
                                             np.polynomial.polynomial.polypow(np.array([c, d]), i))
        for j in range(n + 1):
            coef = p[j] if j < len(p) else 0
            M[i, j] = math.sqrt(math.comb(n, i) / math.comb(n, j)) * coef
    return M
def Jvec(n, w):   # antilinear structure map on V_n, J cohvec(n,u) = cohvec(n, J u)
    return np.array([(-1) ** (n - i) * np.conj(w[n - i]) for i in range(n + 1)])

# ---- group designs: binary tetrahedral (24, strength 5) and binary icosahedral (120, strength 11)
phi = (1 + 5 ** .5) / 2
def quat_group(icosahedral):
    qs = [np.array(s) / 2 for s in itertools.product([1, -1], repeat=4)]
    for i in range(4):
        for sg in (1, -1):
            e = np.zeros(4); e[i] = sg; qs.append(e)
    if icosahedral:
        base = [phi, 1, 1 / phi, 0]
        def parity(p): return sum(1 for i in range(4) for j in range(i + 1, 4) if p[i] > p[j]) % 2
        for p in itertools.permutations(range(4)):
            if parity(p) == 0:
                for sg in itertools.product([1, -1], repeat=3):
                    v = np.zeros(4); sgn = list(sg) + [1]
                    for idx, pos in enumerate(p):
                        v[pos] = base[idx] * (sgn[idx] if base[idx] != 0 else 1)
                    qs.append(v / 2)
    Q = np.unique(np.round(np.array(qs), 12), axis=0)
    assert len(Q) == (120 if icosahedral else 24)
    return [np.array([[q[0] + 1j * q[1], q[2] + 1j * q[3]], [-q[2] + 1j * q[3], q[0] - 1j * q[1]]]) for q in Q]
G24, G120 = quat_group(False), quat_group(True)
Q8 = [G for G in G24 if sorted(np.round(np.abs(G.reshape(-1)), 6).tolist()) in ([0, 0, 1, 1], )]   # +-1, +-i, +-j, +-k (a 3-design)
assert len(Q8) == 8
ico = []   # icosahedron vertices (a 5-design on S^2), as spinors
for s1 in (1, -1):
    for s2 in (1, -1):
        for v in ([0, s1, s2 * phi], [s1, s2 * phi, 0], [s2 * phi, 0, s1]):
            x = np.array(v, dtype=float); x /= np.linalg.norm(x)
            th, ph = math.acos(x[2]), math.atan2(x[1], x[0])
            ico.append(np.array([math.cos(th / 2), math.sin(th / 2) * np.exp(1j * ph)]))
assert len(ico) == 12
SPHERE_STRENGTH, G24_STRENGTH, G120_STRENGTH = 5, 5, 11

cases = [(2, 1), (3, 1), (3, 2), (4, 1), (4, 3)]
# ---- 0. leg amplitude
worst0 = 0; ctrl_J = []; ctrl_sign = []
for (n, m) in cases:
    k = n - m
    Y = np.array(V.cg_matrix(n, m, k).tolist(), dtype=complex)
    g0 = su2_from_spinor(spinor())
    assert np.allclose((np.kron(D(n, g0), D(m, g0))) @ Y, Y @ D(k, g0), atol=1e-12), "equivariance"
    c0 = (-1) ** m * math.sqrt((k + 1) / (n + 1))
    for _ in range(6):
        g, M, Mp = spinor(), spinor(), spinor()
        A = np.vdot(np.kron(cohvec(n, M), cohvec(m, Mp)), Y @ cohvec(k, g))
        form = np.vdot(M, g) ** k * np.vdot(M, Jmap(Mp)) ** m
        worst0 = max(worst0, abs(A - c0 * form) / max(abs(A), 1e-30))
        ctrl_J.append(abs(A - c0 * np.vdot(M, g) ** k * np.vdot(M, Mp) ** m) < 1e-9)
        ctrl_sign.append(abs(A - abs(c0) * form) < 1e-9)
check(f"0. leg amplitude c <M|g>^k <M|J M'>^m, max relative error {worst0:.1e}", worst0 < 1e-9)
control("0. minus-sector point not J-conjugated", all(ctrl_J))
control("0. sign (-1)^m dropped", all(ctrl_sign) and any(m % 2 for (_, m) in cases) and False or all(ctrl_sign))

# ---- 1. edge resolution
worst1 = 0; ctrl_h = []
for (n, m) in cases:
    need = max(n, m)
    assert need <= SPHERE_STRENGTH
    dim = (n + 1) * (m + 1)
    u = rng.normal(size=dim) + 1j * rng.normal(size=dim); v = rng.normal(size=dim) + 1j * rng.normal(size=dim)
    Ju = np.zeros(dim, dtype=complex)
    U = u.reshape(n + 1, m + 1)
    JU = np.array([[(-1) ** (n - i) * (-1) ** (m - j) * np.conj(U[n - i, m - j]) for j in range(m + 1)] for i in range(n + 1)])
    lhs = np.vdot(JU.reshape(-1), v)
    rhs = 0; rhs_h = 0
    for M in ico:
        for Mp in ico:
            w = np.kron(cohvec(n, M), cohvec(m, Mp))
            rhs += np.vdot(JU.reshape(-1), w) * np.vdot(w, v)
            rhs_h += np.vdot(u, w) * np.vdot(w, v)
    rhs *= dim / 144; rhs_h *= dim / 144
    worst1 = max(worst1, abs(lhs - rhs) / abs(lhs))
    ctrl_h.append(abs(np.vdot(u, v) - rhs_h) < 1e-9 and abs(lhs - np.vdot(u, v)) < 1e-9)
    print(f"     (n,m)=({n},{m}): sphere design degree {SPHERE_STRENGTH} >= integrand degree {need}")
check(f"1. edge resolution <Ju,v> = (n+1)(m+1) int int <Ju|M,M'><M,M'|v>, max relative error {worst1:.1e}", worst1 < 1e-9)
control("1. Hermitian form in place of <Ju,v>", all(ctrl_h))

# ---- 2. node
def proj_invariants(n_list, group):
    """average of the diagonal action on the tensor product of spins n_list"""
    dims = [x + 1 for x in n_list]; tot = np.prod(dims)
    P = np.zeros((tot, tot), dtype=complex)
    for g in group:
        Mx = np.array([[1]], dtype=complex)
        for x in n_list: Mx = np.kron(Mx, D(x, g))
        P += Mx
    return P / len(group)
worst2 = 0; ctrl2 = []
for (n, m) in [(2, 1)]:
    k = n - m
    Y = np.array(V.cg_matrix(n, m, k).tolist(), dtype=complex)
    gs = [su2_from_spinor(spinor()) for _ in range(4)]
    kets = [cohvec(k, g[:, 0]) for g in gs]
    # (b) integral over Spin(4) = SU(2) x SU(2) by 2I x 2I
    def integral(group):
        acc = np.zeros((n + 1) ** 4 * (m + 1) ** 4, dtype=complex)
        for Gp in group:
            Dn = D(n, Gp)
            for Gm in group:
                Dm = D(m, Gm)
                legs = [np.kron(Dn, Dm) @ (Y @ kk) for kk in kets]
                t = legs[0]
                for l in legs[1:]: t = np.kron(t, l)
                acc += t
        return acc / len(group) ** 2
    b = integral(G120)
    # (a) projector form: P_SU2 on (V_k)^4, then Y^4, then P_n (x) P_m after reordering
    vk = kets[0]
    for kk in kets[1:]: vk = np.kron(vk, kk)
    Pk = proj_invariants([k] * 4, G24)          # degree 4 k = 4 <= 5
    v1 = Pk @ vk
    Y4 = np.kron(np.kron(Y, Y), np.kron(Y, Y))
    v2 = (Y4 @ v1).reshape([n + 1, m + 1] * 4)
    perm = [0, 2, 4, 6, 1, 3, 5, 7]
    v3 = v2.transpose(perm).reshape((n + 1) ** 4, (m + 1) ** 4)
    Pn = proj_invariants([n] * 4, G120); Pm = proj_invariants([m] * 4, G120)   # degrees 4n = 8, 4m = 4 <= 11
    v4 = Pn @ v3 @ Pm.T
    a = v4.reshape([n + 1] * 4 + [m + 1] * 4).transpose([0, 4, 1, 5, 2, 6, 3, 7]).reshape(-1)
    worst2 = abs(a - b).max() / abs(b).max()
    print(f"     node (n,m)=({n},{m}): Spin(4) design: 2I x 2I, strength {G120_STRENGTH} >= degrees 4n = {4*n}, 4m = {4*m}; "
          f"SU(2) design: 24 elements, strength {G24_STRENGTH} >= 4k = {4*k}")
    check(f"2. node: integral over Spin(4) equals the projector form, max relative error {worst2:.1e}", worst2 < 1e-9)
    bw = integral(Q8)    # control: the quaternion group Q8 (strength 3 < 8 = 4 n)
    ctrl2.append(abs(a - bw).max() / abs(b).max() < 1e-9)
control("2. weak design (the 8-element quaternion group) for the Spin(4) integral", all(ctrl2))
print("OK" if not fail else "FAILED: " + "; ".join(fail))
sys.exit(1 if fail else 0)
