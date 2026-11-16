"""Numerical check (not a proof) of the nondegeneracy of the 44 x 44 Hessian of the Lorentzian vertex
action (Lightlike/Asymptotics/Lorentzian/Vertex.lean, lorAction, power form) at the SU(2) critical
point of the regular Euclidean 4-simplex (BDFHP, arXiv:0907.2440, Sec. 4 eq. (17), Sec. 5.4.3, Sec. 6.4
p. 30), built independently of the Lean files with mpmath (70 digits, finite differences with step
1e-9, so the entries are accurate to about 1e-18).

Variables: X_a = X0_a exp(M(theta_a, phi_a)) for a = 0..3 (X_4 = 1 gauge fixed; M = (i/2) theta.sigma
+ (1/2) phi.sigma), z_e = (w_e, 1), w_e = w0_e + u_e + i v_e: 24 + 20 = 44 real variables. X0_a = Q_4^H Q_a
(the critical point of the Euclidean theory), z_e proportional to X_a xi_src, xi_src = J g_ab e0,
xi_tgt = -J (g_ba e0), n_e = 2, p_e = gamma k_e. The chart variable of each edge is rescaled by
1 + |w0_e|^2 (an orthonormal frame of the Fubini-Study metric); without this rescaling two singular
values are about 2.5e-3 only because the edge 02 has |w0| = 5.4 (a chart artefact).
Checks: Re S = 0 and the gradient vanishes at the point (so the SU(2) critical point is a critical
point of the Lorentzian action), and the smallest singular value of -H is above 0.1 for gamma = 1/2
and 4 (values 0.2023 and 0.1558). Controls: a rotated point has a large gradient, and rotated target
spinors give Re S < 0.
Usage: python3 -I scripts/asymptotics/lorentzian_hessian_check.py     (about 90 s)
"""
import sys
import itertools
from mpmath import mp, mpf, mpc, matrix, sqrt, log, exp, expm, conj, pi, acos, svd_c, eye

mp.dps = 70
I = mpc(0, 1)
SX = matrix([[0, 1], [1, 0]]); SY = matrix([[0, -I], [I, 0]]); SZ = matrix([[1, 0], [0, -1]])
SIG = [SX, SY, SZ]
EPS = matrix([[0, -1], [1, 0]])
EDGES = [(a, b) for a in range(5) for b in range(a + 1, 5)]


def herm(M):
    return M.H


def quat(v):
    return matrix([[v[0] + I * v[1], v[2] + I * v[3]], [-v[2] + I * v[3], v[0] - I * v[1]]])


def lift(v):
    al = sqrt((1 + v[2]) / 2)
    be = (v[0] + I * v[1]) / (2 * al)
    return matrix([[al, -conj(be)], [be, al]])


def dmat(t):
    return matrix([[exp(I * t / 2), 0], [0, exp(-I * t / 2)]])


def det3(m):
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


def normal(P, a):
    o = [P[b] for b in range(5) if b != a]
    rows = [[o[i][c] - o[0][c] for c in range(4)] for i in (1, 2, 3)]
    n = []
    for k in range(4):
        minor = [[rows[r][c] for c in range(4) if c != k] for r in range(3)]
        n.append((-1) ** k * det3(minor))
    nrm = sqrt(sum(x * x for x in n))
    n = [x / nrm for x in n]
    if sum(n[c] * (P[a][c] - o[0][c]) for c in range(4)) > 0:
        n = [-x for x in n]
    return n


def regge_state(P):
    N = [normal(P, a) for a in range(5)]
    Qs = [quat(x) for x in N]
    g = []
    for (a, b) in EDGES:
        M = Qs[a] * herm(Qs[b])
        w = [M[0, 1].imag, M[0, 1].real, M[0, 0].imag]
        nw = sqrt(sum(x * x for x in w))
        m = lift([x / nw for x in w])
        t = acos(sum(N[a][c] * N[b][c] for c in range(4)))
        g.append((herm(Qs[a]) * m * dmat(t), herm(Qs[b]) * m * EPS))
    return Qs, g


def jmap(v):
    return [-conj(v[1]), conj(v[0])]


def vdot(a, b):
    return sum(conj(x) * y for x, y in zip(a, b))


T_REG = (1 - sqrt(5)) / 4
P_REG = [[mpf(1) if i == j else mpf(0) for j in range(4)] for i in range(4)] + [[T_REG] * 4]


def setup(gamma, nd):
    Qs, g = regge_state(P_REG)
    X0 = [herm(Qs[4]) * Qs[a] for a in range(5)]
    xs_l, xt_l, k, p, w0 = [], [], [], [], []
    e0 = matrix([1, 0])
    for e, (a, b) in enumerate(EDGES):
        v = g[e][0] * EPS * e0
        xs = [v[0], v[1]]
        u = g[e][1] * e0
        xt = [-x for x in jmap([u[0], u[1]])]
        xs_l.append(xs); xt_l.append(xt)
        k.append(mpf(nd[e]) / 2); p.append(mpf(gamma) * nd[e] / 2)
        z = X0[a] * matrix(xs)
        w0.append(z[0] / z[1])
    return X0, xs_l, xt_l, k, p, w0


def action(X, w, xs, xt, k, p, ref):
    S = mpc(0)
    ab_l = []
    for e, (a, b) in enumerate(EDGES):
        z = matrix([w[e], 1])
        Z = herm(X[a]) * z
        Zp = herm(X[b]) * z
        Zl, Zpl = [Z[0], Z[1]], [Zp[0], Zp[1]]
        ab = vdot(Zl, xs[e]) * vdot(jmap(xt[e]), Zpl)
        nz, nzp = vdot(Zl, Zl).real, vdot(Zpl, Zpl).real
        ab_l.append(ab)
        l = log(ab) if ref is None else log(ab / ref[e])
        S += 2 * k[e] * l - k[e] * log(nz * nzp) + I * p[e] * log(nzp / nz)
    return S, ab_l


def build(x, X0, w0):
    X = list(X0)
    for a in range(4):
        th, ph = x[6 * a:6 * a + 3], x[6 * a + 3:6 * a + 6]
        M = matrix(2, 2)
        for i in range(3):
            M += (I * th[i] / 2 + ph[i] / 2) * SIG[i]
        X[a] = X0[a] * expm(M)
    w = [w0[e] + x[24 + 2 * e] + I * x[25 + 2 * e] for e in range(10)]
    return X, w


def run(gamma, nd, h=mpf(10) ** (-9)):
    X0, xs, xt, k, p, w0 = setup(gamma, nd)
    _, ref = action(X0, w0, xs, xt, k, p, None)
    reS = sum((2 * k[e] * log(abs(ref[e])) for e in range(10)), mpf(0))
    # true Re S(crit) = Re S0 (with ref=None) :
    S0, _ = action(X0, w0, xs, xt, k, p, None)

    def f(x):
        X, w = build(x, X0, w0)
        return action(X, w, xs, xt, k, p, ref)[0]
    zero = [mpf(0)] * 44

    def sh(i, a, j=None, b=0):
        x = list(zero); x[i] = a
        if j is not None:
            x[j] = x[j] + b
        return x
    g = [(f(sh(i, h)) - f(sh(i, -h))) / (2 * h) for i in range(44)]
    f0 = f(zero)
    H = matrix(44, 44)
    for i in range(44):
        H[i, i] = (-f(sh(i, 2 * h)) + 16 * f(sh(i, h)) - 30 * f0 + 16 * f(sh(i, -h)) - f(sh(i, -2 * h))) / (12 * h * h)
        for j in range(i):
            v = (f(sh(i, h, j, h)) - f(sh(i, h, j, -h)) - f(sh(i, -h, j, h)) + f(sh(i, -h, j, -h))) / (4 * h * h)
            H[i, j] = v; H[j, i] = v
    return S0, g, H, w0


def main():
    """Checks (all must pass) and controls (all must be detected)."""
    ok = True
    for gam in (mpf("0.5"), mpf(4)):
        S0, g, H, w0 = run(gam, [2] * 10)
        d = [mpf(1)] * 44
        for e in range(10):
            c = 1 + abs(w0[e]) ** 2
            d[24 + 2 * e] = c; d[25 + 2 * e] = c
        Hn = matrix(44, 44)
        for i in range(44):
            for j in range(44):
                Hn[i, j] = d[i] * d[j] * H[i, j]
        mp.dps = 40
        sv = sorted(svd_c(-Hn, compute_uv=False)[i] for i in range(44))
        mp.dps = 70
        gmax = max(abs(x) for x in g)
        good = abs(S0.real) < mpf(10) ** (-60) and gmax < mpf(10) ** (-15) and sv[0] > mpf("0.1")
        print(f"gamma={gam}: Re S(crit) = {mp.nstr(S0.real, 3)}, max|grad| = {mp.nstr(gmax, 3)}, "
              f"smallest FS-normalised singular value of -H = {mp.nstr(sv[0], 12)} "
              f"(largest {mp.nstr(sv[-1], 6)}): {'ok' if good else 'FAIL'}", flush=True)
        ok = ok and good
    # controls: a rotated point is not critical; rotated target spinors lose Re S = 0
    X0, xs, xt, k, p, w0 = setup(mpf("0.5"), [2] * 10)
    R = expm(mpc(0, 0.3) * SX)
    X1 = [X0[a] * R if a < 4 else X0[a] for a in range(5)]
    _, ref1 = action(X1, w0, xs, xt, k, p, None)
    h = mpf(10) ** (-9)
    f1 = lambda x: action(*build(x, X1, w0), xs, xt, k, p, ref1)[0]
    zero = [mpf(0)] * 44
    gr = []
    for i in range(44):
        xp = list(zero); xp[i] = h
        xm = list(zero); xm[i] = -h
        gr.append(abs((f1(xp) - f1(xm)) / (2 * h)))
    c1 = max(gr) > mpf("0.01")
    print(f"control: a rotated point has max|grad| = {mp.nstr(max(gr), 4)}: {'detected' if c1 else 'NOT detected'}")
    xt_bad = [list((R * matrix(v)).T.tolist()[0]) if False else [ (R * matrix(v))[0], (R * matrix(v))[1] ] for v in xt]
    S2, _ = action(X0, w0, xs, xt_bad, k, p, None)
    c2 = S2.real < -mpf("0.01")
    print(f"control: rotated target spinors give Re S = {mp.nstr(S2.real, 4)} < 0: {'detected' if c2 else 'NOT detected'}")
    ok = ok and c1 and c2
    print("OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
