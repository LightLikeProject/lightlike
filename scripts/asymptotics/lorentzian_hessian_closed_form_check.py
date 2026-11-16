"""Numerical check (not a proof) that the 44 x 44 Hessian of the Lorentzian vertex action at the SU(2)
critical point of the regular Euclidean 4-simplex is, in the chart of
scripts/asymptotics/lorentzian_hessian_check.py (X_a = X0_a exp((i/2) theta.sigma + (1/2) phi.sigma),
z_e = (w_e, 1), w_e = w0_e + u_e + i v_e), given by closed forms in the three blocks, and that the closed-form
matrix is nondegenerate.

With z = (w, 1), A = X0_a, B = X0_b, eta = A xi, theta = B J xi', M_A = A A^H, M_B = B B^H, q_A = z^H M_A z,
q_B = z^H M_B z, s1 = conj(w) eta_0 + eta_1 (= <Z, xi>), s2 = conj(theta_0) w + conj(theta_1)
(= <J xi', Z'>), c_A = k + i p, c_B = k - i p, the action of the edge is
    f = 2k log s1 + 2k log s2 - c_A log q_A - c_B log q_B     (k = n/2, p = gamma k).
 * H^zz (block diagonal over the edges, 2 x 2 in (u, v)): with the Wirtinger second derivatives
     f_ww = -2k (conj theta_0 / s2)^2 + c_A ((M_A00 conj w + M_A10)/q_A)^2 + c_B (...B...)^2,
     f_wbwb = -2k (eta_0 / s1)^2 + c_A ((M_A00 w + M_A01)/q_A)^2 + c_B (...B...)^2,
     f_wwb = -c_A (M_A00/q_A - |M_A00 w + M_A01|^2/q_A^2) - c_B (...B...),
   H_uu = f_ww + f_wbwb + 2 f_wwb, H_vv = -(f_ww + f_wbwb) + 2 f_wwb, H_uv = i (f_ww - f_wbwb).
 * H^Xz: the derivatives of f_w and f_wb along A -> A e^{sL} (L = (i/2) sigma_i, sigma_i/2) at the
   source end, B -> B e^{sL} at the target end (see `mixed` below); entry (L, u) = d_s f_w + d_s f_wb,
   (L, v) = i d_s f_w - i d_s f_wb.
 * H^XX: the node blocks of Lightlike/Asymptotics/Lorentzian/HessianNode.lean (`hessXX_block`).
Compared with the finite-difference Hessian of the existing script (mpmath, 70 digits, step 1e-9): the
printed number is max |H - closed form| / max |H|. The nondegeneracy margin is the smallest singular
value of -H in the Fubini-Study normalisation of the existing script (z-variables scaled by
1 + |w0|^2), also divided by the largest. Controls: dropping the c_B terms from H^zz, and dropping the
target sign of H^XX, are each detected.
Usage: python3 -I scripts/asymptotics/lorentzian_hessian_closed_form_check.py
"""
import sys
import importlib.util
from pathlib import Path

from mpmath import mp, mpf, mpc, matrix, conj, svd_c

_spec = importlib.util.spec_from_file_location(
    "lorentzian_hessian_check", Path(__file__).with_name("lorentzian_hessian_check.py"))
hc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(hc)
_spec2 = importlib.util.spec_from_file_location(
    "lorentzian_hessian_node_check", Path(__file__).with_name("lorentzian_hessian_node_check.py"))
nc = importlib.util.module_from_spec(_spec2)
_spec2.loader.exec_module(nc)

I = mpc(0, 1)


def jmap(v):
    return matrix([-conj(v[1]), conj(v[0])])


GEN = [(I / 2) * hc.SIG[i] for i in range(3)] + [hc.SIG[i] / 2 for i in range(3)]


def edge_data(gamma):
    X0, xs, xt, k, p, w0 = hc.setup(gamma, [2] * 10)
    return X0, xs, xt, k, p, w0


def hzz(gamma, drop_cB=False):
    X0, xs, xt, k, p, w0 = edge_data(gamma)
    blocks = []
    for e, (a, b) in enumerate(hc.EDGES):
        A, B, w = X0[a], X0[b], w0[e]
        xi, xip = matrix(xs[e]), matrix(xt[e])
        eta, theta = A * xi, B * jmap(xip)
        s1 = conj(w) * eta[0] + eta[1]
        s2 = conj(theta[0]) * w + conj(theta[1])
        MA, MB = A * A.H, B * B.H
        z = matrix([w, 1])
        qA = (z.H * MA * z)[0].real
        qB = (z.H * MB * z)[0].real
        cA, cB = k[e] + I * p[e], (0 if drop_cB else k[e] - I * p[e])
        fww = (-2 * k[e] * (conj(theta[0]) / s2) ** 2 + cA * ((MA[0, 0] * conj(w) + MA[1, 0]) / qA) ** 2
               + cB * ((MB[0, 0] * conj(w) + MB[1, 0]) / qB) ** 2)
        fbb = (-2 * k[e] * (eta[0] / s1) ** 2 + cA * ((MA[0, 0] * w + MA[0, 1]) / qA) ** 2
               + cB * ((MB[0, 0] * w + MB[0, 1]) / qB) ** 2)
        fwb = (-cA * (MA[0, 0] / qA - abs(MA[0, 0] * w + MA[0, 1]) ** 2 / qA ** 2)
               - cB * (MB[0, 0] / qB - abs(MB[0, 0] * w + MB[0, 1]) ** 2 / qB ** 2))
        huu, hvv, huv = fww + fbb + 2 * fwb, -(fww + fbb) + 2 * fwb, I * (fww - fbb)
        blocks.append(matrix([[huu, huv], [huv, hvv]]))
    return blocks


def mixed(gamma):
    X0, xs, xt, k, p, w0 = edge_data(gamma)
    out = {}
    for e, (a, b) in enumerate(hc.EDGES):
        A, B, w = X0[a], X0[b], w0[e]
        xi, xip = matrix(xs[e]), matrix(xt[e])
        eta, theta = A * xi, B * jmap(xip)
        s1 = conj(w) * eta[0] + eta[1]
        s2 = conj(theta[0]) * w + conj(theta[1])
        MA, MB = A * A.H, B * B.H
        z = matrix([w, 1])
        qA = (z.H * MA * z)[0].real
        qB = (z.H * MB * z)[0].real
        cA, cB = k[e] + I * p[e], k[e] - I * p[e]
        for node, src in ((a, True), (b, False)):
            if node >= 4:
                continue
            rows = []
            for L in GEN:
                if src:
                    N = A * (L + L.H) * A.H
                    ALxi = A * L * xi
                    s1d = conj(w) * ALxi[0] + ALxi[1]
                    qd = (z.H * N * z)[0].real
                    D = (N[0, 0] * conj(w) + N[1, 0]) / qA - (MA[0, 0] * conj(w) + MA[1, 0]) * qd / qA ** 2
                    dfw = -cA * D
                    dfb = 2 * k[e] * (ALxi[0] / s1 - eta[0] * s1d / s1 ** 2) - cA * conj(D)
                else:
                    N = B * (L + L.H) * B.H
                    thd = B * L * jmap(xip)
                    s2d = conj(thd[0]) * w + conj(thd[1])
                    qd = (z.H * N * z)[0].real
                    D = (N[0, 0] * conj(w) + N[1, 0]) / qB - (MB[0, 0] * conj(w) + MB[1, 0]) * qd / qB ** 2
                    dfw = 2 * k[e] * (conj(thd[0]) / s2 - conj(theta[0]) * s2d / s2 ** 2) - cB * D
                    dfb = -cB * conj(D)
                rows.append((dfw + dfb, I * dfw - I * dfb))
            out[(node, e)] = rows
    return out


def assemble(gamma, drop_cB=False, signs=True):
    Hc = matrix(44, 44)
    blocks, _ = nc.node_blocks(gamma, [2] * 10, signs=signs)
    for a in range(4):
        for i in range(6):
            for j in range(6):
                Hc[6 * a + i, 6 * a + j] = blocks[a][i, j]
    for e, bl in enumerate(hzz(gamma, drop_cB)):
        for i in range(2):
            for j in range(2):
                Hc[24 + 2 * e + i, 24 + 2 * e + j] = bl[i, j]
    for (node, e), rows in mixed(gamma).items():
        for gi, (hu, hv) in enumerate(rows):
            Hc[6 * node + gi, 24 + 2 * e] = hu
            Hc[6 * node + gi, 25 + 2 * e] = hv
            Hc[24 + 2 * e, 6 * node + gi] = hu
            Hc[25 + 2 * e, 6 * node + gi] = hv
    return Hc


def margin(H, w0):
    d = [mpf(1)] * 44
    for e in range(10):
        c = 1 + abs(w0[e]) ** 2
        d[24 + 2 * e] = c
        d[25 + 2 * e] = c
    Hn = matrix(44, 44)
    for i in range(44):
        for j in range(44):
            Hn[i, j] = d[i] * d[j] * H[i, j]
    mp.dps = 40
    sv = sorted(svd_c(-Hn, compute_uv=False)[i] for i in range(44))
    mp.dps = 70
    return sv[0], sv[-1]


def main():
    mp.dps = 70
    ok = True
    for gam in (mpf("0.5"), mpf(4)):
        S0, g, H, w0 = hc.run(gam, [2] * 10)
        hmax = max(abs(H[i, j]) for i in range(44) for j in range(44))

        def diff(Hc):
            return max(abs(H[i, j] - Hc[i, j]) for i in range(44) for j in range(44)) / hmax
        Hc = assemble(gam)
        d = diff(Hc)
        d_cb = diff(assemble(gam, drop_cB=True))
        d_sg = diff(assemble(gam, signs=False))
        lo, hi = margin(Hc, w0)
        good = d < mpf(10) ** (-12) and d_cb > mpf("0.01") and d_sg > mpf("0.01") and lo / hi > mpf("1e-3")
        print(f"gamma={gam}: max|H - closed form|/max|H| = {mp.nstr(d, 4)}; closed-form -H (Fubini-Study "
              f"normalised): smallest singular value {mp.nstr(lo, 6)}, largest {mp.nstr(hi, 6)}, "
              f"smallest/largest = {mp.nstr(lo / hi, 4)}; controls: no c_B {mp.nstr(d_cb, 3)}, "
              f"no target sign {mp.nstr(d_sg, 3)}: {'ok' if good else 'FAIL'}", flush=True)
        ok = ok and good
    print("OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
