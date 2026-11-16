"""Numerical check (not a proof) of the closed form of the node blocks H^{X_a X_a} of the Hessian of
the Lorentzian vertex action (Lightlike/Asymptotics/Lorentzian/Vertex.lean, lorAction) at the SU(2)
critical point of the regular Euclidean 4-simplex, against the 44 x 44 Hessian of
scripts/asymptotics/lorentzian_hessian_check.py (mpmath, finite differences of the action in the
chart X_a = X0_a exp((i/2) theta.sigma + (1/2) phi.sigma), which this script reuses without change).

The closed form (generators J = i sigma / 2 and K = sigma / 2, rotation alpha = theta, boost beta =
phi, k_e = n_e / 2, p_e = gamma k_e): the second derivative of the action along X_a exp(t(alpha J +
beta K)) with the other variables fixed is

  sum over the ends e at the node a of
    k_e [ -1/2 (alpha, alpha)_e + i s_e (alpha, beta)_e + s_e m_e . (alpha x beta)
          - (1/2 + i s_e gamma) (beta, beta)_e ],

with (u, v)_e = u.v - (m_e.u)(m_e.v), m_e = <xi, sigma xi> the unit vector of the spinor at the end
(xi_ab at a source end, xi_ba at a target end: the vectors of the closure sum_e k_e m_e = 0, BDFHP
eq. (25)) and s_e = +1 at a source end, -1 at a target end. BDFHP (61) (Appendix A, p. 33) is this
formula times 4 for source ends only (it corresponds to the generators i sigma and sigma, twice the
stated ones), with s_e = 1 and without the triple-product term; at a target end no variant of (61)
reproduces the second derivative (relative residuals 0.43, 0.48, 0.18 against 3e-6 for this formula,
measured in a node with two source and two target ends, SciPy). The blocks between two different
nodes vanish.

What is compared: the 24 x 24 block H^{XX} of the existing script against the four 6 x 6 node blocks
of the closed form; the printed number is the maximum entry difference divided by the maximum entry
of H^{XX}. The closure (sum_e k_e m_e = 0 at each node) of the spinors of the script is checked
first. Controls: the sign s_e dropped (all ends as source ends) and the triple-product term dropped
must each give a large difference.
Usage: python3 -I scripts/asymptotics/lorentzian_hessian_node_check.py     (about 3 min)
"""
import sys
import importlib.util
from pathlib import Path

from mpmath import mp, mpf, mpc, matrix

_spec = importlib.util.spec_from_file_location(
    "lorentzian_hessian_check", Path(__file__).with_name("lorentzian_hessian_check.py"))
hc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(hc)

I = mpc(0, 1)
EPS3 = {(0, 1, 2): 1, (1, 2, 0): 1, (2, 0, 1): 1, (0, 2, 1): -1, (2, 1, 0): -1, (1, 0, 2): -1}


def spin_vec(xi):
    """The unit vector <xi, sigma xi> of a unit spinor."""
    v = matrix([xi[0], xi[1]])
    return [(v.H * s * v)[0].real for s in hc.SIG]


def node_blocks(gamma, nd, signs=True, triple=True):
    """The closed-form 6 x 6 blocks (alpha = theta first, then beta = phi) for the nodes 0..3, and the
    node closure sums sum_e k_e m_e."""
    X0, xs, xt, k, p, w0 = hc.setup(gamma, nd)
    blocks, closures = [], []
    for a in range(4):
        H = matrix(6, 6)
        clo = [mpf(0)] * 3
        for e, (s_, t_) in enumerate(hc.EDGES):
            if a not in (s_, t_):
                continue
            src = (a == s_)
            m = spin_vec(xs[e] if src else xt[e])
            sg = (1 if src else -1) if signs else 1
            for c in range(3):
                clo[c] += k[e] * m[c]
            P = [[(1 if i == j else 0) - m[i] * m[j] for j in range(3)] for i in range(3)]
            C = [[sum(m[c] * EPS3.get((c, i, j), 0) for c in range(3)) for j in range(3)] for i in range(3)]
            for i in range(3):
                for j in range(3):
                    H[i, j] += -k[e] * P[i][j] / 2
                    H[3 + i, 3 + j] += -k[e] * (mpf(1) / 2 + I * sg * gamma) * P[i][j]
                    cr = k[e] * sg * (I * P[i][j] + (C[i][j] if triple else 0)) / 2
                    H[i, 3 + j] += cr
                    H[3 + j, i] += cr
        blocks.append(H)
        closures.append(clo)
    return blocks, closures


def main():
    mp.dps = 70
    ok = True
    for gam in (mpf("0.5"), mpf(4)):
        S0, g, H, w0 = hc.run(gam, [2] * 10)
        blocks, clo = node_blocks(gam, [2] * 10)
        cl = max(abs(x) for c in clo for x in c)
        hmax = max(abs(H[i, j]) for i in range(24) for j in range(24))
        offd = max([abs(H[i, j]) for i in range(24) for j in range(24) if i // 6 != j // 6] + [mpf(0)])

        def diff(bl):
            return max(abs(H[6 * a + i, 6 * a + j] - bl[a][i, j])
                       for a in range(4) for i in range(6) for j in range(6)) / hmax
        d = diff(blocks)
        d_nosign = diff(node_blocks(gam, [2] * 10, signs=False)[0])
        d_notrip = diff(node_blocks(gam, [2] * 10, triple=False)[0])
        good = d < mpf(10) ** (-12) and offd / hmax < mpf(10) ** (-12) and cl < mpf(10) ** (-12) \
            and d_nosign > mpf("0.05") and d_notrip > mpf("0.05")
        print(f"gamma={gam}: closure max|sum k m| = {mp.nstr(cl, 3)}, off-node blocks / max = "
              f"{mp.nstr(offd / hmax, 3)}, max|H^XX - closed form| / max|H^XX| = {mp.nstr(d, 4)}; "
              f"controls: no sign {mp.nstr(d_nosign, 4)}, no triple product {mp.nstr(d_notrip, 4)}: "
              f"{'ok' if good else 'FAIL'}", flush=True)
        ok = ok and good
    print("OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
