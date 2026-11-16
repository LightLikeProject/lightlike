"""Numerical check (not a proof) of the structure of the real part of the Hessian of the Lorentzian vertex
action at the SU(2) critical point of the regular Euclidean 4-simplex (the closed-form 44 x 44 matrix of
`lorentzian_hessian_closed_form_check.py`, coordinates of `lorentzian_hessian_check.py`; the z-variables are
scaled by 1 + |w0|^2 as there). There is no random input: the configuration is the regular simplex.

Claims, each with tolerances, for gamma = 0.5, 1, 4 (mpmath, 30 digits):
 (a) Re(-H) is positive semidefinite: the smallest eigenvalue is above -1e-20;
 (b) its kernel N has dimension exactly 4 at mp.dps = 30: four eigenvalues of absolute value below 1e-20, the fifth above 1e-2;
 (c) N is the kernel of the linearised conditions Re S = 0: the 40 real functions Im, Re of
     (Z_ab wedge xi_ab) and (Z_ba wedge J xi_ba), each normalised (Z wedge xi = 0 iff Z is proportional to xi),
     have a 40 x 44 Jacobian (central differences, step 1e-10) of rank 40, and the kernel vectors of Re(-H) lie
     in its kernel to 1e-12;
 (d) -H restricted to N: Im(-H) is injective on N (smallest singular value of the 44 x 4 matrix Im(-H) N above 1e-3), and the 4 x 4 matrix of Im(-H) on an orthonormal basis of N has determinant above 1e-5
     (reference values 2.66e-4, 6.81e-4, 4.92e-2 at gamma = 0.5, 1, 4: the test is RELATIVE, |det / reference - 1| < 1e-3, and det > 1e-5) and condition number
     4.978 within 1e-3. Since Re(-H) is semidefinite, a vector of ker(-H) lies in N and is killed by Im(-H); so -H
     is invertible as soon as this 4 x 4 matrix is invertible (sufficient, not necessary: the exact condition is that
     Im(-H) is injective on N).
Along each vector of N, Re S(t v) - Re S(0) = -c t^4 with c > 0 (local exponent 4 within 0.05 between t = 0.01
and 0.001): the maximum is isolated, degenerate only to second order.
Controls (each must FAIL the claims): (i) a boundary spinor xi_01 rotated away from the critical alignment gives
a matrix that is not semidefinite with a 4-dimensional kernel; (ii) a random symmetric matrix in place of
Re(-H) (fixed seed 1) is not semidefinite with a 4-dimensional kernel.
Usage: python3 -I scripts/asymptotics/lorentzian_hessian_kernel_check.py
"""
import random
import sys
import importlib.util
from pathlib import Path

import mpmath
from mpmath import mp, mpf, mpc, matrix, conj

_spec = importlib.util.spec_from_file_location(
    "lorentzian_hessian_closed_form_check",
    Path(__file__).with_name("lorentzian_hessian_closed_form_check.py"))
cf = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cf)
hc = cf.hc
mp.dps = 30
I = mpc(0, 1)
REF = {"0.5": mpf("2.66e-4"), "1": mpf("6.81e-4"), "4": mpf("4.92e-2")}


def jm(v):
    return matrix([-conj(v[1]), conj(v[0])])


def analyse(H, w0):
    """Eigenvalues of Re(-H) (normalised), a basis of the kernel, the 4 x 4 Im block."""
    n = 44
    D = matrix(n, n)
    for i in range(24):
        D[i, i] = mpf(1)
    for e in range(10):
        s = 1 + abs(w0[e]) ** 2
        D[24 + 2 * e, 24 + 2 * e] = s
        D[25 + 2 * e, 25 + 2 * e] = s
    Hn = D.T * (-H) * D
    R = matrix(n, n)
    Im = matrix(n, n)
    for i in range(n):
        for j in range(n):
            R[i, j] = Hn[i, j].real
            Im[i, j] = Hn[i, j].imag
    R = (R + R.T) / 2
    Im = (Im + Im.T) / 2
    E, Q = mpmath.eigsy(R)
    idx = sorted(range(n), key=lambda i: E[i])
    ev = [E[i] for i in idx]
    Y = matrix(n, 4)
    for c in range(4):
        for r in range(n):
            Y[r, c] = Q[r, idx[c]]
    return ev, Y, Im, D


def structure_ok(ev):
    nz = sum(1 for x in ev if abs(x) < mpf(10) ** -20)
    return ev[0] > -mpf(10) ** -20 and nz == 4 and ev[4] > mpf("1e-2")


def main():
    print("mpmath %s, mp.dps = %d; thresholds: zero eigenvalue |l| < 1e-20, fifth eigenvalue > 1e-2" % (mpmath.__version__, mp.dps))
    ok_all = True
    for gs in ("0.5", "1", "4"):
        g = mpf(gs)
        H = cf.assemble(g)
        X0, xs, xt, k, p, w0 = cf.edge_data(g)
        ev, Y, Im, D = analyse(H, w0)
        a = ev[0] > -mpf(10) ** -20
        b = structure_ok(ev)
        M = Y.T * Im * Y
        det = mpmath.det(M)
        sv = sorted(mpmath.svd_r(M, compute_uv=False)[i] for i in range(4))
        cond = sv[-1] / sv[0]
        svI = sorted(mpmath.svd_r(Im * Y, compute_uv=False)[i] for i in range(4))
        inj = svI[0] > mpf("1e-3")
        d = inj and det > mpf("1e-5") and abs(det / REF[gs] - 1) < mpf("1e-3") and abs(cond - mpf("4.978")) < mpf("1e-3")

        # (c) the linearised conditions Re S = 0
        def eqs(x):
            Xb, w = hc.build(x, X0, w0)
            out = []
            for e, (a_, b_) in enumerate(hc.EDGES):
                z = matrix([w[e], 1])
                Z = Xb[a_].H * z
                Zp = Xb[b_].H * z
                xi = matrix(xs[e])
                Jx = jm(matrix(xt[e]))
                c1 = (Z[0] * xi[1] - Z[1] * xi[0]) / (mpmath.sqrt(abs(Z[0]) ** 2 + abs(Z[1]) ** 2)
                                                      * mpmath.sqrt(abs(xi[0]) ** 2 + abs(xi[1]) ** 2))
                c2 = (Zp[0] * Jx[1] - Zp[1] * Jx[0]) / (mpmath.sqrt(abs(Zp[0]) ** 2 + abs(Zp[1]) ** 2)
                                                        * mpmath.sqrt(abs(Jx[0]) ** 2 + abs(Jx[1]) ** 2))
                out += [c1.real, c1.imag, c2.real, c2.imag]
            return out
        h = mpf(10) ** -10
        Jc = matrix(40, 44)
        for i in range(44):
            xp = [mpf(0)] * 44
            xm = [mpf(0)] * 44
            xp[i] = h
            xm[i] = -h
            fp, fm = eqs(xp), eqs(xm)
            for r in range(40):
                Jc[r, i] = (fp[r] - fm[r]) / (2 * h)
        Jn = Jc * D
        G = Jn.T * Jn
        G = (G + G.T) / 2
        E2, Q2 = mpmath.eigsy(G)
        idx2 = sorted(range(44), key=lambda i: E2[i])
        rank40 = E2[idx2[4]] > mpf("1e-3") and abs(E2[idx2[3]]) < mpf(10) ** -20
        K = matrix(44, 4)
        for c in range(4):
            for r in range(44):
                K[r, c] = Q2[r, idx2[c]]
        P = K * K.T
        res = max(mpmath.norm(Y[:, c] - P * Y[:, c]) for c in range(4))
        c_ok = rank40 and res < mpf(10) ** -12

        # the quartic fall-off of Re S along the kernel (gamma = 0.5 only, as it is the slow part)
        quartic = True
        if gs == "0.5":
            S0 = hc.action(X0, w0, xs, xt, k, p, None)[0].real
            for c in range(4):
                v = [D[r, r] * Y[r, c] for r in range(44)]
                vals = []
                for t in (mpf("0.01"), mpf("0.001")):
                    Xb, w = hc.build([t * vv for vv in v], X0, w0)
                    vals.append(hc.action(Xb, w, xs, xt, k, p, None)[0].real - S0)
                expo = mpmath.log(abs(vals[0] / vals[1])) / mpmath.log(10)
                quartic = quartic and vals[0] < 0 and vals[1] < 0 and abs(expo - 4) < mpf("0.05")
        print("gamma %s: min eig Re(-H) %s, zero eigs %d, fifth %s; det M %s, cond %s, injectivity sigma_min(Im(-H) N) %s; ker in ker J: %s; quartic %s"
              % (gs, mp.nstr(ev[0], 3), sum(1 for x in ev if abs(x) < mpf(10) ** -20), mp.nstr(ev[4], 4),
                 mp.nstr(det, 5), mp.nstr(cond, 5), mp.nstr(svI[0], 4), mp.nstr(res, 3), quartic))
        ok_all = ok_all and a and b and c_ok and d and quartic

    # controls
    orig = hc.setup

    def mis(gamma, nd):
        X0, xs, xt, k, p, w0 = orig(gamma, nd)
        xs = [list(x) for x in xs]
        th = mpf("0.4")
        x0, x1 = xs[0]
        xs[0] = [mpmath.cos(th) * x0 - mpmath.sin(th) * x1, mpmath.sin(th) * x0 + mpmath.cos(th) * x1]
        return X0, xs, xt, k, p, w0

    hc.setup = mis
    Hm = cf.assemble(mpf("0.5"))
    hc.setup = orig
    X0, xs, xt, k, p, w0 = orig(mpf("0.5"), [2] * 10)
    evm, _, _, _ = analyse(Hm, w0)
    ctl1 = not structure_ok(evm)
    rnd = random.Random(1)
    A = matrix(44, 44)
    for i in range(44):
        for j in range(i + 1):
            A[i, j] = A[j, i] = mpf(rnd.uniform(-1, 1))
    evr = sorted(mpmath.eigsy(A, eigvals_only=True))
    ctl2 = not (evr[0] > -mpf(10) ** -20 and sum(1 for x in evr if abs(x) < mpf(10) ** -20) == 4)
    print("controls (must fail the claims): misaligned spinor fails %s, random symmetric matrix fails %s"
          % (ctl1, ctl2))
    good = ok_all and ctl1 and ctl2
    print("OK" if good else "FAIL")
    sys.exit(0 if good else 1)


if __name__ == "__main__":
    main()
