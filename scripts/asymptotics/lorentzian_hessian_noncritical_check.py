"""Numerical check (not a proof) that the closed forms of the blocks H^{Xz} (mixed) and H^{zz} of the Hessian of
the Lorentzian vertex action hold at NON-critical configurations, i.e. need no criticality.

Reference: second differences of the action itself (`lorentzian_hessian_check.action`: the sum over
edges of 2k log(ab/ref) - k log(nz nz') + i p log(nz'/nz), computed from X, w and the spinors, independent
of the closed form), in mpmath with 25 digits and step h = 1e-6:
  entry (i, j), i != j: (f(+h,+h) - f(+h,-h) - f(-h,+h) + f(-h,-h)) / (4 h^2)
  entry (i, i):         (f(+h) - 2 f(0) + f(-h)) / h^2
Error budget: truncation O(h^2) ~ 1e-12 (relative), roundoff 1e-25 / h^2 ~ 1e-13; the match must be
below 1e-9.
Configuration: the regular-simplex critical data with X_a -> X_a exp(M_a), M_a random traceless of size
0.3, w, xi, xi' all shifted by random complex numbers of size 0.3 (the gradient is then of order 1).
Controls (must fail with relative error above 1e-3): H^{Xz} with the conjugate part flipped, H^{Xz} with the
entries of edge 0 dropped, H^{zz} without the target terms c_B.
Usage: python3 -I scripts/asymptotics/lorentzian_hessian_noncritical_check.py
"""
import random
import sys
import importlib.util
from pathlib import Path

from mpmath import mp, mpf, mpc, matrix, expm

_spec = importlib.util.spec_from_file_location(
    "lorentzian_hessian_closed_form_check",
    Path(__file__).with_name("lorentzian_hessian_closed_form_check.py"))
cf = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cf)
hc = cf.hc
I = mpc(0, 1)
mp.dps = 25
H_STEP = mpf(10) ** (-6)
AMP = mpf("0.3")
SEED = 1


def main():
    orig = hc.setup
    rnd = random.Random(SEED)

    def r():
        return mpf(rnd.uniform(-1, 1)) * AMP

    X0, xs, xt, k, p, w0 = orig(mpf("0.5"), [2] * 10)
    X = []
    for a in range(5):
        M = matrix(2, 2)
        for i in range(3):
            M += (I * r() + r()) * hc.SIG[i] / 2
        X.append(X0[a] * expm(M))
    xs = [[x[0] + (r() + I * r()), x[1] + (r() + I * r())] for x in xs]
    xt = [[x[0] + (r() + I * r()), x[1] + (r() + I * r())] for x in xt]
    w0 = [w + (r() + I * r()) for w in w0]
    hc.setup = lambda gamma, nd: (X, xs, xt, k, p, w0)

    _, ref = hc.action(X, w0, xs, xt, k, p, None)

    def f(x):
        Xb, w = hc.build(x, X, w0)
        return hc.action(Xb, w, xs, xt, k, p, ref)[0]

    f0 = f([mpf(0)] * 44)

    def second_fd(i):
        h = H_STEP
        xp = [mpf(0)] * 44
        xp[i] = h
        xm = [mpf(0)] * 44
        xm[i] = -h
        return (f(xp) - 2 * f0 + f(xm)) / (h * h)

    def mixed_fd(i, j):
        if i == j:
            return second_fd(i)

        def pt(a, b):
            x = [mpf(0)] * 44
            x[i] = a
            x[j] = b
            return f(x)
        h = H_STEP
        return (pt(h, h) - pt(h, -h) - pt(-h, h) + pt(-h, -h)) / (4 * h * h)

    m = cf.mixed(mpf("0.5"))
    ent = {}
    for (node, e), rows in m.items():
        for gi, (hu, hv) in enumerate(rows):
            ent[(node, e, gi)] = (mixed_fd(6 * node + gi, 24 + 2 * e), mixed_fd(6 * node + gi, 25 + 2 * e),
                                  hu, hv)

    def cmp(tf):
        err = mpf(0)
        mx = mpf(0)
        for (node, e, gi), (fu, fv, hu, hv) in ent.items():
            hu, hv = tf(e, hu, hv)
            err = max(err, abs(fu - hu), abs(fv - hv))
            mx = max(mx, abs(fu), abs(fv))
        return err / mx

    def flip(e, hu, hv):
        dw = (hu + hv / I) / 2
        db = (hu - hv / I) / 2
        return dw - db, I * (dw + db)

    ok = cmp(lambda e, u, v: (u, v))
    c1 = cmp(flip)
    c2 = cmp(lambda e, u, v: (0, 0) if e == 0 else (u, v))
    def zz_err(drop_cB):
        err = mpf(0)
        mx = mpf(0)
        for e, bl in enumerate(cf.hzz(mpf("0.5"), drop_cB)):
            for i in range(2):
                for jj in range(2):
                    fd = mixed_fd(24 + 2 * e + i, 24 + 2 * e + jj)
                    err = max(err, abs(fd - bl[i, jj]))
                    mx = max(mx, abs(fd))
        return err / mx

    z_ok = zz_err(False)
    z_ctl = zz_err(True)
    print("H^Xz at a non-critical configuration: relative error of the closed form = %s" % mp.nstr(ok, 4))
    print("H^zz at a non-critical configuration: relative error of the closed form = %s" % mp.nstr(z_ok, 4))
    print("controls: H^Xz conjugate part flipped %s; H^Xz edge 0 dropped %s; H^zz without c_B %s"
          % (mp.nstr(c1, 4), mp.nstr(c2, 4), mp.nstr(z_ctl, 4)))
    tol = mpf(10) ** (-9)
    ctl = mpf(10) ** (-3)
    good = ok < tol and z_ok < tol and c1 > ctl and c2 > ctl and z_ctl > ctl
    print("OK" if good else "FAIL")
    sys.exit(0 if good else 1)


if __name__ == "__main__":
    main()
