"""Uniform bounds for 1/Gamma and Gamma from Stirling's formula (numerical evidence, not a proof).

Checks the statements of Lightlike/Asymptotics/GammaBounds.lean, with the Stirling exponent
f(w) = w log w - w (principal logarithm):

  (B1) ||1/Gamma(w + 1/2)|| <= exp(3/(4|w|) - Re f(w)) for all w with |w|^2 >= 2, on a polar
       grid in all four quadrants, including points next to the poles of Gamma(w + 1/2) on the
       negative axis (norm_inv_Gamma_half_add_le);
  (B2) ||Gamma(w + 1/2)|| <= sqrt(2 pi) exp(3/(4|w|) + Re f(w)) for Re w >= 0 and |w|^2 >= 2
       (norm_Gamma_half_add_le);
  (B3) Re f(-w) = -Re f(w) - pi |Im w| and Gamma(w + 1/2) Gamma(1/2 - w) = pi / cos(pi w) at
       random points (re_stirF_neg, Gamma_half_add_mul_Gamma_half_sub);
  (B4) on the disc |w| <= 2, the products ||1/Gamma(w + 1/2)|| exp(Re f(w)) and, for Re w >= 0,
       ||Gamma(w + 1/2)|| exp(-Re f(w)) are bounded, and |Re f(w)| <= 4 + 2 pi
       (exists_norm_inv_Gamma_half_add_le, exists_norm_Gamma_half_add_le, abs_re_stirF_le).

Controls (must FAIL):
  * the Gamma bound of (B2) on the left half-plane: next to the poles w = -1/2 - n the ratio of
    ||Gamma(w + 1/2)|| to the bound is unbounded, so the hypothesis Re w >= 0 is needed;
  * the reflection of the exponent without the term pi |Im w|.
Run: .venv/bin/python -I scripts/asymptotics/gamma_bounds_check.py   (expect "RESULT: OK")
"""
import random

from mpmath import mp, mpf, mpc, pi, log, exp, sqrt, cos, gamma, rgamma, re, im, arg, fabs

mp.dps = 30
random.seed(1)


def F(w):
    return w * log(w) - w


def ratio_inv(w):
    """||1/Gamma(w + 1/2)|| divided by its bound exp(3/(4|w|) - Re f(w))."""
    return fabs(rgamma(w + mpf(1) / 2)) / exp(mpf(3) / (4 * fabs(w)) - re(F(w)))


def ratio_gamma(w):
    """||Gamma(w + 1/2)|| divided by its bound sqrt(2 pi) exp(3/(4|w|) + Re f(w))."""
    return fabs(gamma(w + mpf(1) / 2)) / (sqrt(2 * pi) * exp(mpf(3) / (4 * fabs(w)) + re(F(w))))


def polar_grid(rmin, rmax, nr, nth, th0, th1):
    pts = []
    for i in range(nr):
        r = rmin * (rmax / rmin) ** (mpf(i) / (nr - 1))
        for k in range(nth):
            th = th0 + (th1 - th0) * mpf(k) / (nth - 1)
            pts.append(r * exp(mpc(0, 1) * th))
    return pts


def main():
    ok = True
    r0 = sqrt(2)
    pts = polar_grid(r0, mpf(40), 40, 73, -pi, pi)
    pts += [mpc(-mpf(n) - mpf(1) / 2 + d, e) for n in range(1, 30)
            for d in (mpf('-0.01'), mpf(0), mpf('0.01')) for e in (mpf(0), mpf('1e-6'), mpf('0.3'))]
    pts = [w for w in pts if fabs(w) ** 2 >= 2]
    worst = max(ratio_inv(w) for w in pts)
    b1 = worst <= 1
    print(f"(B1) ||1/Gamma(w+1/2)|| / exp(3/(4|w|) - Re f(w)) on {len(pts)} points with |w|^2 >= 2: "
          f"max {mp.nstr(worst, 6)}: {'OK' if b1 else 'FAIL'}")
    ok &= b1
    pts = polar_grid(r0, mpf(40), 40, 37, -pi / 2, pi / 2)
    worst = max(ratio_gamma(w) for w in pts)
    b2 = worst <= 1
    print(f"(B2) ||Gamma(w+1/2)|| / (sqrt(2 pi) exp(3/(4|w|) + Re f(w))) on {len(pts)} points with "
          f"Re w >= 0: max {mp.nstr(worst, 6)}: {'OK' if b2 else 'FAIL'}")
    ok &= b2
    dev_f, dev_r = mpf(0), mpf(0)
    for _ in range(200):
        w = mpc(random.uniform(-20, 20), random.uniform(-20, 20))
        dev_f = max(dev_f, fabs(re(F(-w)) - (-re(F(w)) - pi * fabs(im(w)))))
        lhs = gamma(w + mpf(1) / 2) * gamma(mpf(1) / 2 - w)
        dev_r = max(dev_r, fabs(lhs - pi / cos(pi * w)) / fabs(lhs))
    b3 = dev_f < mpf('1e-20') and dev_r < mpf('1e-20')
    print(f"(B3) Re f(-w) = -Re f(w) - pi|Im w|: max dev {mp.nstr(dev_f, 3)}; reflection formula: "
          f"max rel. dev {mp.nstr(dev_r, 3)}: {'OK' if b3 else 'FAIL'}")
    ok &= b3
    disc = [w for w in polar_grid(mpf('0.001'), mpf(2), 40, 73, -pi, pi)]
    m_inv = max(fabs(rgamma(w + mpf(1) / 2)) * exp(re(F(w))) for w in disc)
    m_gam = max(fabs(gamma(w + mpf(1) / 2)) * exp(-re(F(w))) for w in disc if re(w) >= 0)
    m_f = max(fabs(re(F(w))) for w in disc)
    b4 = m_f <= 4 + 2 * pi and m_inv < 100 and m_gam < 100
    print(f"(B4) on |w| <= 2: sup ||1/Gamma|| e^(Re f) = {mp.nstr(m_inv, 6)}, sup ||Gamma|| e^(-Re f) "
          f"(Re w >= 0) = {mp.nstr(m_gam, 6)}, sup |Re f| = {mp.nstr(m_f, 6)} <= 4 + 2 pi = "
          f"{mp.nstr(4 + 2 * pi, 6)}: {'OK' if b4 else 'FAIL'}")
    ok &= b4
    near = [mpc(-mpf(n) - mpf(1) / 2, mpf('1e-8')) for n in range(1, 6)]
    worst = max(ratio_gamma(w) for w in near)
    c1 = worst > 1
    print(f"control (Gamma bound at w = -1/2 - n + 1e-8 i, Re w < 0): max ratio "
          f"{mp.nstr(worst, 6)}: {'fails as it must' if c1 else 'UNEXPECTED PASS'}")
    ok &= c1
    w = mpc(3, 5)
    dev = fabs(re(F(-w)) + re(F(w)))
    c2 = dev > 1
    print(f"control (Re f(-w) = -Re f(w) without pi|Im w|, at w = 3 + 5i): deviation "
          f"{mp.nstr(dev, 6)} = pi |Im w|: {'fails as it must' if c2 else 'UNEXPECTED PASS'}")
    ok &= c2
    print("RESULT:", "OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
