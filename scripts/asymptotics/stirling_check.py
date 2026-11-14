"""Numerical check (not a proof) of the complex Stirling formula in midpoint form
(Lightlike/Asymptotics/Stirling.lean):

    Gamma(w + 1/2) = sqrt(2 pi) * exp(f(w) + mu(w))            (Gamma_half_add, w in the slit plane)
    f(w) = w log w - w,   D(w) = f(w+1) - f(w) - log(w + 1/2),   mu(w) = sum_{n>=0} D(w + n),

and of the two bounds proven there:

    |D(w)|  <= 3/8 / |w + 1/2|^2                    if |w + 1/2| >= 1          (norm_stirD_le)
    |mu(w)| <= 3/4 / ((1 - c) |w|)                  if Re w >= -c|w|, 0 <= c < 1,
                                                       |w|^2 >= 2/(1 - c)       (norm_stirMu_le)

mu is summed independently of Gamma: the first N terms directly, the tail sum_{n>=N} D(w+n) by
Euler-Maclaurin, with the closed-form integral -H(w+N), H(z) = G(z+1) - G(z) - (z+1/2) log(z+1/2) + z+1/2,
G(z) = z^2 log z / 2 - 3 z^2 / 4, and closed-form derivatives of D (mpmath's generic series
accelerators misextrapolate at some of these points).
Acceptance, at every test point w = r e^{i theta}:
  - relative error |sqrt(2 pi) exp(f + mu) / Gamma(w + 1/2) - 1| < 1e-30;
  - both bounds hold wherever their hypotheses hold (with the smallest admissible c).
Controls (must FAIL):
  - no midpoint shift, Gamma(w) in place of Gamma(w + 1/2): relative error > 1e-2 at every point;
  - no remainder, exp(f) in place of exp(f + mu): relative error > 1e-6 at every point;
  - constant 1/100 in place of 3/4 in the mu bound: violated at some point
    (so the proven bound is within a small factor of the truth, |mu| ~ 1/(24|w|)).
Run: .venv/bin/python -I scripts/asymptotics/stirling_check.py   (expect "RESULT: OK")
"""
from mpmath import mp, mpf, mpc, log, exp, gamma, sqrt, pi, cos, bernoulli, factorial

mp.dps = 60


def f(w):
    return w * log(w) - w


def D(w):
    return f(w + 1) - f(w) - log(w + mpf(1) / 2)


def H(z):
    """Minus the integral of D over [z, z + infinity): G(z+1) - G(z) - int log(z+1/2)."""
    G = lambda x: x ** 2 * log(x) / 2 - 3 * x ** 2 / 4
    h = z + mpf(1) / 2
    return G(z + 1) - G(z) - (h * log(h) - h)


def dD(z, m):
    """m-th derivative of D, m >= 1 odd, from F'' = 1/z and log' = 1/z."""
    Fm = lambda x: (-1) ** m * factorial(m - 2) / x ** (m - 1) if m >= 2 else log(x)
    return Fm(z + 1) - Fm(z) - (-1) ** (m - 1) * factorial(m - 1) / (z + mpf(1) / 2) ** m


def mu(w, K=12):
    N = 500 + int(2 * abs(w))
    head = sum(D(w + n) for n in range(N))
    z = w + N
    tail = -H(z) + D(z) / 2 - sum(bernoulli(2 * k) / factorial(2 * k) * dD(z, 2 * k - 1)
                                  for k in range(1, K + 1))
    return head + tail


def main():
    radii = [mpf("0.7"), mpf(2), mpf(5), mpf(20), mpf(100)]
    angles = [mpf(0), pi / 4, -pi / 4, pi / 2, -pi / 2, 3 * pi / 4, -3 * pi / 4,
              mpf("0.95") * pi, mpf("-0.95") * pi]
    ok = True
    worst_id, worst_ratio_D, worst_ratio_mu = mpf(0), mpf(0), mpf(0)
    min_shift, min_nomu = mpf(10), mpf(10)
    wrong_const_violated = False
    n_D, n_mu = 0, 0
    for r in radii:
        for th in angles:
            w = mpc(r * cos(th), r * mp.sin(th))
            m = mu(w)
            G = gamma(w + mpf(1) / 2)
            rhs = sqrt(2 * pi) * exp(f(w) + m)
            err = abs(rhs / G - 1)
            worst_id = max(worst_id, err)
            if err >= mpf("1e-30"):
                ok = False
                print(f"identity FAIL at w = {mp.nstr(w, 6)}: rel err {mp.nstr(err, 3)}")
            # controls
            e_shift = abs(rhs / gamma(w) - 1)
            e_nomu = abs(sqrt(2 * pi) * exp(f(w)) / G - 1)
            min_shift, min_nomu = min(min_shift, e_shift), min(min_nomu, e_nomu)
            # bound on D
            u = abs(w + mpf(1) / 2)
            if u >= 1:
                n_D += 1
                ratio = abs(D(w)) / (mpf(3) / 8 / u ** 2)
                worst_ratio_D = max(worst_ratio_D, ratio)
                if ratio > 1:
                    ok = False
                    print(f"D bound FAIL at w = {mp.nstr(w, 6)}")
            # bound on mu, smallest admissible c
            c = max(mpf(0), -cos(th)) + mpf("1e-40")
            if c < 1 and abs(w) ** 2 >= 2 / (1 - c):
                n_mu += 1
                bound = mpf(3) / 4 / ((1 - c) * abs(w))
                ratio = abs(m) / bound
                worst_ratio_mu = max(worst_ratio_mu, ratio)
                if ratio > 1:
                    ok = False
                    print(f"mu bound FAIL at w = {mp.nstr(w, 6)}")
                if abs(m) > mpf(1) / 100 / ((1 - c) * abs(w)):
                    wrong_const_violated = True
    print(f"identity: worst relative error {mp.nstr(worst_id, 3)} over {len(radii) * len(angles)} points")
    print(f"D bound: {n_D} points, max |D| / bound = {mp.nstr(worst_ratio_D, 4)}")
    print(f"mu bound: {n_mu} points, max |mu| / bound = {mp.nstr(worst_ratio_mu, 4)}")
    print(f"control Gamma(w): min relative error {mp.nstr(min_shift, 3)} (must be > 1e-2)")
    print(f"control no mu: min relative error {mp.nstr(min_nomu, 3)} (must be > 1e-6)")
    print(f"control constant 1/100: violated somewhere = {wrong_const_violated} (must be True)")
    if not (min_shift > mpf("1e-2") and min_nomu > mpf("1e-6") and wrong_const_violated):
        ok = False
    if n_D == 0 or n_mu == 0:
        ok = False
    print("RESULT: OK" if ok else "RESULT: FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
