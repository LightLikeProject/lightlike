"""Numerical check (not a proof) of laplace_ray_uniform in
Lightlike/Oscillatory/LaplaceRay.lean, with mpmath quadrature at 30 digits.

The theorem: for continuous phi, g on [0, r] with
    |phi(t) + a t^2/2| <= M t^3,   Re phi(t) <= -c t^2,   |g(t) - g(0)| <= K t,   |g(0)| <= G,
and Re a >= alpha > 0, every N > 0 satisfies
    |int_0^r g(t) exp(N phi(t)) dt - g(0) (pi/(N a/2))^(1/2) / 2| <= C / N,
    C = K/(2c) + G M/(2 c'^2) + G/(alpha r),   c' = min(c, alpha/2),
with the principal square root (Lean: cpow with exponent 1/2).

Checks, on five instances (real and complex a, cubic and non-polynomial phase corrections,
constant and varying amplitudes):
 1. the hypotheses hold on a grid of [0, r] (sanity of the instance and its constants);
 2. N |I(N) - L(N)| <= C for N from 1/10 to 10^4 (the bound of the theorem);
 3. N (I(N) - L(N)) tends to the one-sided Laplace coefficient
        kappa = g1/a + 2 g0 phi3/a^2,   g = g0 + g1 t + ...,   phi = -a t^2/2 + phi3 t^3 + ...,
    from int_0^oo t e^(-b t^2) = 1/(2b) and int_0^oo t^3 e^(-b t^2) = 1/(2b^2), b = N a/2:
    |N (I - L) - kappa| is below 5% of max(1, |kappa|) at N = 10^4 and at most half its value at
    N = 10^3 (next order N^(-3/2)). This identifies the 1/N term, which the Lean theorem only
    bounds. In the last instance kappa = -1/4 + 4/16 = 0: the slope of g cancels the cubic phase
    term, and the error is O(N^(-3/2)).
Control, which must FAIL: the leading term g(0) (pi/(N a/2))^(1/2) of the full-line Gaussian
(the factor 1/2 of the half-line dropped, Lean: laplace_ray_gaussian_wrong_constant). Then
N |I - L| grows like sqrt(N) and exceeds C.
The script exits with code 0 only if every check passes and the control fails.

Usage: .venv/bin/python -I scripts/oscillatory/laplace_check.py
"""
import sys

import mpmath as mp

mp.mp.dps = 30

NS = [mp.mpf("0.1"), mp.mpf("0.5"), 1, 2, 5, 10, 30, 100, 300, 1000, 3000, 10000]


def instances():
    """(name, r, a, phi, g, alpha, M, c, K, G, g1, phi3), with g1 = g'(0), phi3 = phi'''(0)/6."""
    one = mp.mpf(1)
    a1 = mp.mpc(1, 0)
    yield ("Gaussian, g = 1", one, a1,
           lambda t: -t**2 / 2, lambda t: mp.mpf(1),
           one, 0, one / 2, 0, one, 0, 0)
    a2 = mp.mpc(1, 2)
    yield ("complex a = 1+2i, phi = -a t^2/2 + i t^3, g = 1 + t", one, a2,
           lambda t: -a2 * t**2 / 2 + 1j * t**3, lambda t: 1 + t,
           one, one, one / 2, one, one, 1, 1j)
    a3 = mp.mpc(2, -1)
    yield ("a = 2-i, phi = -a t^2/2 - t^3, g = exp(i t)", mp.mpf(2), a3,
           lambda t: -a3 * t**2 / 2 - t**3, lambda t: mp.expj(t),
           mp.mpf(2), one, one, one, one, 1j, -1)
    a4 = mp.mpc("0.5", 3)
    # |sin t - t + t^3/6| <= t^5/120 <= t^3/120 and |cos t - 1| <= t/2 on [0, 1]
    yield ("a = 0.5+3i, phi = -a t^2/2 + i (sin t - t + t^3/6) + t^3 (i - 1)/4, g = cos t", one, a4,
           lambda t: -a4 * t**2 / 2 + 1j * (mp.sin(t) - t + t**3 / 6) + t**3 * (1j - 1) / 4,
           lambda t: mp.cos(t),
           mp.mpf("0.5"), mp.mpf(1) / 120 + mp.sqrt(2) / 4, mp.mpf("0.25"), mp.mpf("0.5"), one,
           0, (1j - 1) / 4)
    a5 = mp.mpc(4, 0)
    yield ("a = 4, phi = -2 t^2 + t^3 on [0, 1] (real, damping weakens), g = 2 - t", one, a5,
           lambda t: -2 * t**2 + t**3, lambda t: 2 - t,
           mp.mpf(4), one, one, one, mp.mpf(2), -1, 1)


def constant(r, alpha, M, c, K, G):
    cp = min(c, alpha / 2)
    return K / (2 * c) + G * M / (2 * cp**2) + G / (alpha * r)


def hypotheses_hold(r, a, phi, g, alpha, M, c, K, G):
    if not a.real >= alpha:
        return False
    g0 = g(mp.mpf(0))
    if not abs(g0) <= G:
        return False
    for k in range(0, 401):
        t = r * k / 400
        tol = mp.mpf(10) ** -25
        if abs(phi(t) + a * t**2 / 2) > M * t**3 + tol:
            return False
        if mp.re(phi(t)) > -c * t**2 + tol:
            return False
        if abs(g(t) - g0) > K * t + tol:
            return False
    return True


def integral(r, phi, g, N):
    # split near the peak of width N^(-1/2) so that quadrature resolves it
    w = 1 / mp.sqrt(N)
    pts = sorted({mp.mpf(0), min(r, w), min(r, 4 * w), min(r, 16 * w), r})
    return mp.quad(lambda t: g(t) * mp.exp(N * phi(t)), pts)


def leading(a, g, N, half=True):
    val = g(mp.mpf(0)) * mp.sqrt(mp.pi / (N * a / 2))
    return val / 2 if half else val


def main():
    ok = True
    for name, r, a, phi, g, alpha, M, c, K, G, g1, phi3 in instances():
        C = constant(r, alpha, M, c, K, G)
        hyp = hypotheses_hold(r, a, phi, g, alpha, M, c, K, G)
        kappa = g1 / a + 2 * g(mp.mpf(0)) * phi3 / a**2
        scaled = []
        dev = []
        wrong = []
        for N in NS:
            N = mp.mpf(N)
            I = integral(r, phi, g, N)
            scaled.append(N * abs(I - leading(a, g, N)))
            dev.append(abs(N * (I - leading(a, g, N)) - kappa))
            wrong.append(N * abs(I - leading(a, g, N, half=False)))
        bound = all(s <= C for s in scaled)
        conv = dev[-1] <= mp.mpf("0.05") * max(1, abs(kappa)) and (
            dev[-1] <= dev[-3] / 2 or dev[-1] < mp.mpf(10) ** -15)
        control_fails = wrong[-1] > C and wrong[-1] > 5 * wrong[NS.index(100)]
        print(f"{name}\n  C = {mp.nstr(C, 6)}; hypotheses on grid: {hyp}")
        print("  N |I - L| at N = 1/10 .. 10^4: "
              + ", ".join(mp.nstr(s, 4) for s in scaled))
        print(f"  bound <= C: {bound}")
        print(f"  kappa = {mp.nstr(kappa, 5)}; |N (I - L) - kappa| at N = 10^3, 10^4:"
              f" {mp.nstr(dev[-3], 3)}, {mp.nstr(dev[-1], 3)}; matches: {conv}")
        print(f"  control (factor 1/2 dropped): N |I - L| = {mp.nstr(wrong[-1], 4)} at N = 10^4"
              f" > C, ratio N = 10^4 vs 10^2 is {mp.nstr(wrong[-1] / wrong[NS.index(100)], 4)} (sqrt(N) growth gives 10): {control_fails}")
        ok = ok and hyp and bound and conv and control_fails
    print("OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
