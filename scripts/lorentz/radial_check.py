"""Numerical cross-check of the radial formula for the Haar measure of SL(2,C) (milestone HA2).

Lean (Lightlike/Lorentz/Radial.lean, `lintegral_coshDist`): in the Bruhat chart
g = [[(1+bc)/d, b], [c, d]], with Haar measure |d|^-2 d^2b d^2c d^2d,

    int_G Phi(coshDist g) dg = 4 pi^3 int_1^oo Phi(t) sqrt(t^2 - 1) dt,
    coshDist g = (|g00|^2 + |g01|^2 + |g10|^2 + |g11|^2) / 2.

For Phi(t) = exp(-a t) the right side is 4 pi^3 K1(a) / a.

This script evaluates the left side directly in the chart, by a route that differs from the Lean
proof (which completes the square in c):
  * polar coordinates b = beta e^{i th_b}, c = gamma e^{i th_c}, d = delta e^{i th_d}; then
    |1 + bc|^2 = 1 + 2 beta gamma cos(th_b + th_c) + beta^2 gamma^2, so the integrand depends on
    the phases only through phi = th_b + th_c, and the th_d-integral is 2 pi;
  * the phi-integral is a Bessel function, int_0^{2 pi} exp(-A cos phi) dphi = 2 pi I0(A);
  * with u = beta gamma at fixed beta, the beta-integral is another Bessel function,
    int_0^oo exp(-a (beta^2 + u^2/beta^2)/2) dbeta/beta = K0(a u);
  * the remaining integral over (u, delta) is done by adaptive quadrature.
The reduction steps are themselves checked numerically at sample points.

Control (wrong input): the flat chart measure d^2b d^2c d^2d, without |d|^-2, gives a different
number. This is numerical evidence, not proof.

Run: .venv/bin/python -I scripts/lorentz/radial_check.py   (needs numpy and scipy)
"""
import math
import sys

import numpy as np
from scipy import integrate, special

TOL = 1e-7


def chart_integrand(b, c, d, a, density_power):
    """exp(-a coshDist(bruhat(b, c, d))) |d|^density_power, for complex b, c and d != 0."""
    g00 = (1 + b * c) / d
    cosh_dist = (abs(g00) ** 2 + abs(b) ** 2 + abs(c) ** 2 + abs(d) ** 2) / 2
    return math.exp(-a * cosh_dist) * abs(d) ** density_power


def check_phase_reduction(a):
    """The phase integral of the chart integrand at fixed moduli equals (2 pi)^2 * 2 pi * reduced."""
    beta, gamma, delta = 0.7, 1.3, 0.9
    def f(tb, tc, td):
        b = beta * np.exp(1j * tb)
        c = gamma * np.exp(1j * tc)
        d = delta * np.exp(1j * td)
        return chart_integrand(b, c, d, a, 0)
    # the integrand does not depend on th_d; integrate th_b and th_c numerically
    lhs, _ = integrate.dblquad(lambda tc, tb: f(tb, tc, 0.3), 0, 2 * math.pi, 0, 2 * math.pi,
                               epsabs=1e-12, epsrel=1e-12)
    lhs *= 2 * math.pi
    rhs = (2 * math.pi) ** 3 * reduced(beta, gamma, delta, a, 0)
    return lhs, rhs


def reduced(beta, gamma, delta, a, density_power):
    """The integrand after the three phase integrals, divided by (2 pi)^3, without the radial
    Jacobian beta gamma delta: exp(-a (1 + beta^2 gamma^2)/(2 delta^2) - a (beta^2+gamma^2+delta^2)/2)
    * I0(a beta gamma / delta^2) * delta^density_power, written with i0e for stability."""
    x = a * beta * gamma / delta ** 2
    expo = -a * (1 - beta * gamma) ** 2 / (2 * delta ** 2) - a * (beta ** 2 + gamma ** 2 + delta ** 2) / 2
    return math.exp(expo) * special.i0e(x) * delta ** density_power


def check_beta_reduction(a):
    """At fixed (u, delta), int_0^oo of the reduced integrand in beta (gamma = u/beta, with the
    Jacobian beta gamma dgamma = u du / beta) equals u K0(a u) * (the beta-free factor)."""
    u, delta = 0.8, 0.6
    lhs, _ = integrate.quad(lambda beta: u / beta * reduced(beta, u / beta, delta, a, 0),
                            0, np.inf, epsabs=1e-14, epsrel=1e-12)
    rhs = u * special.k0(a * u) * radial_factor(u, delta, a)
    return lhs, rhs


def radial_factor(u, delta, a):
    """exp(-a (1-u)^2/(2 delta^2) - a delta^2/2) * I0(a u/delta^2) exp(-a u/delta^2)."""
    return (math.exp(-a * (1 - u) ** 2 / (2 * delta ** 2) - a * delta ** 2 / 2)
            * special.i0e(a * u / delta ** 2))


def chart_integral(a, density_power):
    """int over C^3 of exp(-a coshDist) |d|^density_power, via the polar and Bessel reductions."""
    # the integrand in u peaks at u = 1 with width ~ delta; split the u-range there
    def inner_split(delta):
        def g(u):
            return u * special.k0(a * u) * radial_factor(u, delta, a)
        v1, _ = integrate.quad(g, 0, 1, epsabs=1e-13, epsrel=1e-11, limit=400)
        v2, _ = integrate.quad(g, 1, np.inf, epsabs=1e-13, epsrel=1e-11, limit=400)
        return (v1 + v2) * delta ** (1 + density_power)
    val, err = integrate.quad(inner_split, 0, np.inf, epsabs=1e-12, epsrel=1e-10, limit=400)
    return (2 * math.pi) ** 3 * val, (2 * math.pi) ** 3 * err


def radial_side(a):
    """4 pi^3 int_1^oo exp(-a t) sqrt(t^2 - 1) dt, by quadrature and in closed form 4 pi^3 K1(a)/a."""
    val, _ = integrate.quad(lambda t: math.exp(-a * t) * math.sqrt(t * t - 1), 1, np.inf,
                            epsabs=1e-13, epsrel=1e-13)
    return 4 * math.pi ** 3 * val, 4 * math.pi ** 3 * special.k1(a) / a


def main():
    ok = True
    for a in (1.0, 2.0):
        lhs, rhs = check_phase_reduction(a)
        good = abs(lhs - rhs) < TOL * abs(rhs)
        ok &= good
        print(f"a={a}: phase reduction at a sample point  {lhs:.12f} vs {rhs:.12f}  "
              f"{'OK' if good else 'FAIL'}")
        lhs, rhs = check_beta_reduction(a)
        good = abs(lhs - rhs) < TOL * abs(rhs)
        ok &= good
        print(f"a={a}: beta reduction at a sample point   {lhs:.12f} vs {rhs:.12f}  "
              f"{'OK' if good else 'FAIL'}")

    for a in (1.0, 2.0):
        quad_val, closed = radial_side(a)
        chart, err = chart_integral(a, -2)
        good = abs(quad_val - closed) < 1e-10 * closed and abs(chart - closed) < TOL * closed
        ok &= good
        print(f"a={a}: Haar chart integral {chart:.10f} (quadrature error {err:.1e}), "
              f"4 pi^3 K1(a)/a = {closed:.10f}  {'OK' if good else 'FAIL'}")

        flat, _ = chart_integral(a, 0)
        differs = abs(flat - closed) > 1e-2 * closed
        ok &= differs
        print(f"a={a}: control, flat chart measure (no |d|^-2): {flat:.10f}  "
              f"{'differs as expected' if differs else 'FAIL: does not differ'}")

    print("OK" if ok else "FAILED")
    return ok


if __name__ == "__main__":
    sys.exit(0 if main() else 1)
