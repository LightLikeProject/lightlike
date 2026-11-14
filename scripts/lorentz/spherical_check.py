"""Numerical cross-check of the spherical function of SL(2,C) (milestone HA2).

Lean (Lightlike/Lorentz/Spherical.lean, `inner_sphVec_eq_sphericalFn`): for the principal
series (k, rho) = (0, rho) on L^2(C) and e0(z) = pi^{-1/2} (1 + |z|^2)^{i rho - 1},

    <e0, pi(g) e0> = (1/pi) int_C (1 + |z|^2)^{-i rho - 1} N_g(z)^{i rho - 1} d^2z
                   = sin(rho r) / (rho sinh r),     r = arcosh(||g||_F^2 / 2),

with N_g(z) = |g00 z + g10|^2 + |g01 z + g11|^2 (`normT`), and r / sinh r at rho = 0.

The Lean proof uses the Cartan decomposition g = u a_r v and a one-variable substitution on the
diagonal. This script instead integrates over the plane directly, for non-diagonal g, by
two-dimensional quadrature in the stereographic variables z = tan(alpha/2) e^{i theta}, in which
the integrand is smooth and bounded on [0, pi] x [0, 2 pi]. It also checks the kernel
I(g) = int_C d^2z / ((1 + |z|^2) N_g(z)) = pi r / sinh r (`kernelI_eq`).

Controls (wrong inputs): the flat spherical function sin(rho r)/(rho r) of R^3, and the integral
with the vector e0 replaced by its complex conjugate (exponent -i rho - 1 in both factors), give
different numbers. This is numerical evidence, not proof.

Run: .venv/bin/python -I scripts/lorentz/spherical_check.py   (needs numpy and scipy)
"""
import math

import numpy as np
from scipy import integrate

TOL = 1e-7


def sl2c(a, b, c):
    """The matrix [[a, b], [c, (1 + b c)/a]] of determinant 1."""
    return np.array([[a, b], [c, (1 + b * c) / a]], dtype=complex)


def norm_t(g, z):
    """N_g(z) = |g00 z + g10|^2 + |g01 z + g11|^2."""
    return abs(g[0, 0] * z + g[1, 0]) ** 2 + abs(g[0, 1] * z + g[1, 1]) ** 2


def coefficient(g, rho, conj_vector=False):
    """(1/pi) int_C (1+|z|^2)^{-i rho - 1} N_g(z)^{i rho - 1} d^2z by quadrature.

    With z = t e^{i theta}, t = tan(alpha/2): d^2z = t dt dtheta and dt = (1 + t^2)/2 dalpha.
    conj_vector=True uses the exponent -i rho - 1 for N_g as well (the wrong vector conj(e0))."""
    s = -1.0 if conj_vector else 1.0

    def f(alpha, theta, part):
        t = math.tan(alpha / 2)
        z = t * complex(math.cos(theta), math.sin(theta))
        a = 1 + t * t
        n = norm_t(g, z)
        val = (t / 2) * a ** (-1j * rho) * n ** (s * 1j * rho - 1) / math.pi
        return val.real if part == 0 else val.imag

    opts = dict(epsabs=1e-11, epsrel=1e-10)
    re, _ = integrate.dblquad(lambda al, th: f(al, th, 0), 0, 2 * math.pi, 0, math.pi, **opts)
    im, _ = integrate.dblquad(lambda al, th: f(al, th, 1), 0, 2 * math.pi, 0, math.pi, **opts)
    return complex(re, im)


def kernel_i(g):
    """I(g) = int_C d^2z / ((1 + |z|^2) N_g(z)) by quadrature."""
    def f(alpha, theta):
        t = math.tan(alpha / 2)
        z = t * complex(math.cos(theta), math.sin(theta))
        return (t / 2) / norm_t(g, z)
    val, _ = integrate.dblquad(f, 0, 2 * math.pi, 0, math.pi, epsabs=1e-12, epsrel=1e-11)
    return val


def distance(g):
    """r = arcosh(||g||_F^2 / 2)."""
    return math.acosh(float(np.sum(np.abs(g) ** 2)) / 2)


def spherical(rho, r):
    """sin(rho r)/(rho sinh r), with r / sinh r at rho = 0 and 1 at r = 0 (`sphericalFn`)."""
    if r == 0:
        return 1.0
    if rho == 0:
        return r / math.sinh(r)
    return math.sin(rho * r) / (rho * math.sinh(r))


def main():
    ok = True
    samples = [sl2c(1.3 + 0.4j, 0.7 - 0.2j, -0.5 + 0.9j),
               sl2c(0.6 - 0.3j, -1.1 + 0.5j, 0.8 + 0.1j)]
    for k, g in enumerate(samples):
        assert abs(np.linalg.det(g) - 1) < 1e-12
        r = distance(g)
        for rho in (0.0, 0.7, 2.5):
            num = coefficient(g, rho)
            exact = spherical(rho, r)
            good = abs(num - exact) < TOL
            ok &= good
            print(f"g{k} (r = {r:.6f}), rho = {rho}: quadrature {num.real:+.10f}{num.imag:+.1e}i,"
                  f" sin(rho r)/(rho sinh r) = {exact:+.10f}  {'OK' if good else 'FAIL'}")
        num0 = coefficient(g, 0.7)
        flat = math.sin(0.7 * r) / (0.7 * r)
        differs = abs(num0 - flat) > 1e-3
        ok &= differs
        print(f"g{k}: control, flat sin(rho r)/(rho r) = {flat:+.10f}  "
              f"{'differs as expected' if differs else 'FAIL: does not differ'}")
        wrong = coefficient(g, 0.7, conj_vector=True)
        differs = abs(wrong - spherical(0.7, r)) > 1e-3
        ok &= differs
        print(f"g{k}: control, conjugate vector gives {wrong.real:+.10f}{wrong.imag:+.10f}i  "
              f"{'differs as expected' if differs else 'FAIL: does not differ'}")
        ki = kernel_i(g)
        exact = math.pi * r / math.sinh(r)
        good = abs(ki - exact) < TOL * exact
        ok &= good
        print(f"g{k}: I(g) quadrature {ki:.10f}, pi r / sinh r = {exact:.10f}  "
              f"{'OK' if good else 'FAIL'}")

    print("OK" if ok else "FAILED")


if __name__ == "__main__":
    main()
