"""Numerical cross-check of the limit formula for orbital integrals of SL(2,C) (milestone HA2).

Lean (Lightlike/Lorentz/LimitFormula.lean, `limit_formula`): for F smooth with compact
support on M_2(C) and invariant under conjugation by SU(2),

    d^2/dt^2 Phi_F(e^t)|_0 + d^2/dt^2 Phi_F(e^{it})|_0 = -8 pi F(1),
    Phi_F(mu) = int_C F([[mu, x], [0, 1/mu]]) d^2x.

The Lean proof compares second derivatives along orbit curves and integrates in polar
coordinates. This script does neither: it forms the matrices [[mu, x], [0, 1/mu]] explicitly,
evaluates F on them, integrates over x in C by quadrature (adaptive in |x|, trapezoidal in arg x),
and takes the second t-derivatives by central differences with Richardson extrapolation.

Test functions (phi is a bump that equals 1 on [1.5, 2.5] and vanishes outside (1, 3), like
`testBump` in SphericalPlancherelTests.lean; Lean uses only these two properties of it):
- `testLF`: F(X) = phi(||X||_HS^2), the function of LimitFormulaTests.lean; formula value -8 pi.
- `trace-weighted`: F(X) = phi(||X||_HS^2) (1 + (tr X)^2/4 + i tr X/2), also SU(2)-invariant. Here
  each of the two second derivatives has a first-order term that only cancels in the sum, which is
  the mechanism of the Lean proof.

Controls (wrong inputs, each must differ from -8 pi F(1)): the non-invariant
F(X) = phi(||X||_HS^2)(1 + |X_01|^2); the trace-weighted F with only the direction e^t; and the
constant -4 pi in place of -8 pi. This is numerical evidence, not proof.

Run: .venv/bin/python -I scripts/lorentz/limit_formula_check.py   (needs numpy and scipy)
"""
import cmath
import math
import sys

import numpy as np
from scipy import integrate

TOL = 1e-6           # relative tolerance for the formula
N_ARG = 32           # trapezoidal nodes in arg x (exact for the trigonometric polynomials here)
H = 0.04             # finite-difference step


def smooth_transition(x):
    """exp(-1/x) / (exp(-1/x) + exp(-1/(1-x))), 0 for x <= 0, 1 for x >= 1."""
    if x <= 0.0:
        return 0.0
    if x >= 1.0:
        return 1.0
    a, b = math.exp(-1.0 / x), math.exp(-1.0 / (1.0 - x))
    return a / (a + b)


def phi(u):
    """Bump centred at 2: 1 on [1.5, 2.5], 0 outside (1, 3) (rIn = 1/2, rOut = 1)."""
    return smooth_transition((1.0 - abs(u - 2.0)) / 0.5)


def hs_sq(X):
    return float(np.sum(np.abs(X) ** 2))


TEST_FUNCTIONS = {
    "testLF": lambda X: complex(phi(hs_sq(X))),
    "trace-weighted": lambda X: phi(hs_sq(X)) * (1 + np.trace(X) ** 2 / 4 + 0.5j * np.trace(X)),
}
NON_INVARIANT = lambda X: phi(hs_sq(X)) * (1 + abs(X[0, 1]) ** 2)  # noqa: E731

IDENTITY = np.eye(2, dtype=complex)


def orbital_integral(F, mu):
    """int_C F([[mu, x], [0, 1/mu]]) d^2x, with x = r e^{i theta}, d^2x = r dr dtheta.

    F vanishes once ||X||_HS^2 = |mu|^2 + |mu|^-2 + r^2 >= 3, so r < 1 suffices for |mu| near 1.
    """
    thetas = 2 * math.pi * np.arange(N_ARG) / N_ARG

    def ring(r, part):
        vals = [F(np.array([[mu, r * cmath.exp(1j * th)], [0, 1 / mu]])) for th in thetas]
        return getattr(np.mean(vals), part) * 2 * math.pi * r

    a = abs(mu) ** 2 + abs(mu) ** -2
    pts = [math.sqrt(max(u - a, 0.0)) for u in (2.5, 3.0) if u > a]
    out = []
    for part in ("real", "imag"):
        v, _ = integrate.quad(ring, 0.0, 1.0, args=(part,), points=pts or None, epsabs=1e-13,
                              epsrel=1e-12, limit=400)
        out.append(v)
    return complex(*out)


def second_derivative(f, h=H):
    """f''(0) by central differences, Richardson-extrapolated (error O(h^4))."""
    def d(k):
        return (f(k) - 2 * f(0.0) + f(-k)) / (k * k)
    return (4 * d(h / 2) - d(h)) / 3


def lhs(F, directions=(1.0, 1j)):
    return sum(second_derivative(lambda t, w=w: orbital_integral(F, cmath.exp(t * w)))
               for w in directions)


def main():
    ok = True
    for name, F in TEST_FUNCTIONS.items():
        left = lhs(F)
        right = -8 * math.pi * F(IDENTITY)
        good = abs(left - right) < TOL * abs(right)
        ok &= good
        print(f"{name}: Laplacian of Phi_F at 1 = {left:.10f},  -8 pi F(1) = {right:.10f}"
              f"  rel. diff {abs(left - right) / abs(right):.1e}  {'OK' if good else 'FAIL'}")
    F = TEST_FUNCTIONS["trace-weighted"]
    controls = {
        "non-invariant F = phi(|X|^2)(1 + |X_01|^2)":
            (lhs(NON_INVARIANT), -8 * math.pi * NON_INVARIANT(IDENTITY)),
        "trace-weighted F, direction e^t only":
            (lhs(F, directions=(1.0,)), -8 * math.pi * F(IDENTITY)),
        "testLF, constant -4 pi":
            (lhs(TEST_FUNCTIONS["testLF"]), -4 * math.pi * TEST_FUNCTIONS["testLF"](IDENTITY)),
    }
    for label, (left, right) in controls.items():
        differs = abs(left - right) > 1e-3 * abs(right)
        ok &= differs
        print(f"control, {label}: {left:.10f} vs {right:.10f}  "
              f"{'differs as expected' if differs else 'FAIL: does not differ'}")
    print("OK" if ok else "FAILED")
    return ok


if __name__ == "__main__":
    sys.exit(0 if main() else 1)
