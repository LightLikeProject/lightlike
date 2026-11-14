"""Numerical check (not a proof) of the quadratic-phase lemma in
Lightlike/Oscillatory/QuadraticPhase.lean.

For a complex symmetric n x n matrix A with det A != 0 and Im A positive semidefinite, and a
smooth compactly supported u (Lean: quadratic_phase),
    I(tau) = int_{R^n} u(x) exp(i tau <A x, x>/2) dx
           = L(tau) + O(tau^(-n/2-1)),   L(tau) = (2 pi/tau)^(n/2) invSqrtDet(-iA) u(0),
where invSqrtDet(-iA) is the product of the principal roots mu^(-1/2) over the eigenvalues mu
of -iA. Hormander, ALPDO I, Lemma 7.7.3, also gives the next term:
    I(tau) = L(tau) (1 + (i/(2 tau)) tr(A^-1 Hess u(0)) + O(tau^-2)).
Here u(x) = exp(1/4 - 1/(4 - |x|^2)) on |x| < 2 (zero outside), so u(0) = 1 and
Hess u(0) = -1/8 Id, and the predicted coefficient is
    kappa = lim tau (I/L - 1) = -i tr(A^-1) / 16.

I(tau) is computed by the tensor-product trapezoidal rule on [-2, 2]^n. The integrand is smooth
with compact support, so the rule converges faster than any power of the step. The computation
is independent of the Lean proof. Checks, on six instances (n = 1, 2; real and complex,
diagonal and not; Im A definite, semidefinite of rank 1, and zero):
 1. A is symmetric, Im A is positive semidefinite, det A != 0 (sanity of the instance);
 2. every eigenvalue of -iA has Re >= 0 (Lean: im_nonneg_of_mem_roots);
 3. tau^(n/2+1) |I - L| does not grow over TAUS (a 16-fold range of tau): its value at the
    largest tau is at most twice its value at the smallest. A wrong leading coefficient leaves
    an O(tau^(-n/2)) error, so this quantity then grows linearly in tau;
 4. |tau (I/L - 1) - kappa| < 2e-3 at the two largest tau (the next-order coefficient).
Controls, which must FAIL check 3:
 (a) wrong phase: (2 pi/tau)^(1/2) u(0), the leading term of the real Gaussian of Laplace's
     method without the Fresnel factor e^(i pi/4), for A = 1 on R^1 (Lean:
     fresnel_bump_wrong_phase);
 (b) wrong branch: -L for A = 1 + i/2 on R^1, the other square root of 1/det(-iA) (Lean:
     fresnel_bump_wrong_branch);
 (c) wrong input: A = 0 on R^1, where I = int u does not decay, while the formula's leading
     term is 0 since invSqrtDet 0 = 0 in Lean (Lean: quadratic_phase_needs_det).
The script exits with code 0 only if every check passes and every control fails.

Usage: .venv/bin/python -I scripts/oscillatory/quadphase_check.py
"""
import sys

import numpy as np

TAUS = {1: [20.0, 40.0, 80.0, 160.0, 320.0], 2: [10.0, 20.0, 40.0, 80.0, 160.0]}
STEP = {1: 2e-4, 2: 1.25e-3}
CHUNK = 200


def amplitude(r2):
    """The bump exp(1/4 - 1/(4 - r^2)) on r^2 < 4, zero outside."""
    out = np.zeros_like(r2)
    inside = r2 < 4.0
    out[inside] = np.exp(0.25 - 1.0 / (4.0 - r2[inside]))
    return out


def integral(A, tau):
    """I(tau) = int u(x) exp(i tau <A x, x>/2) dx by the trapezoidal rule on [-2, 2]^n.

    For n = 2 the grid is summed in blocks of CHUNK rows to bound memory."""
    n = A.shape[0]
    h = STEP[n]
    t = np.arange(-2.0, 2.0 + h / 2, h)
    if n == 1:
        return np.sum(amplitude(t * t) * np.exp(1j * tau * A[0, 0] * t * t / 2)) * h
    total = 0j
    y = t[None, :]
    for i0 in range(0, len(t), CHUNK):
        x = t[i0:i0 + CHUNK, None]
        q = A[0, 0] * x * x + 2 * A[0, 1] * x * y + A[1, 1] * y * y
        total += np.sum(amplitude(x * x + y * y) * np.exp(1j * tau * q / 2))
    return total * h * h


def inv_sqrt_det(M):
    """invSqrtDet M: the product of principal roots mu^(-1/2) over the eigenvalues of M."""
    return np.prod(np.linalg.eigvals(M).astype(complex) ** -0.5)


def leading(A, tau):
    """L(tau) = (2 pi/tau)^(n/2) invSqrtDet(-iA) u(0), with u(0) = 1."""
    n = A.shape[0]
    return (2 * np.pi / tau) ** (n / 2) * inv_sqrt_det(-1j * A)


INSTANCES = {
    "A = 1 (n = 1)": np.array([[1.0]], dtype=complex),
    "A = -2 (n = 1)": np.array([[-2.0]], dtype=complex),
    "A = 1 + i/2 (n = 1)": np.array([[1.0 + 0.5j]]),
    "A = diag(1, -1), signature 0": np.diag([1.0, -1.0]).astype(complex),
    "A = [[1, 1/2], [1/2, -1]] + 0.3i Id": np.array([[1.0, 0.5], [0.5, -1.0]]) + 0.3j * np.eye(2),
    "A = [[2, 1], [1, 2]] + i [[0.4, 0.2], [0.2, 0.1]], Im A of rank 1":
        np.array([[2.0, 1.0], [1.0, 2.0]]) + 1j * np.array([[0.4, 0.2], [0.2, 0.1]]),
}


def no_growth(errs):
    """Check 3: the scaled error at the largest tau is at most twice that at the smallest."""
    return errs[-1] <= 2 * errs[0]


def scaled_errors(A, values, coeff_fn):
    """tau^(n/2+1) |I(tau) - coeff_fn(tau)| over TAUS, from precomputed values I(tau)."""
    n = A.shape[0]
    return [tau ** (n / 2 + 1) * abs(v - coeff_fn(tau)) for tau, v in zip(TAUS[n], values)]


def main():
    ok = True
    for name, A in INSTANCES.items():
        n = A.shape[0]
        values = [integral(A, tau) for tau in TAUS[n]]
        sym = np.allclose(A, A.T)
        im_psd = np.linalg.eigvalsh((A.imag + A.imag.T) / 2).min() >= -1e-12
        nondeg = abs(np.linalg.det(A)) > 1e-9
        eig_ok = np.linalg.eigvals(-1j * A).real.min() >= -1e-12
        errs = scaled_errors(A, values, lambda tau: leading(A, tau))
        kappa = -1j * np.trace(np.linalg.inv(A)) / 16
        devs = [abs(tau * (v / leading(A, tau) - 1) - kappa) for tau, v in zip(TAUS[n], values)]
        good = (sym and im_psd and nondeg and eig_ok and no_growth(errs)
                and max(devs[-2:]) < 2e-3)
        ok &= good
        print(f"{name}: invSqrtDet(-iA) = {inv_sqrt_det(-1j * A):.6f}, kappa = {kappa:.6f}")
        print("  tau =", ", ".join(f"{tau:g}" for tau in TAUS[n]))
        print("  tau^(n/2+1)|I - L| =", ", ".join(f"{e:.4f}" for e in errs))
        print("  |tau (I/L - 1) - kappa| =", ", ".join(f"{d:.2e}" for d in devs))
        print("  ", "OK" if good else "FAILED")

    one = np.array([[1.0]], dtype=complex)
    wrong_phase = scaled_errors(one, [integral(one, tau) for tau in TAUS[1]],
                                lambda tau: (2 * np.pi / tau) ** 0.5)
    damped = np.array([[1.0 + 0.5j]])
    wrong_branch = scaled_errors(damped, [integral(damped, tau) for tau in TAUS[1]],
                                 lambda tau: -leading(damped, tau))
    zero = np.zeros((1, 1), dtype=complex)
    degenerate = scaled_errors(zero, [integral(zero, tau) for tau in TAUS[1]], lambda tau: 0.0)
    controls_fail = True
    for label, errs in [("(a) no Fresnel phase, A = 1", wrong_phase),
                        ("(b) other branch, A = 1 + i/2", wrong_branch),
                        ("(c) A = 0", degenerate)]:
        fails = not no_growth(errs)
        controls_fail &= fails
        print(f"control {label}: tau^(3/2)|I - L| =", ", ".join(f"{e:.2f}" for e in errs),
              "(fails check 3)" if fails else "(PASSES check 3: control broken)")
    ok &= controls_fail
    print("OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
