"""Numerical check (not a proof) of the stationary phase theorem in
Lightlike/Oscillatory/StationaryPhase.lean.

For a smooth phase phi with Im phi >= 0 on the support of a smooth compactly supported a, whose
critical points (Im phi = 0, d phi = 0) on the support form a finite set K, all nondegenerate,
    R(tau) = int a e^(i tau phi) - sum over x0 in K of
             e^(i tau phi(x0)) (2 pi / tau)^(n/2) det(-i Hess phi(x0))^(-1/2) a(x0)
is O(tau^(-n/2 - 1)) (Lean: stationary_phase; Hormander, ALPDO I, Theorem 7.7.5). The
square root is the principal branch on each eigenvalue of -i Hess phi(x0), as in Lean's
invSqrtDet; for the diagonal Hessians used here it is the product of the principal powers.

The amplitudes are plateau cutoffs, equal to 1 on |x| <= R/2 and 0 for |x| >= R. Lean's bump
(smallAmp, a Mathlib ContDiffBump) has the same plateau and support but an unspecified profile in
between; the theorem's leading term depends only on a(x0) = 1, and the remainder bound holds for
every smooth amplitude, so the profile does not matter. The integrals are computed by the
trapezoidal rule, with the step chosen so that 2 pi / h is far above tau max |grad Re phi|; the
integrands are smooth with compact support, so the rule converges faster than any power of the
step. The computation is independent of the Lean proof.

Decay test. The envelope M_j = max |R(tau)| over tau in [tau0 2^j, tau0 2^(j+1)] and the local
power p_j = log2(M_j / M_(j+1)). For R ~ tau^-q, p_j tends to q. An instance passes if p at the
last pair of windows is at least n/2 + 1 - TOL, with TOL = 0.15.

Checks, which must pass:
 1. phi = x^2/2 + x^3 + i x^4 on R^1 (Lean: stationary_phase_testPhase), R = 1, K = {0}, Hessian 1,
    leading term (2 pi/tau)^(1/2) e^(i pi/4). Also the next coefficient: Hormander's L_1 for
    g = phi - x^2/2 = x^3 + i x^4 and a = 1 near 0 has the terms (nu, mu) = (2, 1), giving
    -i/8 g''''(0) = 3, and (3, 2), giving i/96 (g^2)^(6)(0) = 7.5 i. So
    tau R / ((2 pi/tau)^(1/2) e^(i pi/4)) = L_1 + O(1/tau) with L_1 = 3 + 7.5 i; the Richardson
    estimate from tau = 3200, 6400 must be within 0.01 of it;
 2. phi = x^3/3 - x + i (x^2 - 1)^2 on R^1 (Lean: stationary_phase_twoPhase), R = 2, K = {1, -1},
    phi(+-1) = -+2/3, -i phi''(+-1) = 8 -+ 2i, leading term
    (2 pi/tau)^(1/2) (e^(-2 i tau/3) (8 - 2i)^(-1/2) + e^(2 i tau/3) (8 + 2i)^(-1/2));
 3. phi = (x^2 - y^2)/2 + i (x^4 + y^4) on R^2, R = 1, K = {0}, Hessian diag(1, -1) of signature 0,
    so det(-i H)^(-1/2) = (-i)^(-1/2) i^(-1/2) = 1 and the leading term is (2 pi/tau) a(0);
 4. the degenerate phase phi = i x^4 on R^1, R = 1 (Lean: integral_quartic_lower): the integral
    equals 2 Gamma(5/4) tau^(-1/4) up to e^(-tau/16) (the amplitude is 1 on |x| <= 1/2), and it
    is at least Lean's lower bound 2 e^(-1) tau^(-1/4) at every sample;
 5. a critical point on the boundary of the support (Lean: stationary_phase_edge):
    phi = x^2/2 + i x^3 on R^1, whose imaginary part x^3 is negative for x < 0, and
    a = psi(x) psi(1 - x) with psi(t) = e^(-1/t) for t > 0, supported on [0, 1] and flat at 0. The
    leading term is (2 pi/tau)^(1/2) e^(i pi/4) a(0) = 0, so the integral itself must pass the
    decay test (it decays faster than any power).
Controls, which must FAIL the decay test:
 (a) the test phase without the Fresnel factor e^(i pi/4): R ~ tau^(-1/2) (Lean:
     testPhase_wrong_phase, for the local form);
 (b) the two-point phase with the contribution of x0 = -1 left out: R ~ tau^(-1/2);
 (c) the 2D phase with the positive-definite branch det(-i I)^(-1/2) = e^(i pi/2) instead of the
     signature-0 value 1: R ~ tau^(-1);
 (d) the degenerate phase i x^4 with the formula's leading term for any coefficient (here the
     coefficient 1, and 0): the integral decays like tau^(-1/4), so p tends to 1/4 (Lean:
     stationary_phase_needs_nondegenerate);
 (e) the edge phase of check 5 with an amplitude that is not flat at the boundary: 1 near x = 0
     and cut off sharply below 0 (the plateau cutoff of radius 1 on [0, 1]). The boundary point now
     contributes half of the Fresnel term, (1/2) (2 pi/tau)^(1/2) e^(i pi/4), so the integral decays
     like tau^(-1/2). Flatness of the amplitude, which smoothness forces at a boundary critical
     point, is what removes the leading term.
The script exits with code 0 only if every check passes and every control fails.

Usage: python3 -I scripts/oscillatory/stationary_check.py
"""
import math
import sys

import numpy as np

TOL = 0.15
SAMPLES = 200
CHUNK = 8


def psi(t):
    out = np.zeros_like(t)
    pos = t > 0
    out[pos] = np.exp(-1.0 / t[pos])
    return out


def plateau(r, rad):
    """Smooth cutoff: 1 on r <= rad/2, 0 on r >= rad."""
    t = (rad - r) / (rad / 2)
    return psi(t) / (psi(t) + psi(1 - t))


def integrals(amp, phase, weight, taus):
    """Trapezoidal sums of amp * exp(i tau phase) for each tau (amp vanishes at the ends)."""
    out = []
    for i in range(0, len(taus), CHUNK):
        t = np.asarray(taus[i:i + CHUNK])[:, None]
        out.extend(weight * np.sum(amp[None, :] * np.exp(1j * t * phase[None, :]), axis=1))
    return np.array(out)


def envelope(amp, phase, weight, lead, tau0, windows, samples=SAMPLES):
    """Envelopes of R = I - lead(tau) over dyadic windows, and their local powers."""
    Ms, data = [], []
    for j in range(windows):
        taus = np.linspace(tau0 * 2 ** j, tau0 * 2 ** (j + 1), samples)
        vals = integrals(amp, phase, weight, taus)
        Ms.append(np.max(np.abs(vals - lead(taus))))
        data.append((taus, vals))
    Ms = np.array(Ms)
    return Ms, np.log2(Ms[:-1] / Ms[1:]), data


def report(name, tau0, Ms, ps, target):
    print(f"{name}: windows from tau = {tau0:g}, envelopes",
          ", ".join(f"{m:.2e}" for m in Ms))
    print("  local powers p =", ", ".join(f"{p:.2f}" for p in ps), f"(target {target:g})")
    return ps[-1] >= target - TOL


def verdict(good, control=False):
    if control:
        print("  ", "control FAILED as required" if not good else "control PASSED (error)")
        return not good
    print("  ", "OK" if good else "FAILED")
    return good


def main():
    ok = True
    fresnel = np.exp(1j * np.pi / 4)

    # 1. the test phase, one critical point
    h1 = 5e-5
    x1 = np.arange(-1.0, 1.0 + h1 / 2, h1)
    a1 = plateau(np.abs(x1), 1.0)
    F1 = x1 ** 2 / 2 + x1 ** 3 + 1j * x1 ** 4

    def lead1(t):
        return np.sqrt(2 * np.pi / t) * fresnel

    Ms, ps, data = envelope(a1, F1, h1, lead1, 100, 5)
    good = report("1. x^2/2 + x^3 + i x^4, K = {0}", 100, Ms, ps, 1.5)
    t, v = data[-1]
    print(f"  tau^(1/2) I / sqrt(2 pi) at tau = {t[-1]:g}: {np.sqrt(t[-1] / (2 * np.pi)) * v[-1]:.6f}"
          f" (e^(i pi/4) = {fresnel:.6f})")
    tt = np.array([3200.0, 6400.0])
    L1 = tt * (integrals(a1, F1, h1, tt) - lead1(tt)) / lead1(tt)
    L1r = 2 * L1[1] - L1[0]
    print(f"  next coefficient L_1 (Richardson, tau = 3200, 6400): {L1r:.4f} (Hormander: 3+7.5j)")
    good = good and abs(L1r - (3 + 7.5j)) < 0.01
    ok &= verdict(good)

    # 2. two critical points
    h2 = 5e-5
    x2 = np.arange(-2.0, 2.0 + h2 / 2, h2)
    a2 = plateau(np.abs(x2), 2.0)
    F2 = x2 ** 3 / 3 - x2 + 1j * (x2 ** 2 - 1) ** 2
    cp = (8 - 2j) ** -0.5
    cm = (8 + 2j) ** -0.5

    def lead2(t):
        return np.sqrt(2 * np.pi / t) * (np.exp(-2j * t / 3) * cp + np.exp(2j * t / 3) * cm)

    Ms, ps, _ = envelope(a2, F2, h2, lead2, 100, 5)
    good = report("2. x^3/3 - x + i (x^2 - 1)^2, K = {1, -1}", 100, Ms, ps, 1.5)
    ok &= verdict(good)

    # 3. two dimensions, signature 0
    h3 = 2e-3
    g = np.arange(-1.0, 1.0 + h3 / 2, h3)
    X, Y = np.meshgrid(g, g, indexing="ij")
    r = np.sqrt(X * X + Y * Y).ravel()
    a3 = plateau(r, 1.0)
    keep = a3 > 0
    F3 = ((X * X - Y * Y) / 2 + 1j * (X ** 4 + Y ** 4)).ravel()[keep]
    a3 = a3[keep]
    c3 = (-1j) ** -0.5 * (1j) ** -0.5
    print(f"  det(-i diag(1, -1))^(-1/2) = {c3:.6f}")

    def lead3(t):
        return (2 * np.pi / t) * c3

    Ms, ps, _ = envelope(a3, F3, h3 * h3, lead3, 25, 4, samples=60)
    good = report("3. (x^2 - y^2)/2 + i (x^4 + y^4) on R^2, K = {0}", 25, Ms, ps, 2.0)
    ok &= verdict(good)

    # 4. the degenerate phase: known value and Lean's lower bound
    F4 = 1j * x1 ** 4
    taus = np.linspace(400, 6400, 200)
    vals = integrals(a1, F4, h1, taus)
    exact = 2 * math.gamma(1.25) * taus ** -0.25
    rel = np.max(np.abs(vals - exact) / exact)
    taus_lb = np.linspace(16, 6400, 200)
    vals_lb = integrals(a1, F4, h1, taus_lb)
    lb_ok = bool(np.all(vals_lb.real >= 2 * np.exp(-1) * taus_lb ** -0.25))
    good = rel < 1e-8 and lb_ok and np.max(np.abs(vals_lb.imag)) < 1e-12
    print(f"4. i x^4: max relative error against 2 Gamma(5/4) tau^(-1/4) on [400, 6400]: {rel:.2e};"
          f" I >= 2 e^(-1) tau^(-1/4) on [16, 6400]: {lb_ok}")
    ok &= verdict(good)

    # 5. a critical point on the boundary of the support
    x5 = np.arange(0.0, 1.0 + h1 / 2, h1)
    a5 = psi(x5) * psi(1 - x5)
    F5 = x5 ** 2 / 2 + 1j * x5 ** 3
    Ms, ps, _ = envelope(a5, F5, h1, lambda t: 0 * t, 100, 5)
    good = report("5. x^2/2 + i x^3, a = psi(x) psi(1 - x), K = {0} on the boundary", 100, Ms, ps,
                  1.5)
    ok &= verdict(good)

    # controls
    Ms, ps, _ = envelope(a1, F1, h1, lambda t: np.sqrt(2 * np.pi / t), 100, 5)
    ok &= verdict(report("control (a) test phase without e^(i pi/4)", 100, Ms, ps, 1.5), True)

    Ms, ps, _ = envelope(a2, F2, h2,
                         lambda t: np.sqrt(2 * np.pi / t) * np.exp(-2j * t / 3) * cp, 100, 5)
    ok &= verdict(report("control (b) two-point phase, x0 = -1 left out", 100, Ms, ps, 1.5), True)

    Ms, ps, _ = envelope(a3, F3, h3 * h3, lambda t: (2 * np.pi / t) * 1j, 25, 4, samples=60)
    ok &= verdict(report("control (c) 2D, positive-definite branch e^(i pi/2)", 25, Ms, ps, 2.0),
                  True)

    for c in (1.0, 0.0):
        Ms, ps, _ = envelope(a1, F4, h1, lambda t, c=c: np.sqrt(2 * np.pi / t) * c, 100, 5)
        ok &= verdict(report(f"control (d) i x^4 with coefficient {c:g}", 100, Ms, ps, 1.5), True)

    # trapezoidal rule on [0, 1]: half weight at the jump x = 0
    b5 = plateau(x5, 1.0)
    b5[0] /= 2
    Ms, ps, _ = envelope(b5, F5, h1, lambda t: 0 * t, 100, 5)
    ok &= verdict(report("control (e) edge phase, amplitude not flat at 0", 100, Ms, ps, 1.5), True)

    print("OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
