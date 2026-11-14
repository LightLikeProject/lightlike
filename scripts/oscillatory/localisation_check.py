"""Numerical check (not a proof) of non-stationary phase and localisation in
Lightlike/Oscillatory/Localisation.lean.

For u smooth with compact support and a smooth phase F with Im F >= 0 on the support of u,
    I(tau) = int u(x) exp(i tau F(x)) dx
is O(tau^-k) for every k if every point of the support has dF != 0 or Im F > 0 (Lean:
nonstationary_phase, exists_bound_noncritical; Hormander, ALPDO I, Theorem 7.7.1). If the critical
points (Im F = 0, dF = 0) on the support of a form a finite set K, then for suitable smooth cutoffs
chi_x0 supported near x0 in K, with chi_x0(x0) = 1,
    D(tau) = int a e^(i tau F) - sum over x0 in K of int chi_x0 a e^(i tau F)
is O(tau^-k) for every k (Lean: integral_localise). The cutoffs there come from a smooth partition
of unity, so each equals 1 on a neighbourhood of its point; here chi is a plateau cutoff, equal
to 1 on |x| <= r/2 and 0 for |x| >= r.

The amplitudes are bumps u(x) = exp(1/4 - 1/(4 - 4|x|^2/R^2)) on |x| < R (zero outside), and the
integrals are computed by the trapezoidal rule. The integrands are smooth with compact support,
so the rule converges faster than any power of the step, and the step is chosen with 2 pi/h
far above the largest tau, so that aliasing is negligible. The computation is independent of the
Lean proof.

Decay test. A smooth compactly supported u decays faster than any power but not exponentially,
and I(tau) oscillates, so the test uses the envelope M_j = max |I(tau)| over the window
tau in [tau0 2^j, tau0 2^(j+1)], and the local power p_j = log2(M_j / M_(j+1)). For I ~ tau^-a,
p_j tends to a; for decay faster than every power, p_j grows without bound. An instance passes if
p at the last pair of windows is at least P_MIN = 6.

Checks, which must pass:
 1. F(x) = x on R^1 (Lean: nonstationary_phase_linPhase), R = 1;
 2. F(x) = x + i x^2 on R^1, R = 1: complex phase, dF != 0;
 3. F(x, y) = x + i (x^2 + y^2)/2 on R^2, R = 1: dF != 0 everywhere;
 4. F(x) = x^2/2 + i/2 on R^1, R = 1: a critical point of Re F with Im F = 1/2 > 0, the
    exponential branch of exists_bound_noncritical (Lean: noncritical_const_I, for F = i). Also
    |I(tau)| <= e^(-tau/2) int u at every sample (exists_bound_exp with c = 1/2);
 5. localisation: F = x^2/2 + x^3 + i x^4 (the Lean test phase, whose only critical point is 0),
    a = bump with R = 1, chi = plateau cutoff with r = 1/2 (Lean: localise_testPhase, with a
    cutoff supported in the ball of radius 1/2): D(tau) = int (1 - chi) a e^(i tau F).
Controls, which must FAIL the decay test:
 (a) a critical point: int a e^(i tau F) itself for the test phase decays like tau^(-1/2)
     (stationary phase), so p tends to 1/2 (Lean: nonstationary_phase_needs_noncritical);
 (b) F = 0 (Im F = 0, dF = 0): I is the constant int u, p = 0 (Lean:
     noncritical_needs_hypothesis);
 (c) a cutoff that equals 1 only at the critical point: chi = the bump with R = 1/2, so
     1 - chi ~ x^2 near 0 and D(tau) ~ tau^(-3/2), p tends to 3/2. So chi(x0) = 1 alone does not
     give the remainder bound; it holds for the partition-of-unity cutoffs that integral_localise
     constructs, which equal 1 near x0.
The script exits with code 0 only if every check passes and every control fails.

Usage: python3 -I scripts/oscillatory/localisation_check.py
"""
import sys

import numpy as np

P_MIN = 6.0
SAMPLES = 60
CHUNK = 8


def bump(r2, R):
    """The bump exp(1/4 - 1/(4 - 4 r^2/R^2)) on r < R, zero outside; equal to 1 at 0."""
    out = np.zeros_like(r2)
    inside = r2 < R * R
    out[inside] = np.exp(0.25 - 1.0 / (4.0 - 4.0 * r2[inside] / (R * R)))
    return out


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


def envelope(amp, phase, weight, tau0, windows):
    Ms, samples = [], []
    for j in range(windows):
        taus = np.linspace(tau0 * 2 ** j, tau0 * 2 ** (j + 1), SAMPLES)
        vals = integrals(amp, phase, weight, taus)
        Ms.append(np.max(np.abs(vals)))
        samples.append((taus, vals))
    Ms = np.array(Ms)
    return Ms, np.log2(Ms[:-1] / Ms[1:]), samples


def report(name, tau0, Ms, ps):
    print(f"{name}: windows from tau = {tau0:g}, envelopes",
          ", ".join(f"{m:.2e}" for m in Ms))
    print("  local powers p =", ", ".join(f"{p:.2f}" for p in ps))
    return ps[-1] >= P_MIN


def main():
    ok = True
    h1 = 2e-4
    x = np.arange(-1.0, 1.0 + h1 / 2, h1)
    u = bump(x * x, 1.0)

    Ms, ps, _ = envelope(u, x + 0j, h1, 25, 6)
    good = report("1. F = x", 25, Ms, ps)
    print("  ", "OK" if good else "FAILED")
    ok &= good

    Ms, ps, _ = envelope(u, x + 1j * x * x, h1, 25, 3)
    good = report("2. F = x + i x^2", 25, Ms, ps)
    print("  ", "OK" if good else "FAILED")
    ok &= good

    h2 = 2e-3
    g = np.arange(-1.0, 1.0 + h2 / 2, h2)
    X, Y = np.meshgrid(g, g, indexing="ij")
    r2 = (X * X + Y * Y).ravel()
    u2 = bump(r2, 1.0)
    keep = u2 > 0
    F2 = (X.ravel() + 0.5j * r2)[keep]
    Ms, ps, _ = envelope(u2[keep], F2, h2 * h2, 25, 3)
    good = report("3. F = x + i (x^2 + y^2)/2 on R^2", 25, Ms, ps)
    print("  ", "OK" if good else "FAILED")
    ok &= good

    Ms, ps, samples = envelope(u, x * x / 2 + 0.5j, h1, 25, 3)
    total = h1 * np.sum(u)
    ratio = max(np.max(np.abs(v) * np.exp(t / 2)) for t, v in samples) / total
    good = report("4. F = x^2/2 + i/2", 25, Ms, ps) and ratio <= 1 + 1e-9
    print(f"  max |I| e^(tau/2) / int u = {ratio:.4f}")
    print("  ", "OK" if good else "FAILED")
    ok &= good

    h5 = 5e-5
    x5 = np.arange(-1.0, 1.0 + h5 / 2, h5)
    a = bump(x5 * x5, 1.0)
    F5 = x5 ** 2 / 2 + x5 ** 3 + 1j * x5 ** 4
    chi = plateau(np.abs(x5), 0.5)
    Ms, ps, _ = envelope((1 - chi) * a, F5, h5, 100, 5)
    good = report("5. localisation, test phase, plateau cutoff r = 1/2", 100, Ms, ps)
    print("  ", "OK" if good else "FAILED")
    ok &= good

    Ms, ps, _ = envelope(a, F5, h5, 100, 5)
    bad = report("control (a) critical point, test phase without cutoff", 100, Ms, ps)
    print("  ", "control FAILED as required" if not bad else "control PASSED (error)")
    ok &= not bad

    Ms, ps, _ = envelope(u, 0 * x + 0j, h1, 25, 6)
    bad = report("control (b) F = 0", 25, Ms, ps)
    print("  ", "control FAILED as required" if not bad else "control PASSED (error)")
    ok &= not bad

    chib = bump(x5 * x5, 0.5)
    Ms, ps, _ = envelope((1 - chib) * a, F5, h5, 100, 5)
    bad = report("control (c) cutoff equal to 1 only at 0", 100, Ms, ps)
    print("  ", "control FAILED as required" if not bad else "control PASSED (error)")
    ok &= not bad

    print("OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
