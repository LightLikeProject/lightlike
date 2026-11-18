# SP3, T-SP3-P1: the full-strength Tauberian theorem (record of the attempts)

Status of 18 November 2026, branch `pl/sp3` (work in progress, not merged). Written for the PR body of
the logarithmic result (`ingham_log`, queue entry 101) and for the maintainers' rule that a "weaker than the
source" result merges as partial only after two different full-proof attempts with concrete failure
reasons. Claim tags follow the project convention: MEASURED = checked in Lean or by reading the cited
location; PROXY / ASSUMPTION = stated as such.

## Sources opened

* B. Mukhametzhanov, A. Zhiboedov, *Modular invariance, tauberian theorems and microcanonical entropy*,
  arXiv:1904.06359, read as text and as page images: the Theorem on p. 7 with eq. (1.8); eqs. (2.3)-(2.7);
  Section 3, eqs. (3.1)-(3.6) (HKS bound); Section 4, eqs. (4.1)-(4.10); Section 5, eqs. (5.1)-(5.19);
  Appendix A, eqs. (A.1)-(A.13). MEASURED (read).
* K. Bringmann, C. Jennings-Shaffer, K. Mahlburg, *On a Tauberian theorem of Ingham and Euler-Maclaurin
  summation*, arXiv:1910.03036: abstract, Theorem 1.1, Section 3.2 (counterexample), Theorems 4.1 and 4.2.
  MEASURED (read). They do not prove Ingham's theorem; they cite Ingham 1941 (not opened by us).
* Not opened: Ingham, Ann. of Math. 42 (1941) 1075-1090; Korevaar, *Tauberian theory* (Springer 2004),
  Section IV.21; Subhankulov (1976); Qiao-Rychkov arXiv:1709.00008.

## What the log result is, and why the full result needs more

`ingham_log` proves `log rho[0,X] ~ 2 sqrt(aX)` from `beta log L(beta) -> a`. The asymptotics of
`rho[0,X]` itself does NOT follow from the real-axis hypothesis `L(beta) ~ C beta^b e^{a/beta}`: BJM Section
3.2 gives a counterexample (an increasing sequence with the right Laplace asymptotics on the real axis
whose partial sums violate the conclusion; attributed there to Avakumovic-Karamata and to Ingham's remark
on p. 1088). Ingham's Theorem 1 (their Theorem 4.1) needs the extra bound `f(z) = O(chi(|z|) e^{phi(|z|)})`
in the sectors `|Im z| <= Delta Re z`. MZ's (1.8) needs modular invariance instead (their Theorem, p. 7).

## Attempt A (paper route, not formalised): saddle/window estimates

`F(X) >= e^{beta x_lo} L(beta)/4` and `F(X) <= e^{beta X} L(beta)` pin `F` only to `e^{o(sqrt X)}`, because
`e^{-beta x}` varies by `e^{eta a/beta}` across a window of relative width `eta`. This is the method of
`ingham_log`; it cannot give constant-factor asymptotics. Concrete obstacle: the weight varies faster than
the window can resolve.

## Attempt B (paper route, not formalised): tilted measures and the Laplace continuity theorem

The tilted measures converge to a Gaussian at scale `beta^{-3/2}` around `a/beta^2`, but `F(x0)` is decided on
the scale `beta^{-1}` (the weight `e^{beta x}` changes by `e^{beta^{-1/2}}` across one Gaussian width), which
needs a local limit theorem. Karamata (14738ca) does not apply: `L(beta(1+s))/L(beta)` is not regularly
varying. Missing in Mathlib: a continuity theorem for Laplace transforms (checked by grep).

## Attempt C (Lean, in progress): the MZ route (Sections 3-5, Appendix A)

Proved in Lean on `pl/sp3`, no `sorry` (files in `Lightlike/Asymptotics/Tauberian/`):

| piece | file | MZ |
|---|---|---|
| exchange `int (int g(t)e^{-itx}dt) e^{-beta x} d sigma = int g(t) L(beta+it) dt` | FourierExchange | (4.3)-(4.4) |
| heavy-operator bound | Hks | (3.3)-(3.4) |
| `sinc` decreasing on `[0,pi]`; majorant `sinc(x)^4/sinc(a)^4 >= 1_{[-a,a]}` | Majorant | (4.1), (4.9) |
| box transform `2b sinc(bx)`; Fourier transform of a convolution; four-fold box kernel `g >= 0`, support `|t| <= 4b`, `ghat = (2b sinc(bx))^4` | Box, BoxConv | (4.9) |
| crossing density `sum a^{k+1}x^k/((k+1)!k!)`: Laplace transform `e^{a/beta}-1` (real and complex `Re z>0`) | Crossing, ComplexLaplace | (2.6), (2.7) |
| upper bound `O(x^{-3/4}e^{2 sqrt(ax)})` (central binomial bound, AM-GM) | CrossingBound | (2.6) |
| sharp asymptotics `crossingDensity ~ 2a e^z sqrt(pi/2)/(pi z sqrt z)` (Laplace's method, Wallis integrals) | BesselAsymp, BesselSeries | (2.6) |
| tangent-line bound; main-term integral `O(Delta^{-3/4} e^{2 sqrt(a Delta)})` | LocalBound | (5.10)-(5.17) |
| window bound and Fourier representation for a positive measure | Window2 | (4.1)-(4.4) |

Still to do, with the concrete difficulty of each (no piece is claimed missing from Mathlib unless
stated):

1. Hypotheses: DONE in Lean (`Vacuum.lean`, `vacuum_gap_of_modular`). MZ's printed form
   `Z(beta) = e^{pi^2 c/3beta}(1 + O(e^{-Delta_1/beta}))` plus real modular invariance `Z(beta) = Z(4 pi^2/beta)`
   gives, for a positive measure with `Z` finite: no mass below `-v` (`no_mass_below`), a vacuum atom of mass 1
   at `-v` (`atom_eq_one`, dominated convergence) and no mass in `(-v, -v + g/(4 pi^2))` (`no_mass_gap`).
   So the theorem can take MZ's printed hypothesis; no difference of kind arises from this step.
2. The remainder estimate (5.19): `|Z(z) - e^{a/z}| <= Z'(4 pi^2 Re z/|z|^2)` from complex modular invariance
   and positivity, and the HKS bound for `Z'` over all `beta' > 0` (heavy/light split).
3. The contour functional (5.3)-(5.7) with kernel `G(nu)` (Appendix A). Mathlib has the Cauchy integral
   theorem on rectangles (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`); a pole on the
   contour at `z = 0` has no residue calculus. Workaround to try first: subtract the principal part so the
   integrand is analytic, or indent the contour.
4. Assembly (5.8)-(5.19) and the constant `(1/2 pi)(3/(c Delta))^{1/4}` from the sharp Bessel asymptotics.

Searched in the pinned Mathlib and Physlib (grep): Beurling-Selberg extremal functions, Wiener-Ikehara
theorem (docstring mention only), Fejer kernel, modified Bessel `I_1` (only `Complex.besselJ`, 2026, no
asymptotics), inverse Laplace transform. All absent; the first three were bypassed by the explicit kernel
above, `I_1` by the series/Wallis route.

## Difference of kind to name if only part lands

Without the full (1.8): "no error estimate and hypotheses of the real-axis type" would be a
`weaker` difference against MZ (1.8); BJM Theorem 4.1 (sector bound) is a different, incomparable
hypothesis set. Neither is claimed closed.
