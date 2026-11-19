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

## Attempt D (Lean): the pole-free smoothing route (replaces item 3, the contour functional)

Why the contour route was dropped: the Dirichlet integral / Cauchy-Fourier pair for `1/(beta + it)`
on the real line and a residue formula for a pole on a segment are not in the pinned Mathlib (grep:
`Dirichlet`, `sinc` integral, `residue`). Replacement, all proved in Lean:

* smoothed step `psi(y) = (1/N) int_{u<y} e^{beta u} kappa(u) du`, `kappa(u) = (2b sinc(bu))^4`
  (`Psi.lean`); `int g(t)/(beta+it) e^{-ity} dt = int_0^infty e^{-beta s} kappa(y+s) ds` by Fubini and
  `1/(beta+it) = int_0^infty e^{-(beta+it)s} ds` (`Smoothing.lean`, `fourier_inv_eq`, `smooth_representation`):
  no inversion theorem and no pole;
* `N psi(Delta - x) = e^{beta Delta} e^{-beta x} Psi(x - Delta)`; difference of two smoothed counting
  functions `<= e^{beta Delta} 16 b^4 M/(N beta)` when the Laplace transforms differ by `<= M` on `|t| <= 4b`
  (`Difference.lean`);
* comparison of a measure with its smoothing at `beta = sqrt(a/Delta)`: pointwise error bound for `psi`
  (first-order term in `beta` cancels by `int u kappa = 0`; `Psi.lean`, `Compare.lean`), outer region by
  Markov against `e^{-beta x}`, inner region by unit windows against the local bound with the tangent-line
  bound `2 sqrt(a(Delta-k)) <= 2 sqrt(a Delta) - beta k` (`Inner.lean`, `Assembly.lean`, `Tangent.lean`,
  `WindowWeights.lean`, `CompareAsymp.lean`); size `Delta^{-3/4} e^{2 sqrt(a Delta)}`, MZ's order;
* distribution function of the crossing measure `rho_0(-inf,x] = sum (ax)^m/(m!)^2 = I_0(2 sqrt(ax))`
  (`Rho0Cdf.lean`, `BesselI0.lean`), local bound for `rho_0` (`Rho0Local.lean`), effective Laplace method for
  `I_0` with relative error `O(1/s)` (`LaplaceEff.lean`: comparison with the Gaussian,
  `1 - cos >= 2 theta^2/pi^2`, `theta^2/2 - (1-cos) <= theta^4/2`);
* assembly `cardy_counting` (`CardyCounting.lean`): `|sigma(-inf,Delta] - I_0(2 sqrt(a Delta))| <= K Delta^{-3/4}
  e^{2 sqrt(a Delta)}`; with `besselI0_eff` this is MZ (1.8) with the relative error `O(Delta^{-1/2})`.

## Comparison of `cardy_mz` with the source (read 19 November 2026, arXiv:1904.06359v1, pdftotext)

Locations (printed page numbers of v1): the Theorem with eq. (1.8), p. 7; modular invariance (2.2), its
integral form (2.3) and the density of states (2.4), p. 8; the crossing kernel (2.6) and its Laplace
transform (2.7), p. 9; the proof, (5.1) = (1.8) restated, p. 15, the estimates (5.8)-(5.17), pp. 17-19,
and the remainder (5.18)-(5.19), pp. 19-20.

* (1.8): `F(Δ) = ∫₀^Δ dΔ' ρ(Δ') = (1/2π) (3/(cΔ))^{1/4} e^{2π√(cΔ/3)} [1 + O(Δ^{-1/2})]`, `Δ → ∞`, for a positive
  `ρ` with `Z(β) = ∫₀^∞ dΔ e^{-β(Δ - c/12)} ρ(Δ)` modular invariant, `Z(β) = Z(4π²/β)` (for `Re β > 0`, (2.2)),
  and `Z(β) = e^{π²c/(3β)}(1 + O(e^{-Δ₁/β}))`, `Δ₁ > 0`, as `|β| → 0` with `Re β > 0`.
* `cardy_mz` (CardyRelative.lean): `|F(Δ) · √(4π√(aΔ)) e^{-2√(aΔ)} - 1| ≤ K Δ^{-1/2}` for `Δ ≥ Δ₁`, with
  `F(Δ) = σ(-∞, Δ - v]`, `v = c/12`, `a = 4π²v = π²c/3`. Since `2√(aΔ) = 2π√(cΔ/3)` and
  `√(4π√(aΔ)) = 2π(cΔ/3)^{1/4}`, this is (1.8) with an explicit constant in the `O`.
* Hypotheses (`SpectralHyp` + `hmodC`): `Z(β)` finite for `β > 0`; `Z(z) = Z(4π²/z)` for `Re z > 0` (= (2.2));
  `|Z(β) - e^{a/β}| ≤ C e^{(a-g)/β}` for real `0 < β < β₀` (= the high-temperature form with `g = Δ₁`, but only
  on the real axis); the real modular invariance field is implied by (2.2).
* Difference (kind representation; reported to the maintainers 19 Nov, decision pending): `σ` is a positive
  measure in the shifted variable `x = Δ - c/12` instead of the density `ρ(Δ) = Σ_O δ(Δ - Δ_O)` of (2.4);
  `F(Δ) = σ(-∞, Δ - v]`; the main term is written `√(4π√(aΔ)) e^{-2√(aΔ)} = 2π(cΔ/3)^{1/4} e^{-2π√(cΔ/3)}`.
* Not a difference: assuming the high-temperature form only for real `β → 0⁺` is a weaker hypothesis than MZ's
  (complex `β`, `|β| → 0`), so the formal theorem is stronger; named in the docstring.
* `cardy_counting` (CardyCounting.lean) is the step of Section 5: `F_σ - F_{ρ₀} = O(x^{-3/4} e^{2√(a x)})` with the
  crossing kernel `ρ₀` of (2.6) (atom at `x = 0`, density `√(a/x) I₁(2√(a x))`; `laplaceC_rho0` = (2.7)), and
  `F_{ρ₀}(x) = I₀(2√(a x))` (`rho0_real_Iic`). MZ bound the remainder (5.19) with the contour functional; route D
  replaces it by the pole-free smoothing above.
* Non-vacuity: `σ = δ_{-v} + ρ₀` (CardyExample.lean) satisfies all hypotheses; its counting function is
  `1 + I₀(2√(a x))` exactly (`exampleSpectrum_real_Iic`, trust check).

## Difference of kind to name if only part lands

Without the full (1.8): "no error estimate and hypotheses of the real-axis type" would be a
`weaker` difference against MZ (1.8); BJM Theorem 4.1 (sector bound) is a different, incomparable
hypothesis set. Neither is claimed closed.
