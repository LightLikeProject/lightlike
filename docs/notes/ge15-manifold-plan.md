# GE15 on a manifold: sources read and plan

Stream fable2, branch `fable2/ge15-manifold` (from `regge/ge15` 44bc02e), started 19 November 2026.
regge proved the first variation of the Einstein–Hilbert action in coordinates on `ℝⁿ`
(`eh_first_variation`, `isEHCritical_iff`); this branch is to state and prove it on a manifold.

## Source read

S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 4, pp. 114 to 116 of the
arXiv PDF (text read on 19 November 2026):

* (4.54) `S_H = ∫ dⁿx L_H`; (4.55) `L_H = √(−g) R`.
* (4.56) `δS = ∫ dⁿx [√(−g) g^{μν} δR_{μν} + √(−g) R_{μν} δg^{μν} + R δ√(−g)] = (δS)₁ + (δS)₂ + (δS)₃`.
* (4.57) to (4.60): `δR^ρ_{μλν} = ∇_λ(δΓ^ρ_{νμ}) − ∇_ν(δΓ^ρ_{λμ})`.
* (4.61): `(δS)₁ = ∫ dⁿx √(−g) ∇_σ[g^{μσ} δΓ^λ_{λμ} − g^{μν} δΓ^σ_{μν}]`, "by Stokes's theorem, this is equal to
  a boundary contribution at infinity which we can set to zero by making the variation vanish at infinity".
* (4.62) to (4.65): `δ√(−g) = −½ √(−g) g_{μν} δg^{μν}`.
* (4.66): `δS = ∫ dⁿx √(−g) (R_{μν} − ½ R g_{μν}) δg^{μν}`; (4.67): `R_{μν} − ½ R g_{μν} = 0`.

Carroll varies the inverse metric `δg^{μν}` and writes the integral with `dⁿx` and `√(−g)`, the natural volume
element of the metric on the manifold. Equation (4.73) (the action with a cosmological constant,
`S = ∫ dⁿx √(−g) (R − 2Λ)`, pp. 117 to 118) was located but not re-read by this stream; regge's note
(`docs/notes/ge15-carroll-comparison.md` on `regge/ge15` at 5a58787, read) compares it.

## What exists (read at 44bc02e)

* `Lightlike/Spacetime/VariationIntegral.lean`: `eh_first_variation` for `g h : (Fin n → ℝ) → Matrix`, smooth,
  symmetric, `det g ≠ 0` everywhere, `T` compact containing `tsupport h`:
  `HasDerivAt (fun t => ∫ x in T, lagDensity g h Λ t x) (−∫ x in T, √|det g| ∑ h_{αβ} (R^{αβ} − ½ R g^{αβ} + Λ g^{αβ})) 0`.
* `Lightlike/Spacetime/VolumeMeasure.lean`: `NondegMetric.volDensity g x₀ y = √|det (g.coordMetric x₀ y)|`,
  `NondegMetric.volumeMeasure`, and `NondegMetric.volumeMeasure_chart`: for a measurable `A` inside the source
  of the chart at `x₀`, `volumeMeasure g A = ∫⁻ y in extChartAt x₀ '' A, ofReal (volDensity g x₀ y)`.
* `Lightlike/Spacetime/ChartAgreement.lean`: `scalarCurvatureAt_coord`: for a Levi-Civita connection `cov` of
  `g`, `cov.scalarCurvatureAt g ((extChartAt x₀).symm y) = scalarCurvature (g.coordMetric x₀) y`.

## Plan

1. **One chart.** For a compact `K` inside the source of the chart at `x₀`, and a one-parameter family of
   metrics `g_t` with Levi-Civita connections, whose components in that chart are
   `coordMetric g x₀ + t h` with `h` supported in the image of `K`: the action
   `S(t) = ∫_K (R(g_t) − 2Λ) d vol_{g_t}` (integral for `NondegMetric.volumeMeasure`) equals the chart integral
   of regge's `lagDensity`, by `volumeMeasure_chart` and `scalarCurvatureAt_coord`; then `eh_first_variation`
   gives its derivative at `t = 0`. Open point: regge's theorem asks for a metric on all of `ℝⁿ` with
   `det ≠ 0` everywhere, while a chart gives components only on the chart target; either extend the
   components outside a neighbourhood of the image of `K`, or use a version of the theorem local to an open
   set (to be asked of regge).
2. **Compact support in general.** Cover the support of the perturbation by finitely many charts and use a
   smooth partition of unity; the first variation is linear in the perturbation (the pointwise derivative
   of the Lagrangian density is linear in `h` and its derivatives), so it is the sum of the one-chart
   variations. This needs the pointwise derivative formula inside regge's proof as a lemma.
3. **Critical points.** `G + Λ g = 0` if and only if the variation vanishes for all compactly supported
   perturbations, chart by chart from `isEHCritical_iff`.

Later, as separate pieces: the boundary term when the perturbation does not vanish at the boundary; `f(R)`
gravity; the sign of `Λ` as a trust check.

Difference from the source already known (kind: representation): Carroll varies the inverse metric and
states the result for arbitrary variations vanishing at infinity; here the metric is perturbed as `g + t h`
with `h` of compact support, as in regge's chart theorem.

## Status (19 November 2026)

Compiled, in `Lightlike/Spacetime/EHManifold/`:

* `Locality.lean`: `christoffel_eventuallyEq`, `riemann_congr`, `ricci_congr`, `scalarCurvature_congr`: the
  coordinate curvature at a point depends only on the germ of the metric there.
* `Retraction.lean`: `ballRetract φ x = c + φ x • (x − c)` for a smooth bump `φ`; smooth, into the ball of
  radius `φ.rOut`, the identity on the ball of radius `φ.rIn`.
* `BallVariation.lean`: `eh_first_variation_ball`: regge's first-variation formula for a coordinate metric
  that is smooth, symmetric and nondegenerate only on a ball, and a perturbation supported in a compact set
  inside the smaller concentric ball. Proof: `eh_first_variation` for the metric composed with the retraction
  (route (c) of the integrator; regge's theorem is used unchanged), and locality.
* `ChartVariation.lean`: `eh_first_variation_chart`: the same formula for the chart components
  `g.coordMetric x₀` of a metric `g` on a manifold, when the larger ball lies in the target of the chart.
* `ChartAction.lean`: `NondegMetric.volumeMeasure_restrict_chart`: on a measurable `K` inside one chart
  domain, the volume measure is the image under the inverse chart of `√|det g| dy`.

Not done (this is still weaker than Carroll's statement on a manifold): the intrinsic form, in which the
action is `∫_K (R − 2Λ) d vol_g` for the volume measure of `M` and the scalar curvature of the Levi-Civita
connection (to be obtained from `volumeMeasure_restrict_chart` and `scalarCurvatureAt_coord`); perturbations
whose support is not inside one small coordinate ball (partition of unity; needs the additivity of the
first variation); and the equivalence "critical if and only if `G + Λ g = 0`" on the manifold.

Added after that status (19 November 2026): `IntrinsicAction.lean` compiles.
`NondegMetric.setIntegral_volumeMeasure_chart` (`∫_K f d vol_g = ∫_{φ(K)} √|det g| · (f ∘ φ⁻¹) dy` for a
measurable `K` inside one chart domain) and `eh_action_chart` (for a Levi-Civita connection of `g`:
`∫_K (R − 2Λ) d vol_g` equals the chart integral of `lagDensity (g.coordMetric x₀) 0 Λ 0` over the chart image
of `K`). So the intrinsic action of one metric is identified with regge's coordinate density. Still open for
(i): the same identification along a family `g_t` whose chart components are `g + t h` (then
`eh_first_variation_chart` gives the derivative of the intrinsic action); (ii) and (iii) as above.
