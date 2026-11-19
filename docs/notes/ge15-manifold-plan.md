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
`S = ∫ dⁿx √(−g) (R − 2Λ)`, pp. 117 to 118) was located but not re-read for this note; regge's note
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
  (the coordinate theorem is used unchanged), and locality.
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

`ManifoldVariation.lean` compiles (19 November 2026): `eh_first_variation_manifold_chart`. For a metric `g`
on `M`, a compact `K` inside one chart domain with chart image in a small coordinate ball, and a family `g_t`
of metrics with Levi-Civita connections whose chart components are `g + t h` near the image of `K`
(`h` smooth, symmetric, supported in the image of `K`): the intrinsic action
`S(t) = ∫_K (R(g_t) − 2Λ) d vol_{g_t}` has derivative `−∫ √|g| (R^{αβ} − ½ R g^{αβ} + Λ g^{αβ}) h_{αβ}` at
`t = 0`. This is Carroll's (4.66) (with `Λ`, and with the metric perturbed instead of its inverse) for a
variation supported in one small coordinate ball; the left side is intrinsic, the right side is written in the
components of the chart.

Differences from Carroll that remain: (a) the family `g_t`, its Levi-Civita connections and the
measurability of the integrand are hypotheses (data), not constructed from a tensor field `h` on `M`;
(b) the perturbation is supported in one small coordinate ball; (c) the right side is in chart components,
not `∫ (G^{μν} + Λ g^{μν}) h_{μν} d vol_g`; (d) no "critical if and only if `G + Λ g = 0`" on the manifold.

## Status after the tensor-field form (19 November 2026)

All files of `Lightlike/Spacetime/EHManifold/` compile, with no `sorry`.

* `eh_first_variation_manifold` (`TensorVariation.lean`): for a metric `g` and a smooth symmetric bilinear
  field `h` (`SymBilinField`) that vanishes outside a compact `K` inside one chart domain, with chart image in
  a small coordinate ball, `d/dt ehAction (g.perturb h t) Λ K = −∫ √|g| (R^{αβ} − ½ R g^{αβ} + Λ g^{αβ}) h_{αβ}`
  at `t = 0`. Here `ehAction g Λ K = ∫_K (R − 2Λ) d vol_g` with the Levi-Civita connection of `g`
  (`leviCivita g`), and `g.perturb h t = g + t h` (a metric for small `t`:
  `NondegMetric.exists_addSmul_nondegenerate`, `SmallT.lean`). The family, its connections and the
  measurability are no longer hypotheses.
* `isEHCriticalOnBall_iff` (`BallCriticalConverse.lean`): a coordinate metric on a ball is critical for all
  perturbations supported in the smaller ball if and only if the symmetric part of
  `R^{αβ} − ½ R g^{αβ} + Λ g^{αβ}` vanishes on the smaller ball (Carroll (4.67) with `Λ`, in coordinates).

Differences from Carroll (4.54) to (4.67) that remain: (b) the perturbation is supported in one small
coordinate ball; (c) the right side is in chart components; (d) the "critical if and only if" is proved for
coordinate metrics on a ball, not yet stated for the manifold action `ehAction`.

## Status after the intrinsic form (19 November 2026)

| Formal statement (Lean) | Source (Carroll, gr-qc/9712019, ch. 4) | Match |
| --- | --- | --- |
| `eh_first_variation_manifold_intrinsic` (`IntrinsicVariation.lean`): for a metric `g` on `M` and a smooth symmetric tensor field `h` vanishing outside a compact `K` inside a small coordinate ball of one chart, `d/dt ehAction (g + t h) Λ K = −∫_K ⟨G + Λ g, h⟩_g d vol_g` at `t = 0` | (4.66), p. 116: `δS = ∫ dⁿx √−g [R_{μν} − ½ R g_{μν}] δg^{μν}` | weaker. Convention: the metric is varied, not its inverse (`δg^{μν} = −g^{μα} g^{νβ} δg_{αβ}`), hence the sign; `Λ` is added; any signature. Weaker: the perturbation is supported in one small coordinate ball, not in an arbitrary compact set |
| `eh_first_variation_manifold_eq_zero` (`ManifoldCritical.lean`), `isEHCriticalOnBall_iff` (`BallCriticalConverse.lean`) | (4.67), p. 116: stationary points of the action are the solutions of Einstein's equation | weaker. On the manifold only "Einstein's equation implies stationary" (for the perturbations above); the equivalence is proved for coordinate metrics on a ball |

`ehAction g Λ K = ∫_K (R − 2Λ) d vol_g` (Levi-Civita connection and volume measure of `g`);
`ehIntegrand g h Λ p = ⟨G + Λ g, h⟩_g (p)` is the contraction with the inverse metric, defined with
`formContract` (basis independent: `formContract_basis_indep`) and the Einstein form `einsteinBilin`.
Both sides of the first statement are intrinsic; charts appear only in the hypothesis on the support.

Open: (c) a perturbation with arbitrary compact support. First step done: `eh_variation_piece`
(`PieceVariation.lean`), the variation of the density over a measurable piece with the divergence of the
flux (`ehFluxDiv`) kept. Still needed: chart independence of the flux divergence, and a partition of unity.

## Status after the compact-support form (19 November 2026)

| Formal statement (Lean) | Source (Carroll, gr-qc/9712019, ch. 4) | Match |
| --- | --- | --- |
| `eh_first_variation_manifold_compact` (`CompactVariation.lean`): for a metric `g` of any signature on `M` and a smooth symmetric tensor field `h` vanishing outside a compact set `K`, `d/dt ehAction (g + t h) Λ K = −∫_K ⟨G + Λ g, h⟩_g d vol_g` at `t = 0` | (4.66), p. 116: `δS = ∫ dⁿx √−g [R_{μν} − ½ R g_{μν}] δg^{μν}` | match. Convention: the metric is varied, not its inverse (`δg^{μν} = −g^{μα} g^{νβ} δg_{αβ}`), hence the sign. Representation: the action is the integral over a compact set `K` containing the support of the perturbation (the action over all of `M` need not converge); `Λ` is added |
| `isEHStationary_iff_einstein` (`EinsteinIntrinsic.lean`), `isEHStationary_iff` (`ManifoldStationary.lean`) | (4.67), p. 116: stationary points of the action are the solutions of Einstein's equation | match (see the section on (4.73), (4.74) below for the statement with `Λ`) |

How the compact-support form is proved (no chart independence of the Palatini flux is used): `K` is cut
into finitely many disjoint measurable pieces, each in a small coordinate ball; over a piece the derivative
of the action is the chart integral of the Einstein term plus the divergence of the flux
(`hasDerivAt_ehAction_piece`, `pieceVar`); this formula is additive in `h` (`pieceVar_sum`,
`ehFluxDiv_sum`); `h = ∑ ρ_i h` for a smooth partition of unity (Mathlib's
`SmoothPartitionOfUnity.exists_isSubordinate`); and for each `ρ_i h`, supported in one small ball, the
formula equals `−∫ ⟨G + Λ g, ρ_i h⟩` by `eh_first_variation_manifold_intrinsic` and the uniqueness of the
derivative (`eh_first_variation_of_cover`).

The converse "stationary implies Einstein's equation" is proved with test tensor fields `η (E_ab + E_ba)`
built from chart data (`SymBilinField.ofChart`, `testField`) and the fundamental lemma of the calculus of
variations on an open set.

## Catalogue draft (for the maintainers; `docs/results.yaml` is not edited here)

To be used only once the files compile and the gate is green.

* LL-XXXX-h. **First variation of the Einstein–Hilbert action on a manifold.**
  `Lightlike.eh_first_variation_manifold_compact` (`Lightlike/Spacetime/EHManifold/CompactVariation.lean`).
  For a pseudo-Riemannian metric `g` on a smooth manifold and a smooth symmetric tensor field `h` vanishing
  outside a compact set `K`: `d/dt|₀ ∫_K (R(g + t h) − 2Λ) d vol_{g + t h} = −∫_K ⟨G + Λ g, h⟩_g d vol_g`.
  Source: Carroll, gr-qc/9712019, ch. 4, (4.66), p. 116 (read). Differences: convention (metric varied, not
  its inverse); representation (action over a compact set containing the support); `Λ` added; any signature.
* LL-XXXX-i. **Stationary points of the Einstein–Hilbert action are the solutions of Einstein's equation.**
  `Lightlike.isEHStationary_iff` (`Lightlike/Spacetime/EHManifold/ManifoldStationary.lean`).
  Source: Carroll, ibid., (4.67), p. 116 (read). Difference: representation (Einstein's equation is stated in
  the components of every chart, as the vanishing of the symmetric part of `R^{αβ} − ½ R g^{αβ} + Λ g^{αβ}`).

## The cosmological constant: Carroll (4.73), (4.74), p. 118 (read 19 November 2026)

Carroll's text: "We therefore consider an action given by `S = ∫ dⁿx √−g (R − 2Λ)` (4.73), where `Λ` is
some constant. The resulting field equations are `R_{μν} − ½ R g_{μν} + Λ g_{μν} = 0` (4.74)".

| Formal statement (Lean) | Source | Match |
| --- | --- | --- |
| `isEHStationary_iff_einstein` (`EinsteinIntrinsic.lean`): `g` is a stationary point of `ehAction · Λ` (`∫_K (R − 2Λ) d vol_g`, for every perturbation of compact support) if and only if `G(u, v) + Λ g(u, v) = 0` for all tangent vectors at all points, `G = Ric − ½ R g` for the Levi-Civita connection | (4.73), (4.74), p. 118 | match, including the sign of `Λ`. Representation: the action is taken over compact sets containing the support of the perturbation; any signature and dimension |
| `isEHStationary_iff_ricci`: for `n ≠ 2`, stationary iff `Ric = (2Λ/(n − 2)) g` | not in Carroll at this place; algebraic consequence (trace of (4.74)), from `satisfiesEinstein_iff_ricci` | corollary |

So the statements with `Λ` are compared with (4.73), (4.74), and those with `Λ = 0` with (4.66), (4.67).

## Matter: Carroll (4.68) to (4.70), p. 116 (read)

Carroll: `S = S_H / (8πG) + S_M` (4.68); "`(1/√−g) δS/δg^{μν} = (1/8πG)(R_{μν} − ½ R g_{μν}) +
(1/√−g) δS_M/δg^{μν} = 0`" (4.69); "we recover Einstein's equations if we can set
`T_{μν} = −(1/√−g) δS_M/δg^{μν}`" (4.70).

| Formal statement (Lean) | Source | Match |
| --- | --- | --- |
| `total_action_stationary_iff` (`MatterEinstein.lean`): if `SM` has the energy-momentum tensor `T` at `g` (`HasMatterVariation`: `d/dt SM (g + t h) = ∫_K ⟨T, h⟩_g d vol_g` for every `h` vanishing outside the compact `K`) and `κ ≠ 0`, then `ehAction · Λ K / κ + SM` is stationary at `g` for all such `h`, `K` if and only if `G(u, v) + Λ g(u, v) = κ T(u, v)` at every point | (4.68) to (4.70) with `κ = 8πG` | match. Convention: the metric is varied, not its inverse, so (4.70) reads `δS_M = +∫ ⟨T, δg⟩ d vol`. Representation: the matter action is an arbitrary function of the metric with a prescribed first variation (no matter fields); `Λ` is included; actions over compact sets |
