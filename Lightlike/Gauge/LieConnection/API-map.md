# Gauge transformations for a general Lie group

## Abstract (Alpha)

This API treats the local gauge potential of a general Lie group `G` (Mathlib's `LieGroup`, modelled on a real Banach
space without boundary), with values in its Lie algebra `GroupLieAlgebra`, following Svetlichny's *Preparation for
Gauge Theory*: the adjoint action, the curvature with the Lie bracket, the gauge transformation
`A' = Ad_g A - dg g⁻¹` (eq. (38)) and the covariance `F' = Ad_g F` of the curvature (eq. (64)) for a gauge
transformation that varies with the point.

## Content (Alpha)

The adjoint action `Ad_g = d(conj_g)_1` preserves the bracket, and the curvature `F = dA + ⁅A, A⁆` of a Lie-algebra
valued one-form transforms as `F ↦ Ad_g F` under a constant `g` [1] {1}. In the chart at the identity the
multiplication is `C³`, the bracket is the antisymmetrised mixed second derivative of the chart multiplication, and
`D(Ad)_1 = ad` [2] [3]. Along a path in the chart, the derivative of the adjoint action is `Da + ⁅Dγ, a⁆` and the
right Maurer–Cartan form `dg g⁻¹` satisfies `dθ = ⁅θ, θ⁆` [4]. The gauge transform of a potential by `g`,
`A' = Ad_g A - dg g⁻¹` (eq. (38)), has curvature `Ad_g F` (eq. (64)) for every `C²` gauge transformation [5] {1}.
Principal bundles and the gluing of local potentials (Theorem 10) are in the connection API [TODO].

## Lean References

1. Lightlike/Gauge/LieConnection/LieGroup.lean - `Gauge.adjoint`, `Gauge.adjoint_lie`, `Gauge.lieCurvature`,
   `Gauge.lieCurvature_adjoint`
2. Lightlike/Gauge/LieConnection/LieGroupChart.lean - `Gauge.contDiffAt_chartMul`, `Gauge.bracket_eq_chart`,
   `Gauge.fderiv_adjoint_chart`
3. Lightlike/Gauge/LieConnection/ChartCalculus.lean - `Gauge.fderiv_conj_chart`
4. Lightlike/Gauge/LieConnection/ChartGauge.lean - `Gauge.fderiv_conjApply_chart`, `Gauge.maurerCartan_chart`
5. Lightlike/Gauge/LieConnection/LieGroupGauge.lean - `Gauge.rightMCForm`, `Gauge.lieGaugeTransform`,
   `Gauge.rightMCForm_eq_chart`, `Gauge.lieCurvature_lieGaugeTransform_of_chart`, `Gauge.rightMCForm_mul_left`,
   `Gauge.lieCurvature_lieGaugeTransform`

## References

1. G. Svetlichny, Preparation for Gauge Theory, arXiv:math-ph/9902027 (1999), §4.6 p. 30 (eq. (38)) and pp. 42-43
   (eqs. (62)-(64)).
