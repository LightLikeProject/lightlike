module

public import Lightlike.Spacetime.Minkowski
public import Lightlike.Spacetime.Curvature

/-!
# Curvature in local coordinates; Minkowski space is flat

Mathlib (v4.35) has a Levi-Civita connection for *Riemannian* (positive definite) metrics, but no
curvature tensor and nothing for indefinite metrics. We therefore work in **local coordinates**,
which is how curvature is computed in every GR textbook:

* a *coordinate metric* is a matrix-valued function `g : ℝⁿ → Matrix (Fin n) (Fin n) ℝ`
  (the components `g_{μν}(x)` in a chart);
* `christoffel`, `riemann`, `ricci`, `scalarCurvature` are the standard coordinate formulas
  (Carroll, *Spacetime and Geometry*, eqs. 3.27, 3.67, 3.89, 3.91), with partial derivatives
  given by Mathlib's Fréchet derivative `fderiv`.
* `NondegMetric.coordMetricW g x₀` extracts the coordinate components of a manifold-level
  `LorentzianMetric` in the preferred chart of `M` at `x₀`.

**What is *not* proved here:** that these coordinate expressions transform as tensors under a change
of chart. For Minkowski space this does not matter for the flatness statement below, because the
model-space atlas consists of a single chart (the identity), so "the Riemann tensor vanishes in
every chart of the atlas" is literally what `minkowski_flat` states.

This is the Corners layer of the CO30 branch: the versions for any model with corners of the declarations of
`Lightlike/Spacetime/Curvature.lean` that the CO30 and GE11 files use, with a `W` suffix where the boundaryless file owns the name.
-/

@[expose] public section

open Matrix Manifold Set
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-! ## Coordinate metrics on an open domain

Lean is a total language: `(g x)⁻¹` is the **zero matrix** when `g x` is singular, `a / 0 = 0`, and
`fderiv` is `0` wherever a function is not differentiable. Curvature formulas therefore return
*junk values* (not errors) on degenerate or non-smooth input, and a statement like "the Riemann
tensor vanishes" can be true for meaningless reasons (e.g. for `g = 0`).

All curvature *predicates* below therefore require `IsCoordMetric g U`: `U` open, and on `U` the
matrix `g` is symmetric, invertible, with smooth (`C^∞`) components. Pure formula identities (e.g.
antisymmetry of `riemann` in its last two indices) are stated without these hypotheses because they
hold for every input. -/

/-! ## Constant metrics are flat -/

/-! ## Coordinate components of a manifold-level Lorentzian metric -/

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The components `g_{ij}(y) = g(∂ᵢ, ∂ⱼ)` of a Lorentzian metric in the preferred chart of `M`
at `x₀`, where `∂ᵢ` is the coordinate vector field: the image of the standard basis vector `eᵢ`
under the derivative of the inverse chart. Defined for all `y : ℝⁿ`; meaningful on the chart's
target. -/
def NondegMetric.coordMetricW (g : NondegMetric I M) (x₀ : M)
    (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    g.g ((extChartAt I x₀).symm y)
      (mfderivWithin 𝓘(ℝ, Fin n → ℝ) I (extChartAt I x₀).symm (range I) y (Pi.single i 1))
      (mfderivWithin 𝓘(ℝ, Fin n → ℝ) I (extChartAt I x₀).symm (range I) y (Pi.single j 1))

end Lightlike
