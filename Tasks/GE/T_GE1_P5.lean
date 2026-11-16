import Lightlike.Spacetime.Connection
import Lightlike.GR.Einstein

/-!
# Task T-GE1-P5

The intrinsic scalar curvature is the coordinate scalar curvature in every chart.

The statement is `Lightlike.scalarCurvatureAt_chart`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. In the chart the coordinate vector fields `∂ᵢ` have vanishing brackets and `∇_{∂ᵢ} ∂ⱼ = Γᵏᵢⱼ ∂ₖ` for the Levi-Civita connection (Koszul formula); then the coordinate formula of `Curvature.lean` is the trace of `curvatureAt`. Fixes the sign convention of the two definitions.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* Lightlike/Spacetime/Connection.lean: `Connection.scalarCurvatureAt`; Lightlike/Spacetime/Curvature.lean: `scalarCurvature`; Lightlike/Spacetime/Coordinates.lean: `LorentzianMetric.coordMetric`

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.scalarCurvatureAt_chart

## References

Milestone GE1 (smooth curvature from connections), ROADMAP section "Lorentzian and Riemannian geometry".
Structural: statement of the manifold-level theory of `Lightlike/Spacetime/Connection.lean`; the
conventions are those of Mathlib pull request 45069 for the curvature sign and signature `(-,+,…,+)`.
Reference for the content: Carroll, Spacetime and Geometry (2004), Chapter 3 (eqs. 3.4 and 3.113); not yet a verified location in docs/tasks/sources.yaml.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle
open scoped Manifold ContDiff

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 1 M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]

/-- **Agreement with the coordinate curvature.** For the Levi-Civita connection of a Lorentzian
metric on a manifold modelled on `ℝⁿ`, the intrinsic scalar curvature at a point of a chart is the
coordinate `scalarCurvature` of the chart components. -/
theorem scalarCurvatureAt_chart (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (h : cov.IsLeviCivita g) (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    cov.scalarCurvatureAt g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) =
      scalarCurvature (g.coordMetric x₀) y := by
  sorry

end Lightlike
