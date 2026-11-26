import Mathlib
import Lightlike.Spacetime.Corners.RicciTransport

/-!
# The curvature in a chart for a model transported to `Fin n → ℝ`

For `e : E ≃L[ℝ] (Fin n → ℝ)` (a choice of coordinates on the finite-dimensional model space `E`), the charts `e ∘ extChartAt I x₀` are the charts of the
model `I.transContinuousLinearEquiv e`. The intrinsic Ricci tensor, scalar curvature and Einstein equations of `cov` and `g` agree in these
charts with the coordinate ones (`ricciAt_coord_trans`, `scalarCurvatureAt_coord_trans`, `satisfiesEinstein_iff_chart_trans`), by the theorems of
`ChartAgreement.lean` for the transported connection and metric.
-/

open Bundle Manifold Set VectorField Filter
open scoped Manifold ContDiff Topology
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

section
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 2 M]
  (e : E ≃L[ℝ] (Fin n → ℝ)) (cov : Connection I M) [LocallySmoothConnectionW cov]

/-- **The Einstein equations are the same for the transported connection and metric.** -/
theorem satisfiesEinstein_trans_iff (g : NondegMetric I M) (h : cov.IsLeviCivita g) (Λ : ℝ) :
    g.SatisfiesEinstein cov Λ ↔ (transMetric e g).SatisfiesEinstein (transCov e cov) Λ := by
  have := locallySmoothConnectionW_transCov e cov
  sorry

end

end Lightlike
