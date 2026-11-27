import Mathlib
import Lightlike.Spacetime.LaplaceBeltrami.Green
import Lightlike.Spacetime.NondegMetric

/-!
# The Laplace–Beltrami operator of a Riemannian metric is nonnegative

For a smooth Riemannian metric (Mathlib's `Bundle.ContMDiffRiemannianMetric`, as a nondegenerate metric through
`NondegMetric.ofRiemannian`) the inverse coordinate metric is positive definite, so `g⁻¹(df, df) = |df|² ≥ 0`
(`NondegMetric.ofRiemannian_dualPair_self_nonneg`). With Green's identity, on a compact manifold
`∫_M f Δ_g f dvol_g = ∫_M |df|² dvol_g ≥ 0` (`NondegMetric.ofRiemannian_integral_mul_laplaceBeltrami_self_nonneg`): the
Laplacian with the sign convention `Δ = -div grad` is a nonnegative operator, so its eigenvalues are `≥ 0`.
-/

open MeasureTheory Set Manifold Matrix Filter
open scoped ContDiff Topology
noncomputable section
namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  [MeasurableSpace M] [BorelSpace M]
  (hR : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, Fin n → ℝ) ∞ (Fin n → ℝ) (fun x : M => TangentSpace 𝓘(ℝ, Fin n → ℝ) x))

/-- **`|df|² = g⁻¹(df, df) ≥ 0` for a Riemannian metric.** -/
theorem NondegMetric.ofRiemannian_dualPair_self_nonneg (f : M → ℝ) (x : M) :
    0 ≤ (NondegMetric.ofRiemannian hR).dualPair f f x := by
  unfold NondegMetric.dualPair
  rw [NondegMetric.dualPairCoord_eq_dotProduct]
  have hpd := (NondegMetric.ofRiemannian_coordMetric_posDef hR x (mem_extChartAt_target x)).inv
  simpa [star_trivial] using hpd.posSemidef.dotProduct_mulVec_nonneg
    (fun i => coordPartial x f (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) i)

variable [CompactSpace M]

/-- **The Laplace–Beltrami operator of a Riemannian metric on a compact manifold is nonnegative**:
`∫_M f Δ_g f dvol_g = ∫_M |df|² dvol_g ≥ 0`. -/
theorem NondegMetric.ofRiemannian_integral_mul_laplaceBeltrami_self_nonneg {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f) :
    0 ≤ ∫ x, f x * (NondegMetric.ofRiemannian hR).laplaceBeltrami f x ∂(NondegMetric.ofRiemannian hR).volumeMeasure := by
  rw [(NondegMetric.ofRiemannian hR).integral_mul_laplaceBeltrami hf hf]
  exact integral_nonneg fun x => NondegMetric.ofRiemannian_dualPair_self_nonneg hR f x

end Lightlike
