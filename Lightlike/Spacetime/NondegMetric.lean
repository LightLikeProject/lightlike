import Lightlike.Spacetime.Coordinates
import Lightlike.Spacetime.NondegMetricBase

/-!
# Smooth symmetric nondegenerate bilinear fields on a manifold (general metrics)

`NondegMetric I M` is a smooth section `g` of the bundle of bilinear forms on the tangent bundle, symmetric and
nondegenerate at every point: a pseudo-Riemannian metric of any signature. The two cases of the library are
corollaries: a Lorentzian metric (`NondegMetric.ofLorentzian`) and a smooth Riemannian metric of Mathlib
(`NondegMetric.ofRiemannian`). For a manifold modelled on `ℝⁿ`, `NondegMetric.coordMetric` is the matrix of
components in a chart, with the proofs that it is symmetric (`coordMetric_transpose`), invertible
(`coordMetric_isUnit_det`) and smooth (`coordMetric_smooth`) on the chart target, as for Lorentzian metrics
(`LorentzianMetric.coordMetric` is the same expression: `ofLorentzian_coordMetric`). The volume measure of a
general metric is in `VolumeMeasure.lean`.

The structure has the same smoothness field as `LorentzianMetric` and Mathlib's `ContMDiffRiemannianMetric`.
-/

open Bundle Manifold Matrix
open scoped ContDiff

noncomputable section
namespace Lightlike



section Coordinates

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- **For a Riemannian metric the coordinate matrix is positive definite** on the chart target. -/
theorem NondegMetric.ofRiemannian_coordMetric_posDef
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, Fin n → ℝ) ∞ (Fin n → ℝ) (fun x : M => TangentSpace 𝓘(ℝ, Fin n → ℝ) x))
    (x₀ : M) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    ((NondegMetric.ofRiemannian h).coordMetric x₀ y).PosDef := by
  set g := NondegMetric.ofRiemannian h with hg
  set p := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y with hpdef
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  set b := coordBasis x₀ hp with hb
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · have := g.coordMetric_transpose x₀ y
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · have hv : (∑ i, x i • b i) ≠ 0 := fun h0 => hx (funext fun i => by
      simpa using Fintype.linearIndependent_iff.1 b.linearIndependent x h0 i)
    have hpos := h.pos p _ hv
    have e1 : star x ⬝ᵥ ((g.coordMetric x₀ y) *ᵥ x) = h.inner p (∑ i, x i • b i) (∑ j, x j • b j) := by
      simp only [dotProduct, Matrix.mulVec, map_sum, ContinuousLinearMap.sum_apply, map_smul,
        ContinuousLinearMap.smul_apply, smul_eq_mul, g.coordMetric_eq x₀ hy, Finset.mul_sum, star_trivial]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hs := h.symm p (coordBasis x₀ hp j) (coordBasis x₀ hp i)
      rw [hs]
      change x i * (h.inner p (coordBasis x₀ hp i) (coordBasis x₀ hp j) * x j) = _
      ring
    rw [e1]; exact hpos

/-- **For a Riemannian metric the volume density is `√(det g)`** (the determinant is positive). -/
theorem NondegMetric.ofRiemannian_abs_det
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, Fin n → ℝ) ∞ (Fin n → ℝ) (fun x : M => TangentSpace 𝓘(ℝ, Fin n → ℝ) x))
    (x₀ : M) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    |((NondegMetric.ofRiemannian h).coordMetric x₀ y).det| = ((NondegMetric.ofRiemannian h).coordMetric x₀ y).det :=
  abs_of_pos (NondegMetric.ofRiemannian_coordMetric_posDef h x₀ hy).det_pos

end Coordinates

end Lightlike
