import Mathlib
import Lightlike.Spacetime.RoundSphereTwo
import Lightlike.Spacetime.StereoConformal

/-!
# The stereographic charts of the 2-sphere are conformal

For Mathlib's chart `stereographic' 2 v` of the unit sphere `S²`, the derivative of `u ↦ ↑((stereographic' 2 v).symm u) ∈ ℝ³` pulls
the Euclidean inner product back to `16/(‖u‖²+4)²` times the inner product of `ℝ²` (`inner_fderiv_chartInv2`), the same
statement as `inner_fderiv_chartInv` for `S³`.
-/

open Manifold Metric
open scoped ContDiff RealInnerProductSpace
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

/-- the linear isometry `E2 → E3` onto the orthogonal complement of `v` used by Mathlib's chart `stereographic'` -/
def stereoW2 (v : S2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin (2 + 1)) :=
  (Submodule.subtypeL _).comp
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere v)).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem stereoW2_inner (v : S2) (ξ ξ' : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (stereoW2 v ξ) (stereoW2 v ξ') = inner ℝ ξ ξ' := by
  simp only [stereoW2, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  exact (Submodule.coe_inner _ _ _).symm.trans (LinearIsometryEquiv.inner_map_map _ _ _)

theorem stereoW2_orth (v : S2) (ξ : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (stereoW2 v ξ) (v : EuclideanSpace ℝ (Fin (2 + 1))) = 0 := by
  have h := ((OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere v)).repr.symm ξ).2
  have h2 := (Submodule.mem_orthogonal_singleton_iff_inner_right (𝕜 := ℝ)).1 h
  rw [real_inner_comm] at h2
  simpa [stereoW2] using h2

/-- Mathlib's inverse stereographic chart is `stereoMap` for `W = stereoW2 v`. -/
theorem stereographic_symm_eq2 (v : S2) (u : EuclideanSpace ℝ (Fin 2)) :
    (((stereographic' 2 v).symm u : S2) : EuclideanSpace ℝ (Fin (2 + 1))) =
      stereoMap (stereoW2 v) v u := by
  rw [stereographic'_symm_apply]
  have hn : ‖((OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere v)).repr.symm u :
      EuclideanSpace ℝ (Fin (2 + 1)))‖ = ‖u‖ := by
    rw [Submodule.norm_coe, LinearIsometryEquiv.norm_map]
  simp only [stereoMap, stereoW2, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, hn]
  simp only [smul_smul]

/-- **The inverse stereographic chart of the 2-sphere is conformal**: the pullback of the Euclidean inner product has the
factor `16 / (‖u‖² + 4)²`. -/
theorem inner_fderiv_chartInv2 (v : S2) (u ξ ξ' : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (fderiv ℝ (fun u => (((stereographic' 2 v).symm u : S2) : EuclideanSpace ℝ (Fin (2 + 1)))) u ξ)
      (fderiv ℝ (fun u => (((stereographic' 2 v).symm u : S2) : EuclideanSpace ℝ (Fin (2 + 1)))) u ξ') =
      16 * ((‖u‖ ^ 2 + 4)⁻¹) ^ 2 * inner ℝ ξ ξ' := by
  obtain ⟨D, hD, hDa⟩ := hasFDerivAt_stereoMap (stereoW2 v) (v : EuclideanSpace ℝ (Fin (2 + 1))) u
  have hf : (fun u => (((stereographic' 2 v).symm u : S2) : EuclideanSpace ℝ (Fin (2 + 1)))) =
      stereoMap (stereoW2 v) (v : EuclideanSpace ℝ (Fin (2 + 1))) := by
    funext w; exact stereographic_symm_eq2 v w
  rw [hf, hD.fderiv]
  exact inner_stereoMap_deriv (stereoW2 v) (stereoW2_inner v) (v : EuclideanSpace ℝ (Fin (2 + 1)))
    (by simp [norm_eq_of_mem_sphere v]) (stereoW2_orth v) u D hDa ξ ξ'

end Lightlike
