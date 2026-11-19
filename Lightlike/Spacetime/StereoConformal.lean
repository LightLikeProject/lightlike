import Mathlib
import Lightlike.Spacetime.FLRWSphere
import Lightlike.Spacetime.Corners.ChartCurvature

/-!
# The inverse stereographic chart of the 3-sphere is conformal (CO30, attempt 1)

For Mathlib's chart `stereographic' 3 v` of the unit sphere, the derivative of `u ↦ ↑((stereographic' 3 v).symm u) ∈ ℝ⁴` pulls the Euclidean inner
product back to `16/(‖u‖²+4)²` times the inner product of `ℝ³` (`inner_fderiv_chartInv`): in these coordinates the round metric is `|du|²/(1+|u|²/4)²`,
the spatial part of the FLRW metric with `k = 1`.

**Limits.** The derivative of the chart only; the coordinate metric of `J × S³` is a separate step.
-/

open Manifold Metric
open scoped ContDiff RealInnerProductSpace
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- the inverse stereographic map in the form `u ↦ q⁻¹ (4 W u + (‖u‖² − 4) v)`, `q = ‖u‖² + 4` -/
def stereoMap (W : F →L[ℝ] V) (v : V) (u : F) : V :=
  (‖u‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • W u) + ((‖u‖ ^ 2 + 4)⁻¹ * (‖u‖ ^ 2 - 4)) • v

/-- the derivative of `stereoMap`, applied to a vector -/
theorem hasFDerivAt_stereoMap (W : F →L[ℝ] V) (v : V) (u : F) :
    ∃ D : F →L[ℝ] V, HasFDerivAt (stereoMap W v) D u ∧ ∀ ξ,
      D ξ = (4 * (‖u‖ ^ 2 + 4)⁻¹) • W ξ - (8 * ⟪u, ξ⟫ * ((‖u‖ ^ 2 + 4)⁻¹) ^ 2) • W u
        + (16 * ⟪u, ξ⟫ * ((‖u‖ ^ 2 + 4)⁻¹) ^ 2) • v := by
  have hn : HasFDerivAt (fun x : F => ‖x‖ ^ 2) (2 • innerSL ℝ u) u := (hasStrictFDerivAt_norm_sq u).hasFDerivAt
  have hq : HasFDerivAt (fun x : F => ‖x‖ ^ 2 + 4) (2 • innerSL ℝ u) u := hn.add_const 4
  have hqne : ‖u‖ ^ 2 + 4 ≠ 0 := by positivity
  have hi : HasFDerivAt (fun x : F => (‖x‖ ^ 2 + 4)⁻¹) ((-((‖u‖ ^ 2 + 4) ^ 2)⁻¹) • (2 • innerSL ℝ u)) u :=
    (hasDerivAt_inv hqne).comp_hasFDerivAt u hq
  have hm : HasFDerivAt (fun x : F => ‖x‖ ^ 2 - 4) (2 • innerSL ℝ u) u := hn.sub_const 4
  have hA : HasFDerivAt (fun x : F => (4 : ℝ) • W x) ((4 : ℝ) • W) u := (W.hasFDerivAt).const_smul 4
  have h1 := hi.smul hA
  have h3 := (hi.mul hm).smul_const v
  refine ⟨_, h1.add h3, fun ξ => ?_⟩
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    FunLike.coe_sub, Pi.sub_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  have e3 : (‖u‖ ^ 2 + 4)⁻¹ * (2 * ⟪u, ξ⟫) + (‖u‖ ^ 2 - 4) * (-((‖u‖ ^ 2 + 4) ^ 2)⁻¹ * (2 * ⟪u, ξ⟫)) =
      16 * ⟪u, ξ⟫ * ((‖u‖ ^ 2 + 4)⁻¹) ^ 2 := by
    field_simp; ring
  have e2 : (-((‖u‖ ^ 2 + 4) ^ 2)⁻¹ * (2 * ⟪u, ξ⟫)) * 4 = -(8 * ⟪u, ξ⟫ * ((‖u‖ ^ 2 + 4)⁻¹) ^ 2) := by
    field_simp; ring
  simp only [Nat.cast_ofNat]
  rw [e3, smul_smul, smul_smul, mul_comm ((‖u‖ ^ 2 + 4)⁻¹) 4, e2, neg_smul]
  abel

/-- **The derivative of the inverse stereographic map is conformal**: `⟪D ξ, D ξ'⟫ = 16/(‖u‖²+4)² ⟪ξ, ξ'⟫`. -/
theorem inner_stereoMap_deriv (W : F →L[ℝ] V) (hW : ∀ ξ ξ', ⟪W ξ, W ξ'⟫ = ⟪ξ, ξ'⟫) (v : V) (hv : ⟪v, v⟫ = 1)
    (hWv : ∀ ξ, ⟪W ξ, v⟫ = 0) (u : F) (D : F →L[ℝ] V)
    (hD : ∀ ξ, D ξ = (4 * (‖u‖ ^ 2 + 4)⁻¹) • W ξ - (8 * ⟪u, ξ⟫ * ((‖u‖ ^ 2 + 4)⁻¹) ^ 2) • W u
        + (16 * ⟪u, ξ⟫ * ((‖u‖ ^ 2 + 4)⁻¹) ^ 2) • v) (ξ ξ' : F) :
    ⟪D ξ, D ξ'⟫ = 16 * ((‖u‖ ^ 2 + 4)⁻¹) ^ 2 * ⟪ξ, ξ'⟫ := by
  have hvW : ∀ ξ, ⟪v, W ξ⟫ = 0 := fun ξ => by rw [real_inner_comm]; exact hWv ξ
  have hnu : ‖u‖ ^ 2 = ⟪u, u⟫ := (real_inner_self_eq_norm_sq u).symm
  rw [hD ξ, hD ξ']
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hW, hWv, hvW, hv, RCLike.conj_to_real]
  rw [real_inner_comm ξ u, real_inner_comm ξ' u]
  simp only [← hnu]
  have hq : ‖u‖ ^ 2 + 4 ≠ 0 := by positivity
  field_simp
  ring


/-- the linear isometry `E3 → E4` onto the orthogonal complement of `v` used by Mathlib's chart `stereographic'` -/
def stereoW (v : S3) : EuclideanSpace ℝ (Fin 3) →L[ℝ] E4 :=
  (Submodule.subtypeL _).comp
    (OrthonormalBasis.fromOrthogonalSpanSingleton 3 (ne_zero_of_mem_unit_sphere v)).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem stereoW_inner (v : S3) (ξ ξ' : EuclideanSpace ℝ (Fin 3)) : inner ℝ (stereoW v ξ) (stereoW v ξ') = inner ℝ ξ ξ' := by
  simp only [stereoW, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  exact (Submodule.coe_inner _ _ _).symm.trans (LinearIsometryEquiv.inner_map_map _ _ _)

theorem stereoW_orth (v : S3) (ξ : EuclideanSpace ℝ (Fin 3)) : inner ℝ (stereoW v ξ) (v : E4) = 0 := by
  have h := ((OrthonormalBasis.fromOrthogonalSpanSingleton 3 (ne_zero_of_mem_unit_sphere v)).repr.symm ξ).2
  have h2 := (Submodule.mem_orthogonal_singleton_iff_inner_right (𝕜 := ℝ)).1 h
  rw [real_inner_comm] at h2
  simpa [stereoW] using h2


/-- Mathlib's inverse stereographic chart is `stereoMap` for `W = stereoW v`. -/
theorem stereographic_symm_eq (v : S3) (u : EuclideanSpace ℝ (Fin 3)) :
    (((stereographic' 3 v).symm u : S3) : E4) = stereoMap (stereoW v) v u := by
  rw [stereographic'_symm_apply]
  have hn : ‖((OrthonormalBasis.fromOrthogonalSpanSingleton 3 (ne_zero_of_mem_unit_sphere v)).repr.symm u : E4)‖ = ‖u‖ := by
    rw [Submodule.norm_coe, LinearIsometryEquiv.norm_map]
  simp only [stereoMap, stereoW, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, hn]
  simp only [smul_smul]

/-- **The inverse stereographic chart of the sphere is conformal**: the pullback of the Euclidean inner product has the factor
`16 / (‖u‖² + 4)²`. -/
theorem inner_fderiv_chartInv (v : S3) (u ξ ξ' : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (fderiv ℝ (fun u => (((stereographic' 3 v).symm u : S3) : E4)) u ξ)
      (fderiv ℝ (fun u => (((stereographic' 3 v).symm u : S3) : E4)) u ξ') =
      16 * ((‖u‖ ^ 2 + 4)⁻¹) ^ 2 * inner ℝ ξ ξ' := by
  obtain ⟨D, hD, hDa⟩ := hasFDerivAt_stereoMap (stereoW v) (v : E4) u
  have hf : (fun u => (((stereographic' 3 v).symm u : S3) : E4)) = stereoMap (stereoW v) (v : E4) := by
    funext w; exact stereographic_symm_eq v w
  rw [hf, hD.fderiv]
  exact inner_stereoMap_deriv (stereoW v) (stereoW_inner v) (v : E4) (by simp [norm_eq_of_mem_sphere v])
    (stereoW_orth v) u D hDa ξ ξ'

end Lightlike
