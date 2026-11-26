import Mathlib
import Lightlike.Spacetime.RoundSphereTwo
import Lightlike.Spacetime.RoundSphereTwoCoord
import Lightlike.Dirac.SpinStructure

/-!
# The spin structure of the unit 2-sphere

The library's unit 2-sphere `S2` (Mathlib's `sphere (0 : ℝ³) 1` with the transported model `I2` on
`Fin 2 → ℝ`) with the round metric `roundMetric2I 1`. This file builds the frames of its spin structure
(`sphereSpinStructure`, in progress) from two explicit inverse stereographic maps into the sphere:

* `stereoN y = (2y₀, 2y₁, |y|²-1)/(|y|²+1)`, the inverse of the projection from the north pole
  `N = (0,0,1)`, onto `S2 ∖ {N}`;
* `stereoS y = (2y₀, -2y₁, 1-|y|²)/(|y|²+1)`, from the south pole with the second axis reversed, onto
  `S2 ∖ {S}`, so that the transition `stereoS⁻¹ ∘ stereoN (y) = (y₀, -y₁)/|y|²` (`z ↦ 1/z`) preserves the
  orientation.

Mathlib's own charts (`stereographic'`) are not used for the frames: they compose with an orthonormal basis of
`(ℝ ∙ v)ᗮ` chosen by `OrthonormalBasis.fromOrthogonalSpanSingleton`, so their transition carries an unspecified
orthogonal matrix. Mathlib's atlas enters only through the smooth structure (`mfderiv`, `TangentSpace I2`).

## Main definitions (this layer)

* `stereoNE`, `stereoSE`: the two maps into `ℝ³`; `stereoNE_mem`, `stereoSE_mem`: they land on the sphere;
* `stereoN`, `stereoS`: the same as maps into `S2`, smooth for the model `I2` (`contMDiff_stereoN`, `contMDiff_stereoS`).
-/

open Bundle Manifold Metric
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Dirac

/-- `|y|²` for `y ∈ ℝ²`. -/
def nsq (y : Fin 2 → ℝ) : ℝ := y 0 ^ 2 + y 1 ^ 2

lemma nsq_nonneg (y : Fin 2 → ℝ) : 0 ≤ nsq y := by unfold nsq; positivity

/-- The inverse stereographic map from the north pole, as a map into `ℝ³`. -/
def stereoNE (y : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin (2 + 1)) :=
  (nsq y + 1)⁻¹ • (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![2 * y 0, 2 * y 1, nsq y - 1]

/-- The inverse stereographic map from the south pole, with the second axis reversed, into `ℝ³`. -/
def stereoSE (y : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin (2 + 1)) :=
  (nsq y + 1)⁻¹ • (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![2 * y 0, -(2 * y 1), 1 - nsq y]

lemma norm_sq_vec3 (a b c : ℝ) :
    ‖(WithLp.equiv 2 (Fin 3 → ℝ)).symm ![a, b, c]‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]

lemma stereoNE_mem (y : Fin 2 → ℝ) : stereoNE y ∈ sphere (0 : EuclideanSpace ℝ (Fin (2 + 1))) 1 := by
  have hq := nsq_nonneg y
  rw [mem_sphere_zero_iff_norm, stereoNE, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (by linarith : (0 : ℝ) < nsq y + 1)]
  have h : ‖(WithLp.equiv 2 (Fin 3 → ℝ)).symm ![2 * y 0, 2 * y 1, nsq y - 1]‖ = nsq y + 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (by linarith), norm_sq_vec3]
    unfold nsq; ring
  rw [h, inv_mul_cancel₀ (by linarith)]

lemma stereoSE_mem (y : Fin 2 → ℝ) : stereoSE y ∈ sphere (0 : EuclideanSpace ℝ (Fin (2 + 1))) 1 := by
  have hq := nsq_nonneg y
  rw [mem_sphere_zero_iff_norm, stereoSE, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (by linarith : (0 : ℝ) < nsq y + 1)]
  have h : ‖(WithLp.equiv 2 (Fin 3 → ℝ)).symm ![2 * y 0, -(2 * y 1), 1 - nsq y]‖ = nsq y + 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (by linarith), norm_sq_vec3]
    unfold nsq; ring
  rw [h, inv_mul_cancel₀ (by linarith)]

lemma contDiff_stereoNE : ContDiff ℝ ∞ stereoNE := by
  unfold stereoNE nsq
  have hd : ContDiff ℝ ∞ (fun y : Fin 2 → ℝ => y 0 ^ 2 + y 1 ^ 2 + 1) := by fun_prop
  refine (hd.inv fun y => by positivity).smul ?_
  exact (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toContinuousLinearEquiv.contDiff.comp
    (contDiff_pi.2 fun i => by fin_cases i <;> simp <;> fun_prop)

lemma contDiff_stereoSE : ContDiff ℝ ∞ stereoSE := by
  unfold stereoSE nsq
  have hd : ContDiff ℝ ∞ (fun y : Fin 2 → ℝ => y 0 ^ 2 + y 1 ^ 2 + 1) := by fun_prop
  refine (hd.inv fun y => by positivity).smul ?_
  exact (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toContinuousLinearEquiv.contDiff.comp
    (contDiff_pi.2 fun i => by fin_cases i <;> simp <;> fun_prop)

/-- `stereoN : ℝ² → S2`. -/
def stereoN (y : Fin 2 → ℝ) : S2 := ⟨stereoNE y, stereoNE_mem y⟩

/-- `stereoS : ℝ² → S2`. -/
def stereoS (y : Fin 2 → ℝ) : S2 := ⟨stereoSE y, stereoSE_mem y⟩

lemma contMDiff_stereoN : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) I2 ∞ stereoN := by
  rw [ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right]
  exact (contDiff_stereoNE.contMDiff).codRestrict_sphere stereoNE_mem

lemma contMDiff_stereoS : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) I2 ∞ stereoS := by
  rw [ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right]
  exact (contDiff_stereoSE.contMDiff).codRestrict_sphere stereoSE_mem

end Lightlike.Dirac
