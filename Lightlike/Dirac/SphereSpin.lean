import Mathlib
import Lightlike.Spacetime.RoundSphereTwo
import Lightlike.Spacetime.RoundSphereTwoCoord
import Lightlike.Dirac.SpinStructure
import Lightlike.Spacetime.StereoConformal

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

/-! ## Conformality of the two maps -/

/-- The vector of `ℝ³` with coordinates `a, b, c`. -/
abbrev vec3 (a b c : ℝ) : EuclideanSpace ℝ (Fin (2 + 1)) := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![a, b, c]

@[simp] lemma vec3_apply0 (a b c : ℝ) : vec3 a b c 0 = a := rfl
@[simp] lemma vec3_apply1 (a b c : ℝ) : vec3 a b c 1 = b := rfl
@[simp] lemma vec3_apply2 (a b c : ℝ) : vec3 a b c 2 = c := rfl

lemma inner_vec3 (a b c a' b' c' : ℝ) :
    inner ℝ (vec3 a b c) (vec3 a' b' c') = a * a' + b * b' + c * c' := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, vec3, mul_comm]

/-- `ξ ↦ (ξ₀, ε ξ₁, 0)`, an isometry of `ℝ²` onto the plane `x₂ = 0`. -/
def Wpl (ε : ℝ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin (2 + 1)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ => vec3 (ξ 0) (ε * ξ 1) 0
      map_add' := fun ξ ξ' => by ext i; fin_cases i <;> simp [vec3] <;> ring
      map_smul' := fun c ξ => by ext i; fin_cases i <;> simp [vec3] <;> ring }

lemma Wpl_apply (ε : ℝ) (ξ : EuclideanSpace ℝ (Fin 2)) : Wpl ε ξ = vec3 (ξ 0) (ε * ξ 1) 0 := rfl

lemma inner_Wpl {ε : ℝ} (hε : ε * ε = 1) (ξ ξ' : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (Wpl ε ξ) (Wpl ε ξ') = inner ℝ ξ ξ' := by
  rw [Wpl_apply, Wpl_apply, inner_vec3]
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  linear_combination (ξ 1 * ξ' 1) * hε

lemma inner_Wpl_pole (ε σ : ℝ) (ξ : EuclideanSpace ℝ (Fin 2)) : inner ℝ (Wpl ε ξ) (vec3 0 0 σ) = 0 := by
  rw [Wpl_apply, inner_vec3]; ring

lemma modelEquiv2_symm_apply (y : Fin 2 → ℝ) (i : Fin 2) : modelEquiv2.symm y i = y i := rfl

lemma norm_sq_modelEquiv2_symm (y : Fin 2 → ℝ) : ‖modelEquiv2.symm y‖ ^ 2 = nsq y := by
  rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two, modelEquiv2_symm_apply, nsq]

/-- `stereoNE` is the library's `stereoMap` for the plane `x₂ = 0`, the north pole, at `2y`. -/
lemma stereoNE_eq (y : Fin 2 → ℝ) :
    stereoNE y = stereoMap (Wpl 1) (vec3 0 0 1) ((2 : ℝ) • modelEquiv2.symm y) := by
  have hq := nsq_nonneg y
  have hn : ‖(2 : ℝ) • modelEquiv2.symm y‖ ^ 2 = 4 * nsq y := by
    rw [norm_smul, mul_pow, norm_sq_modelEquiv2_symm]; norm_num
  unfold stereoMap
  rw [hn]
  ext i
  fin_cases i <;>
    simp [stereoNE, Wpl_apply, vec3, modelEquiv2_symm_apply] <;> field_simp <;> ring

/-- `stereoSE` is `stereoMap` for the plane `x₂ = 0` with the second axis reversed, the south pole, at `2y`. -/
lemma stereoSE_eq (y : Fin 2 → ℝ) :
    stereoSE y = stereoMap (Wpl (-1)) (vec3 0 0 (-1)) ((2 : ℝ) • modelEquiv2.symm y) := by
  have hq := nsq_nonneg y
  have hn : ‖(2 : ℝ) • modelEquiv2.symm y‖ ^ 2 = 4 * nsq y := by
    rw [norm_smul, mul_pow, norm_sq_modelEquiv2_symm]; norm_num
  unfold stereoMap
  rw [hn]
  ext i
  fin_cases i <;>
    simp [stereoSE, Wpl_apply, vec3, modelEquiv2_symm_apply] <;> field_simp <;> ring

/-! ## The round metric on the coordinate vectors -/

/-- The derivative of `stereoNE` (or `stereoSE`) is conformal with factor `4/(|y|²+1)²`. -/
lemma hasFDerivAt_stereoMap_two {ε σ : ℝ} (hε : ε * ε = 1) (hσ : σ * σ = 1) (y : Fin 2 → ℝ) :
    ∃ D : (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (2 + 1)),
      HasFDerivAt (fun y => stereoMap (Wpl ε) (vec3 0 0 σ) ((2 : ℝ) • modelEquiv2.symm y)) D y ∧
        ∀ v w, inner ℝ (D v) (D w) = 4 * ((nsq y + 1)⁻¹) ^ 2 * (v 0 * w 0 + v 1 * w 1) := by
  set L : (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2) := (2 : ℝ) • (modelEquiv2.symm : (Fin 2 → ℝ) →L[ℝ] _)
  obtain ⟨D0, hD0, hDa⟩ := hasFDerivAt_stereoMap (Wpl ε) (vec3 0 0 σ) (L y)
  refine ⟨D0.comp L, hD0.comp y L.hasFDerivAt, fun v w => ?_⟩
  have hv : inner ℝ (vec3 0 0 σ) (vec3 0 0 σ) = 1 := by rw [inner_vec3]; linarith
  have h := inner_stereoMap_deriv (Wpl ε) (inner_Wpl hε) (vec3 0 0 σ) hv (inner_Wpl_pole ε σ) (L y) D0 hDa
    (L v) (L w)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h]
  have hLy : ‖L y‖ ^ 2 = 4 * nsq y := by
    simp only [L, ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe]
    rw [norm_smul, mul_pow, norm_sq_modelEquiv2_symm]; norm_num
  have hLvw : inner ℝ (L v) (L w) = 4 * (v 0 * w 0 + v 1 * w 1) := by
    simp only [L, ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe, inner_smul_left,
      inner_smul_right, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
      modelEquiv2_symm_apply]
    norm_num; ring
  rw [hLy, hLvw]
  have hq := nsq_nonneg y
  field_simp
  ring

/-- **The round metric on the coordinate vectors of a map `ℝ² → S2`** whose composite with the inclusion has
derivative `D`: `g(dσ v, dσ w) = ⟨D v, D w⟩`. -/
lemma roundMetric_mfderiv {σm : (Fin 2 → ℝ) → S2} {y : Fin 2 → ℝ}
    (hσ : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) I2 σm y) {D : (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (2 + 1))}
    (hD : HasFDerivAt (fun y => sphereIncl2 (σm y)) D y) (v w : Fin 2 → ℝ) :
    (roundMetric2I 1 one_ne_zero).g (σm y) (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 σm y v)
      (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 σm y w) = inner ℝ (D v) (D w) := by
  have hι := hasMFDerivAt_transContinuousLinearEquiv modelEquiv2 (hasMFDerivAt_sphereIncl2 (σm y))
  have hc := hι.comp y hσ.hasMFDerivAt
  have hu := hc.mfderiv.symm.trans hD.hasMFDerivAt.mfderiv
  show pullbackForm (I := I2) (radiusForm 1) sphereIncl2 (σm y) _ _ = _
  rw [pullbackForm_apply, radiusForm_apply, one_pow, one_mul, dι_I2, dι_I2]
  have hv : D v = dcoe2 (σm y) (modelEquiv2.symm (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 σm y v)) := by
    rw [← hu]; rfl
  have hw : D w = dcoe2 (σm y) (modelEquiv2.symm (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 σm y w)) := by
    rw [← hu]; rfl
  rw [hv, hw]

lemma roundMetric_stereoN (y v w : Fin 2 → ℝ) :
    (roundMetric2I 1 one_ne_zero).g (stereoN y) (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 stereoN y v)
      (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 stereoN y w) = 4 * ((nsq y + 1)⁻¹) ^ 2 * (v 0 * w 0 + v 1 * w 1) := by
  obtain ⟨D, hD, hDi⟩ := hasFDerivAt_stereoMap_two (ε := 1) (σ := 1) (by norm_num) (by norm_num) y
  have hf : (fun y => sphereIncl2 (stereoN y)) =
      fun y => stereoMap (Wpl 1) (vec3 0 0 1) ((2 : ℝ) • modelEquiv2.symm y) := by
    funext y; exact stereoNE_eq y
  rw [roundMetric_mfderiv (contMDiff_stereoN.mdifferentiableAt (by simp)) (hf ▸ hD), hDi]

lemma roundMetric_stereoS (y v w : Fin 2 → ℝ) :
    (roundMetric2I 1 one_ne_zero).g (stereoS y) (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 stereoS y v)
      (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 stereoS y w) = 4 * ((nsq y + 1)⁻¹) ^ 2 * (v 0 * w 0 + v 1 * w 1) := by
  obtain ⟨D, hD, hDi⟩ := hasFDerivAt_stereoMap_two (ε := -1) (σ := -1) (by norm_num) (by norm_num) y
  have hf : (fun y => sphereIncl2 (stereoS y)) =
      fun y => stereoMap (Wpl (-1)) (vec3 0 0 (-1)) ((2 : ℝ) • modelEquiv2.symm y) := by
    funext y; exact stereoSE_eq y
  rw [roundMetric_mfderiv (contMDiff_stereoS.mdifferentiableAt (by simp)) (hf ▸ hD), hDi]

end Lightlike.Dirac
