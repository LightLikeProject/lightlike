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

/-! ## The inverse maps -/

/-- The `i`-th coordinate of a point of `S2` in `ℝ³`. -/
abbrev pc (p : S2) (i : Fin (2 + 1)) : ℝ := (p : EuclideanSpace ℝ (Fin (2 + 1))) i

lemma pc_sq_sum (p : S2) : pc p 0 ^ 2 + pc p 1 ^ 2 + pc p 2 ^ 2 = 1 := by
  have h := norm_eq_of_mem_sphere p
  have h2 : ‖(p : EuclideanSpace ℝ (Fin (2 + 1)))‖ ^ 2 = 1 := by rw [h]; simp
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three] at h2
  simpa [pc] using h2

/-- The stereographic projection from the north pole, `p ↦ (p₀, p₁)/(1 - p₂)`. -/
def invN (p : S2) : Fin 2 → ℝ := ![pc p 0 / (1 - pc p 2), pc p 1 / (1 - pc p 2)]

/-- The stereographic projection from the south pole with the second axis reversed,
`p ↦ (p₀, -p₁)/(1 + p₂)`. -/
def invS (p : S2) : Fin 2 → ℝ := ![pc p 0 / (1 + pc p 2), -(pc p 1) / (1 + pc p 2)]

lemma pc_stereoN (y : Fin 2 → ℝ) :
    pc (stereoN y) 0 = 2 * y 0 / (nsq y + 1) ∧ pc (stereoN y) 1 = 2 * y 1 / (nsq y + 1) ∧
      pc (stereoN y) 2 = (nsq y - 1) / (nsq y + 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [pc, stereoN, stereoNE, div_eq_inv_mul]

lemma pc_stereoS (y : Fin 2 → ℝ) :
    pc (stereoS y) 0 = 2 * y 0 / (nsq y + 1) ∧ pc (stereoS y) 1 = -(2 * y 1) / (nsq y + 1) ∧
      pc (stereoS y) 2 = (1 - nsq y) / (nsq y + 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [pc, stereoS, stereoSE, div_eq_inv_mul]

lemma invN_stereoN (y : Fin 2 → ℝ) : invN (stereoN y) = y := by
  obtain ⟨h0, h1, h2⟩ := pc_stereoN y
  have hq := nsq_nonneg y
  have hd : 1 - (nsq y - 1) / (nsq y + 1) = 2 / (nsq y + 1) := by field_simp; ring
  ext k; fin_cases k <;> simp [invN, h0, h1, h2, hd] <;> field_simp

lemma invS_stereoS (y : Fin 2 → ℝ) : invS (stereoS y) = y := by
  obtain ⟨h0, h1, h2⟩ := pc_stereoS y
  have hq := nsq_nonneg y
  have hd : 1 + (1 - nsq y) / (nsq y + 1) = 2 / (nsq y + 1) := by field_simp; ring
  ext k; fin_cases k <;> simp [invS, h0, h1, h2, hd] <;> field_simp

lemma stereoN_invN {p : S2} (hp : pc p 2 ≠ 1) : stereoN (invN p) = p := by
  have hs := pc_sq_sum p
  have h1 : 1 - pc p 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  have hq : nsq (invN p) + 1 = 2 / (1 - pc p 2) := by
    simp only [nsq, invN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    field_simp; nlinarith
  apply Subtype.ext
  ext i
  fin_cases i
  · show (nsq (invN p) + 1)⁻¹ * (2 * invN p 0) = pc p 0
    rw [hq]; simp [invN]; field_simp
  · show (nsq (invN p) + 1)⁻¹ * (2 * invN p 1) = pc p 1
    rw [hq]; simp [invN]; field_simp
  · show (nsq (invN p) + 1)⁻¹ * (nsq (invN p) - 1) = pc p 2
    rw [show nsq (invN p) - 1 = (nsq (invN p) + 1) - 2 by ring, hq]; field_simp; ring

lemma stereoS_invS {p : S2} (hp : pc p 2 ≠ -1) : stereoS (invS p) = p := by
  have hs := pc_sq_sum p
  have h1 : 1 + pc p 2 ≠ 0 := by intro h; exact hp (by linarith)
  have hq : nsq (invS p) + 1 = 2 / (1 + pc p 2) := by
    simp only [nsq, invS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    field_simp; nlinarith
  apply Subtype.ext
  ext i
  fin_cases i
  · show (nsq (invS p) + 1)⁻¹ * (2 * invS p 0) = pc p 0
    rw [hq]; simp [invS]; field_simp
  · show (nsq (invS p) + 1)⁻¹ * -(2 * invS p 1) = pc p 1
    rw [hq]; simp [invS]; field_simp
  · show (nsq (invS p) + 1)⁻¹ * (1 - nsq (invS p)) = pc p 2
    rw [show 1 - nsq (invS p) = 2 - (nsq (invS p) + 1) by ring, hq]; field_simp; ring

/-! ## Smoothness of the projections -/

lemma contMDiff_sphereIncl2_I2 : ContMDiff I2 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 + 1))) ∞ sphereIncl2 := by
  rw [ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left]; exact contMDiff_sphereIncl2

/-- The projection from the north pole in `ℝ³` coordinates. -/
def projNE (z : EuclideanSpace ℝ (Fin (2 + 1))) : Fin 2 → ℝ := ![z 0 / (1 - z 2), z 1 / (1 - z 2)]

/-- The projection from the south pole (second axis reversed) in `ℝ³` coordinates. -/
def projSE (z : EuclideanSpace ℝ (Fin (2 + 1))) : Fin 2 → ℝ := ![z 0 / (1 + z 2), -(z 1) / (1 + z 2)]

lemma contDiffAt_projNE {z : EuclideanSpace ℝ (Fin (2 + 1))} (hz : z 2 ≠ 1) : ContDiffAt ℝ ∞ projNE z := by
  have hd : (1 : ℝ) - z 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hc : ∀ i : Fin (2 + 1), ContDiff ℝ ∞ fun w : EuclideanSpace ℝ (Fin (2 + 1)) => w i := fun i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin (2 + 1)) →L[ℝ] ℝ).contDiff
  refine contDiffAt_pi.2 fun k => ?_
  fin_cases k
  · exact ((hc 0).contDiffAt).div ((contDiff_const.sub (hc 2)).contDiffAt) hd
  · exact ((hc 1).contDiffAt).div ((contDiff_const.sub (hc 2)).contDiffAt) hd

lemma contDiffAt_projSE {z : EuclideanSpace ℝ (Fin (2 + 1))} (hz : z 2 ≠ -1) : ContDiffAt ℝ ∞ projSE z := by
  have hd : (1 : ℝ) + z 2 ≠ 0 := fun h => hz (by linarith)
  have hc : ∀ i : Fin (2 + 1), ContDiff ℝ ∞ fun w : EuclideanSpace ℝ (Fin (2 + 1)) => w i := fun i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin (2 + 1)) →L[ℝ] ℝ).contDiff
  refine contDiffAt_pi.2 fun k => ?_
  fin_cases k
  · exact ((hc 0).contDiffAt).div ((contDiff_const.add (hc 2)).contDiffAt) hd
  · exact ((hc 1).neg.contDiffAt).div ((contDiff_const.add (hc 2)).contDiffAt) hd

lemma contMDiffAt_invN {p : S2} (hp : pc p 2 ≠ 1) : ContMDiffAt I2 𝓘(ℝ, Fin 2 → ℝ) ∞ invN p :=
  (contDiffAt_projNE hp).contMDiffAt.comp p contMDiff_sphereIncl2_I2.contMDiffAt

lemma contMDiffAt_invS {p : S2} (hp : pc p 2 ≠ -1) : ContMDiffAt I2 𝓘(ℝ, Fin 2 → ℝ) ∞ invS p :=
  (contDiffAt_projSE hp).contMDiffAt.comp p contMDiff_sphereIncl2_I2.contMDiffAt

/-! ## The frames -/

/-- The orthonormal frame vector `a` at `stereoN y`: `((|y|²+1)/2) dσN(eₐ)`. -/
def fN (a : Fin 2) (y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ((nsq y + 1) / 2) • (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 stereoN y (Pi.single a 1) : Fin 2 → ℝ)

/-- The orthonormal frame vector `a` at `stereoS y`. -/
def fS (a : Fin 2) (y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ((nsq y + 1) / 2) • (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 stereoS y (Pi.single a 1) : Fin 2 → ℝ)

/-- The north frame on `S2`, meaningful on `S2 ∖ {N}`. -/
def frameN (a : Fin 2) (p : S2) : TangentSpace I2 p := fN a (invN p)

/-- The south frame on `S2`, meaningful on `S2 ∖ {S}`. -/
def frameS (a : Fin 2) (p : S2) : TangentSpace I2 p := fS a (invS p)

lemma roundMetric_fN (y : Fin 2 → ℝ) (a b : Fin 2) :
    (roundMetric2I 1 one_ne_zero).g (stereoN y) (fN a y) (fN b y) = if a = b then 1 else 0 := by
  have hq := nsq_nonneg y
  unfold fN
  rw [map_smul, map_smul, ContinuousLinearMap.smul_apply, roundMetric_stereoN]
  have hab : ((Pi.single a 1 : Fin 2 → ℝ) 0 * (Pi.single b 1 : Fin 2 → ℝ) 0 +
      (Pi.single a 1 : Fin 2 → ℝ) 1 * (Pi.single b 1 : Fin 2 → ℝ) 1) = if a = b then 1 else 0 := by
    fin_cases a <;> fin_cases b <;> simp
  rw [hab, smul_eq_mul, smul_eq_mul]
  split_ifs <;> field_simp <;> ring

lemma roundMetric_fS (y : Fin 2 → ℝ) (a b : Fin 2) :
    (roundMetric2I 1 one_ne_zero).g (stereoS y) (fS a y) (fS b y) = if a = b then 1 else 0 := by
  have hq := nsq_nonneg y
  unfold fS
  rw [map_smul, map_smul, ContinuousLinearMap.smul_apply, roundMetric_stereoS]
  have hab : ((Pi.single a 1 : Fin 2 → ℝ) 0 * (Pi.single b 1 : Fin 2 → ℝ) 0 +
      (Pi.single a 1 : Fin 2 → ℝ) 1 * (Pi.single b 1 : Fin 2 → ℝ) 1) = if a = b then 1 else 0 := by
    fin_cases a <;> fin_cases b <;> simp
  rw [hab, smul_eq_mul, smul_eq_mul]
  split_ifs <;> field_simp <;> ring

lemma frameN_orthonormal {p : S2} (hp : pc p 2 ≠ 1) (a b : Fin 2) :
    (roundMetric2I 1 one_ne_zero).g p (frameN a p) (frameN b p) = if a = b then 1 else 0 := by
  have h := roundMetric_fN (invN p) a b
  rwa [stereoN_invN hp] at h

lemma frameS_orthonormal {p : S2} (hp : pc p 2 ≠ -1) (a b : Fin 2) :
    (roundMetric2I 1 one_ne_zero).g p (frameS a p) (frameS b p) = if a = b then 1 else 0 := by
  have h := roundMetric_fS (invS p) a b
  rwa [stereoS_invS hp] at h

/-! ## Smoothness of the frames -/

lemma totalSpace_mk_eq_of_eq {q q' : S2} (h : q = q') (v : Fin 2 → ℝ) :
    (⟨q, v⟩ : TangentBundle I2 S2) = ⟨q', v⟩ := by subst h; rfl

lemma isOpen_pc_ne (c : ℝ) : IsOpen {q : S2 | pc q 2 ≠ c} :=
  isOpen_ne_fun ((EuclideanSpace.proj (2 : Fin (2 + 1))).continuous.comp continuous_subtype_val)
    continuous_const

/-- The pushforward `p ↦ dσ_{τ p}(v)` of a constant vector by a smooth map `σ : ℝ² → S2` with a smooth local
inverse `τ`, as a section of the tangent bundle, is smooth wherever `σ ∘ τ = id` near the point. -/
lemma contMDiffAt_pushforward {σm : (Fin 2 → ℝ) → S2} (hσ : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) I2 ∞ σm)
    {τ : S2 → Fin 2 → ℝ} {p : S2} (hτ : ContMDiffAt I2 𝓘(ℝ, Fin 2 → ℝ) ∞ τ p)
    (hinv : ∀ᶠ q in nhds p, σm (τ q) = q) (v : Fin 2 → ℝ) :
    ContMDiffAt I2 (I2.prod 𝓘(ℝ, Fin 2 → ℝ)) ∞
      (fun q => (⟨q, (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 σm (τ q) v : Fin 2 → ℝ)⟩ : TangentBundle I2 S2)) p := by
  have hT := hσ.contMDiff_tangentMap (m := ∞) (by simp)
  have hin : ContMDiffAt I2 (𝓘(ℝ, Fin 2 → ℝ)).tangent ∞
      (fun q => (⟨τ q, v⟩ : TangentBundle 𝓘(ℝ, Fin 2 → ℝ) (Fin 2 → ℝ))) p := by
    rw [Bundle.contMDiffAt_totalSpace]
    refine ⟨hτ, ?_⟩
    simpa [TangentBundle.trivializationAt_apply, mfld_simps] using contMDiffAt_const
  refine (hT.contMDiffAt.comp p hin).congr_of_eventuallyEq ?_
  filter_upwards [hinv] with q hq
  exact totalSpace_mk_eq_of_eq hq.symm _

lemma frameN_smooth (a : Fin 2) {p : S2} (hp : pc p 2 ≠ 1) :
    ContMDiffAt I2 (I2.prod 𝓘(ℝ, Fin 2 → ℝ)) ∞ (fun q => (⟨q, frameN a q⟩ : TangentBundle I2 S2)) p := by
  have hinv : ∀ᶠ q in nhds p, stereoN (invN q) = q := by
    filter_upwards [(isOpen_pc_ne 1).mem_nhds hp] with q hq using stereoN_invN hq
  have hX := contMDiffAt_pushforward contMDiff_stereoN (contMDiffAt_invN hp) hinv (Pi.single a 1)
  have hc : ContMDiffAt I2 𝓘(ℝ, ℝ) ∞ (fun q => (nsq (invN q) + 1) / 2) p := by
    have h := contMDiffAt_invN hp
    have hq : ContDiff ℝ ∞ (fun y : Fin 2 → ℝ => (nsq y + 1) / 2) := by unfold nsq; fun_prop
    exact hq.contMDiff.contMDiffAt.comp p h
  exact hc.smul_section hX

lemma frameS_smooth (a : Fin 2) {p : S2} (hp : pc p 2 ≠ -1) :
    ContMDiffAt I2 (I2.prod 𝓘(ℝ, Fin 2 → ℝ)) ∞ (fun q => (⟨q, frameS a q⟩ : TangentBundle I2 S2)) p := by
  have hinv : ∀ᶠ q in nhds p, stereoS (invS q) = q := by
    filter_upwards [(isOpen_pc_ne (-1)).mem_nhds hp] with q hq using stereoS_invS hq
  have hX := contMDiffAt_pushforward contMDiff_stereoS (contMDiffAt_invS hp) hinv (Pi.single a 1)
  have hc : ContMDiffAt I2 𝓘(ℝ, ℝ) ∞ (fun q => (nsq (invS q) + 1) / 2) p := by
    have h := contMDiffAt_invS hp
    have hq : ContDiff ℝ ∞ (fun y : Fin 2 → ℝ => (nsq y + 1) / 2) := by unfold nsq; fun_prop
    exact hq.contMDiff.contMDiffAt.comp p h
  exact hc.smul_section hX

/-! ## The frame vectors in `ℝ³` and the frame change -/

/-- `dι (dσ w) = D w` for a map `σ : ℝ² → S2` whose composite with the inclusion has derivative `D`. -/
lemma dι_mfderiv {σm : (Fin 2 → ℝ) → S2} {y : Fin 2 → ℝ}
    (hσ : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) I2 σm y) {D : (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (2 + 1))}
    (hD : HasFDerivAt (fun y => sphereIncl2 (σm y)) D y) (w : Fin 2 → ℝ) :
    dι (I := I2) sphereIncl2 (σm y) (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 σm y w) = D w := by
  have hι := hasMFDerivAt_transContinuousLinearEquiv modelEquiv2 (hasMFDerivAt_sphereIncl2 (σm y))
  have hu := (hι.comp y hσ.hasMFDerivAt).mfderiv.symm.trans hD.hasMFDerivAt.mfderiv
  rw [dι_I2, ← hu]; rfl

/-- The north frame vector `a` at `stereoN y` in `ℝ³`: `W eₐ − (2yₐ/(q+1)) W y + (2yₐ/(q+1)) N`. -/
def FrN (a : Fin 2) (y : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin (2 + 1)) :=
  vec3 ((Pi.single a 1 : Fin 2 → ℝ) 0 - 2 * y a * y 0 / (nsq y + 1))
    ((Pi.single a 1 : Fin 2 → ℝ) 1 - 2 * y a * y 1 / (nsq y + 1)) (2 * y a / (nsq y + 1))

/-- The south frame vector `a` at `stereoS y` in `ℝ³`. -/
def FrS (a : Fin 2) (y : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin (2 + 1)) :=
  vec3 ((Pi.single a 1 : Fin 2 → ℝ) 0 - 2 * y a * y 0 / (nsq y + 1))
    (-((Pi.single a 1 : Fin 2 → ℝ) 1 - 2 * y a * y 1 / (nsq y + 1))) (-(2 * y a / (nsq y + 1)))

lemma dι_fStereo {ε σ : ℝ} (hε : ε * ε = 1) {σm : (Fin 2 → ℝ) → S2} (hσ : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) I2 ∞ σm)
    (hf : ∀ y, sphereIncl2 (σm y) = stereoMap (Wpl ε) (vec3 0 0 σ) ((2 : ℝ) • modelEquiv2.symm y))
    (a : Fin 2) (y : Fin 2 → ℝ) :
    dι (I := I2) sphereIncl2 (σm y)
      (((nsq y + 1) / 2) • (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 σm y (Pi.single a 1) : Fin 2 → ℝ)) =
      vec3 ((Pi.single a 1 : Fin 2 → ℝ) 0 - 2 * y a * y 0 / (nsq y + 1))
        (ε * ((Pi.single a 1 : Fin 2 → ℝ) 1 - 2 * y a * y 1 / (nsq y + 1))) (σ * (2 * y a / (nsq y + 1))) := by
  set L : (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2) := (2 : ℝ) • (modelEquiv2.symm : (Fin 2 → ℝ) →L[ℝ] _)
  obtain ⟨D0, hD0, hDa⟩ := hasFDerivAt_stereoMap (Wpl ε) (vec3 0 0 σ) (L y)
  have hD : HasFDerivAt (fun y => sphereIncl2 (σm y)) (D0.comp L) y := by
    have := hD0.comp y L.hasFDerivAt
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => hf y)
  erw [ContinuousLinearMap.map_smul]
  rw [dι_mfderiv (hσ.mdifferentiableAt (by simp)) hD, ContinuousLinearMap.comp_apply, hDa]
  have hq := nsq_nonneg y
  have hLy : ‖L y‖ ^ 2 = 4 * nsq y := by
    simp only [L, ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe]
    rw [norm_smul, mul_pow, norm_sq_modelEquiv2_symm]; norm_num
  have hin : inner ℝ (L y) (L (Pi.single a 1)) = 4 * y a := by
    simp only [L, ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe, inner_smul_left,
      inner_smul_right, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
      modelEquiv2_symm_apply]
    fin_cases a <;> simp <;> ring
  rw [hLy, hin]
  ext i
  fin_cases i <;>
    simp [L, Wpl_apply, vec3, modelEquiv2_symm_apply, nsq] <;> fin_cases a <;> simp <;> field_simp <;> ring

lemma dι_fN (a : Fin 2) (y : Fin 2 → ℝ) : dι (I := I2) sphereIncl2 (stereoN y) (fN a y) = FrN a y := by
  have h := dι_fStereo (ε := 1) (σ := 1) (by norm_num) contMDiff_stereoN (fun y => stereoNE_eq y) a y
  unfold fN FrN; simpa using h

lemma dι_fS (a : Fin 2) (y : Fin 2 → ℝ) : dι (I := I2) sphereIncl2 (stereoS y) (fS a y) = FrS a y := by
  have h := dι_fStereo (ε := -1) (σ := -1) (by norm_num) contMDiff_stereoS (fun y => stereoSE_eq y) a y
  unfold fS FrS; simpa [neg_mul, one_mul, neg_sub] using h

/-- The transition `z ↦ 1/z`: `y ↦ (y₀, -y₁)/|y|²`. -/
def tau (y : Fin 2 → ℝ) : Fin 2 → ℝ := ![y 0 / nsq y, -(y 1) / nsq y]

/-- The frame change, a rotation: first row `u = ((y₁²-y₀²), -2y₀y₁)/|y|²`, second row `(-u₂, u₁)`. -/
def rotNS (y : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(y 1 ^ 2 - y 0 ^ 2) / nsq y, -(2 * y 0 * y 1) / nsq y;
     (2 * y 0 * y 1) / nsq y, (y 1 ^ 2 - y 0 ^ 2) / nsq y]

/-- **The frame change in `ℝ³`**: `FrS a (τ y) = Σ_b R a b FrN b y` for `y ≠ 0`. -/
lemma FrS_tau {y : Fin 2 → ℝ} (hy : nsq y ≠ 0) (a : Fin 2) :
    FrS a (tau y) = ∑ b, rotNS y a b • FrN b y := by
  have hq := nsq_nonneg y
  have h0 : tau y 0 = y 0 / nsq y := rfl
  have h1 : tau y 1 = -(y 1) / nsq y := rfl
  have hqdef : y 0 ^ 2 + y 1 ^ 2 = nsq y := rfl
  have ht : nsq (tau y) = (nsq y)⁻¹ := by
    rw [nsq, h0, h1, div_pow, div_pow, neg_sq, ← add_div, hqdef, sq, div_mul_eq_div_div, div_self hy,
      one_div]
  have hq1 : nsq y + 1 ≠ 0 := by positivity
  have hq2 : (nsq y)⁻¹ + 1 ≠ 0 := by have := inv_nonneg.mpr hq; positivity
  ext i
  fin_cases a <;> fin_cases i <;>
    simp [FrS, FrN, rotNS, Fin.sum_univ_two, h0, h1, ht] <;>
    unfold nsq at hy hq1 hq2 ⊢ <;> field_simp <;> ring

/-! ## The spin lift of the frame change -/

section Lift

open CliffordAlgebra

variable {n : ℕ}

lemma ι_sq_unit {u : E n} (hu : ‖u‖ = 1) : ι (Qneg n) u * ι (Qneg n) u = -1 := by
  rw [ι_sq_scalar, Qneg_apply, hu]; simp

/-- A unit vector is in the pin group of `Qneg n`. -/
lemma ι_mem_pinGroup_Qneg {u : E n} (hu : ‖u‖ = 1) : ι (Qneg n) u ∈ pinGroup (Qneg n) := by
  have hsq := ι_sq_unit hu
  refine ⟨⟨⟨ι (Qneg n) u, -ι (Qneg n) u, by rw [mul_neg, hsq, neg_neg], by rw [neg_mul, hsq, neg_neg]⟩,
    Subgroup.subset_closure ⟨u, rfl⟩, rfl⟩, ?_⟩
  change ι (Qneg n) u ∈ unitary (CliffordAlgebra (Qneg n))
  rw [Unitary.mem_iff, star_ι]
  exact ⟨by rw [neg_mul, hsq, neg_neg], by rw [mul_neg, hsq, neg_neg]⟩

/-- The product of two unit vectors is in `Spin(n)`. -/
lemma ι_mul_ι_mem_spinGroup_Qneg {u w : E n} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    ι (Qneg n) u * ι (Qneg n) w ∈ spinGroup (Qneg n) :=
  ⟨Submonoid.mul_mem _ (ι_mem_pinGroup_Qneg hu) (ι_mem_pinGroup_Qneg hw), ι_mul_ι_mem_evenOdd_zero _ u w⟩

lemma polar_Qneg (u v : E n) : QuadraticMap.polar (Qneg n) u v = -(2 * inner ℝ u v) := by
  rw [QuadraticMap.polar, Qneg_apply, Qneg_apply, Qneg_apply, norm_add_sq_real]; ring

/-- Conjugation by a unit vector: `ι u ι v ι(u)* = ι(2⟨u,v⟩ u - v)`. -/
lemma conj_ι_unit {u : E n} (hu : ‖u‖ = 1) (v : E n) :
    ι (Qneg n) u * ι (Qneg n) v * star (ι (Qneg n) u) = ι (Qneg n) ((2 * inner ℝ u v) • u - v) := by
  rw [star_ι, mul_neg, ι_mul_ι_mul_ι, polar_Qneg, Qneg_apply, hu, ← map_neg]
  congr 1
  simp only [one_pow, neg_smul, one_smul]
  abel

/-- The unit vector `y/|y|` of `ℝ²`, as a vector of `E 2`. -/
def unitE (y : Fin 2 → ℝ) : E 2 := (√(nsq y))⁻¹ • (modelEquiv2.symm y)

lemma unitE_apply (y : Fin 2 → ℝ) (i : Fin 2) : unitE y i = (√(nsq y))⁻¹ * y i := rfl

lemma norm_unitE {y : Fin 2 → ℝ} (hy : nsq y ≠ 0) : ‖unitE y‖ = 1 := by
  have hq := nsq_nonneg y
  have hs : 0 < √(nsq y) := Real.sqrt_pos.2 (lt_of_le_of_ne hq (Ne.symm hy))
  rw [unitE, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs]
  have hn : ‖modelEquiv2.symm y‖ = √(nsq y) := by
    rw [← norm_sq_modelEquiv2_symm, Real.sqrt_sq (norm_nonneg _)]
  rw [hn, inv_mul_cancel₀ hs.ne']

lemma norm_e (i : Fin n) : ‖(e i : E n)‖ = 1 := by simp [e]

/-- The spin lift `ι(y/|y|) ι(e₁)` of the frame change `rotNS y`. -/
def liftNS (y : Fin 2 → ℝ) : CliffordAlgebra (Qneg 2) := ι (Qneg 2) (unitE y) * ι (Qneg 2) (e 1)

/-- **`liftNS y` is a spin lift of `rotNS y`** (`y ≠ 0`). -/
theorem isSpinLift_liftNS {y : Fin 2 → ℝ} (hy : nsq y ≠ 0) : IsSpinLift (rotNS y) (liftNS y) := by
  have hu := norm_unitE hy
  refine ⟨ι_mul_ι_mem_spinGroup_Qneg hu (norm_e 1), fun a => ?_⟩
  unfold liftNS
  rw [star_mul, show ι (Qneg 2) (unitE y) * ι (Qneg 2) (e 1) * ι (Qneg 2) (e a) *
      (star (ι (Qneg 2) (e 1)) * star (ι (Qneg 2) (unitE y))) =
      ι (Qneg 2) (unitE y) * (ι (Qneg 2) (e 1) * ι (Qneg 2) (e a) * star (ι (Qneg 2) (e 1))) *
        star (ι (Qneg 2) (unitE y)) by simp only [mul_assoc],
    conj_ι_unit (norm_e 1), conj_ι_unit hu]
  congr 1
  have hq := nsq_nonneg y
  have hs : 0 < √(nsq y) := Real.sqrt_pos.2 (lt_of_le_of_ne hq (Ne.symm hy))
  have hss : √(nsq y) * √(nsq y) = nsq y := Real.mul_self_sqrt hq
  ext i
  fin_cases a <;> fin_cases i <;>
    simp [e, unitE_apply, rotNS, Fin.sum_univ_two, PiLp.inner_apply, modelEquiv2_symm_apply] <;> field_simp <;> unfold nsq at hss ⊢ <;>
    simp only [Real.sq_sqrt (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1)))] <;> ring

end Lift

end Lightlike.Dirac
