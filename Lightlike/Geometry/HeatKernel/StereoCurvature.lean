import Lightlike.Geometry.HeatKernel.ConformalCurvature

/-!
# Scalar curvature of the round unit `n`-sphere in stereographic coordinates

The round metric of the unit `n`-sphere in stereographic coordinates is `4 (1 + |y|²)⁻² δ`.  Using
`Lightlike.scalarCurvature` (the GE1 coordinate curvature) and `scalarCurvature_conf` we show that
its scalar curvature at the origin is `n (n − 1)`; for `n = 3` this is the value `R = 6` fed into
`heatCoeffs` for the round `S³` (`Sphere3Expansion`), and for `n = 2` the value `R = 2`.
-/

open Lightlike Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.HeatKernel

variable {n : ℕ}

/-- Stereographic conformal factor `4 / (1 + |y|²)²` of the unit round sphere. -/
def stereoF (n : ℕ) : (Fin n → ℝ) → ℝ := fun y => 4 / (1 + ∑ i, y i ^ 2) ^ 2

/-- `1 + |y|²`. -/
def stereoQ (n : ℕ) : (Fin n → ℝ) → ℝ := fun y => 1 + ∑ i, y i ^ 2

lemma stereoQ_pos (y : Fin n → ℝ) : 0 < stereoQ n y := by
  unfold stereoQ
  positivity

lemma contDiff_stereoQ : ContDiff ℝ ∞ (stereoQ n) := by
  unfold stereoQ
  fun_prop

lemma pd_stereoQ (a : Fin n) (y : Fin n → ℝ) : pd a (stereoQ n) y = 2 * y a := by
  unfold pd stereoQ
  rw [fderiv_const_add, fderiv_fun_sum (fun i _ => by fun_prop)]
  have h : ∀ i, fderiv ℝ (fun y : Fin n → ℝ => y i ^ 2) y (Pi.single a 1) =
      if i = a then 2 * y i else 0 := by
    intro i
    have h0 : HasFDerivAt (fun f : Fin n → ℝ => f i)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) y :=
      hasFDerivAt_apply i y
    have h1 : HasFDerivAt (fun f : Fin n → ℝ => f i ^ 2)
        (((2 : ℕ) • y i ^ (2 - 1)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) y :=
      h0.pow 2
    rw [h1.fderiv]
    by_cases hia : i = a <;> simp [Pi.single_apply, hia]
  simp [h]

lemma pd_stereoF (a : Fin n) (y : Fin n → ℝ) :
    pd a (stereoF n) y = (-16 * y a) * (1 / stereoQ n y ^ 3) := by
  have ht : stereoQ n y ≠ 0 := (stereoQ_pos y).ne'
  have hg : HasDerivAt (fun t : ℝ => 4 / t ^ 2) (-8 / (stereoQ n y) ^ 3) (stereoQ n y) := by
    have h := ((hasDerivAt_pow 2 (stereoQ n y)).inv (pow_ne_zero 2 ht)).const_mul 4
    convert h using 1
    · funext t; simp [div_eq_mul_inv]
    · field_simp
      ring
  have hq : HasFDerivAt (stereoQ n) (fderiv ℝ (stereoQ n) y) y :=
    ((contDiff_stereoQ.differentiable (by simp)) y).hasFDerivAt
  have hc := hg.comp_hasFDerivAt y hq
  have hF : stereoF n = (fun t : ℝ => 4 / t ^ 2) ∘ stereoQ n := rfl
  have := pd_stereoQ a y
  unfold pd at this ⊢
  rw [hF, hc.fderiv]
  simp only [_root_.smul_apply, smul_eq_mul, this]
  field_simp
  ring

lemma contDiff_stereoF : ContDiff ℝ ∞ (stereoF n) :=
  contDiff_const.div (contDiff_stereoQ.pow 2) (fun y => pow_ne_zero 2 (stereoQ_pos y).ne')

lemma stereoF_pos (y : Fin n → ℝ) : stereoF n y ≠ 0 := by
  unfold stereoF
  have := stereoQ_pos y
  unfold stereoQ at this
  positivity

lemma stereoF_zero : stereoF n 0 = 4 := by
  simp [stereoF]

lemma pd_stereoF_zero (a : Fin n) : pd a (stereoF n) 0 = 0 := by
  rw [pd_stereoF]
  simp

lemma pd_coord (a b : Fin n) (y : Fin n → ℝ) :
    pd a (fun y : Fin n → ℝ => y b) y = if a = b then 1 else 0 := by
  have h0 : HasFDerivAt (fun f : Fin n → ℝ => f b)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b) y := hasFDerivAt_apply b y
  unfold pd
  rw [h0.fderiv]
  by_cases h : a = b <;> simp [h]

lemma hess_stereoF (a b : Fin n) :
    pd a (pd b (stereoF n)) 0 = if a = b then -16 else 0 := by
  have hfun : pd b (stereoF n) = fun y => (-16 * y b) * (1 / stereoQ n y ^ 3) :=
    funext (pd_stereoF b)
  have hA : DifferentiableAt ℝ (fun y : Fin n → ℝ => -16 * y b) 0 := by fun_prop
  have hB : DifferentiableAt ℝ (fun y : Fin n → ℝ => 1 / stereoQ n y ^ 3) 0 :=
    ((contDiff_const.div (contDiff_stereoQ.pow 3)
      (fun y => pow_ne_zero 3 (stereoQ_pos y).ne')).differentiable (by simp)) 0
  rw [hfun, pd_mul a hA hB]
  have hQ : stereoQ n 0 = 1 := by simp [stereoQ]
  have hA' : pd a (fun y : Fin n → ℝ => -16 * y b) 0 = if a = b then -16 else 0 := by
    have := pd_coord a b 0
    unfold pd at this ⊢
    rw [fderiv_const_mul (by fun_prop), _root_.smul_apply, this]
    by_cases h : a = b <;> simp [h]
  rw [hA', hQ]
  simp

/-- **Scalar curvature of the round unit `n`-sphere** in stereographic coordinates, computed with
Lightlike's coordinate curvature `scalarCurvature`: at the origin, `R = n (n − 1)`. -/
theorem scalarCurvature_stereo (n : ℕ) :
    scalarCurvature (confMetric (stereoF n)) 0 = n * (n - 1) := by
  rw [scalarCurvature_conf contDiff_stereoF stereoF_pos 0 pd_stereoF_zero (-16) hess_stereoF,
    stereoF_zero]
  ring

/-- The round `S³` has scalar curvature `6`, the value used in `heatCoeffs_sphere3`. -/
theorem scalarCurvature_stereo_three :
    scalarCurvature (confMetric (stereoF 3)) 0 = 6 := by
  rw [scalarCurvature_stereo]; norm_num

/-- The round `S²` has scalar curvature `2`. -/
theorem scalarCurvature_stereo_two :
    scalarCurvature (confMetric (stereoF 2)) 0 = 2 := by
  rw [scalarCurvature_stereo]; norm_num

end Lightlike.HeatKernel
