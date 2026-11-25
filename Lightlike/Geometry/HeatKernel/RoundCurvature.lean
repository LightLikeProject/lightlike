import Mathlib
import Lightlike.Geometry.HeatKernel.StereoCurvature
import Lightlike.Geometry.HeatKernel.ConformalCurvature

/-!
# Scalar curvature of the round 2-sphere of radius `r` at the origin of a stereographic chart

In the chart of Mathlib's atlas the round metric of the 2-sphere of radius `r` is `f · δ` with
`f y = 16 r² / (|y|² + 4)²` (`confMetric (roundF r)`). Its scalar curvature at the origin is `2 / r²`
(`scalarCurvature_roundF_zero`), by `scalarCurvature_conf` at the critical point `0` with Hessian `-r² δ`.
-/

open Lightlike Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.HeatKernel

/-- `|y|² + 4`. -/
def roundQ (n : ℕ) : (Fin n → ℝ) → ℝ := fun y => 4 + ∑ i, y i ^ 2

/-- The conformal factor `16 r² / (|y|² + 4)²` of the round sphere of radius `r` in Mathlib's stereographic chart. -/
def roundF (n : ℕ) (r : ℝ) : (Fin n → ℝ) → ℝ := fun y => 16 * r ^ 2 / roundQ n y ^ 2

variable {n : ℕ}

lemma roundQ_pos (y : Fin n → ℝ) : 0 < roundQ n y := by
  unfold roundQ; positivity

lemma contDiff_roundQ : ContDiff ℝ ∞ (roundQ n) := by
  unfold roundQ; fun_prop

lemma pd_roundQ (a : Fin n) (y : Fin n → ℝ) : pd a (roundQ n) y = 2 * y a := by
  have h := pd_stereoQ a y
  have e : roundQ n = fun y => stereoQ n y + 3 := by
    funext y; unfold roundQ stereoQ; ring
  rw [e]
  unfold pd at h ⊢
  rw [fderiv_add_const]
  exact h

lemma pd_roundF (r : ℝ) (a : Fin n) (y : Fin n → ℝ) :
    pd a (roundF n r) y = (-64 * r ^ 2 * y a) * (1 / roundQ n y ^ 3) := by
  have ht : roundQ n y ≠ 0 := (roundQ_pos y).ne'
  have hg : HasDerivAt (fun t : ℝ => 16 * r ^ 2 / t ^ 2) (-32 * r ^ 2 / (roundQ n y) ^ 3) (roundQ n y) := by
    have h := ((hasDerivAt_pow 2 (roundQ n y)).inv (pow_ne_zero 2 ht)).const_mul (16 * r ^ 2)
    convert h using 1
    · funext t; simp [div_eq_mul_inv]
    · field_simp
      ring
  have hq : HasFDerivAt (roundQ n) (fderiv ℝ (roundQ n) y) y :=
    ((contDiff_roundQ.differentiable (by simp)) y).hasFDerivAt
  have hc := hg.comp_hasFDerivAt y hq
  have hF : roundF n r = (fun t : ℝ => 16 * r ^ 2 / t ^ 2) ∘ roundQ n := rfl
  have := pd_roundQ a y
  unfold pd at this ⊢
  rw [hF, hc.fderiv]
  simp only [_root_.smul_apply, smul_eq_mul, this]
  field_simp
  ring

lemma contDiff_roundF (r : ℝ) : ContDiff ℝ ∞ (roundF n r) :=
  contDiff_const.div (contDiff_roundQ.pow 2) (fun y => pow_ne_zero 2 (roundQ_pos y).ne')

lemma roundF_ne_zero {r : ℝ} (hr : r ≠ 0) (y : Fin n → ℝ) : roundF n r y ≠ 0 := by
  unfold roundF
  have := roundQ_pos y
  positivity

lemma roundF_zero (r : ℝ) : roundF n r 0 = r ^ 2 := by
  simp [roundF, roundQ]
  ring

lemma pd_roundF_zero (r : ℝ) (a : Fin n) : pd a (roundF n r) 0 = 0 := by
  rw [pd_roundF]; simp

lemma hess_roundF (r : ℝ) (a b : Fin n) :
    pd a (pd b (roundF n r)) 0 = if a = b then -r ^ 2 else 0 := by
  have hfun : pd b (roundF n r) = fun y => (-64 * r ^ 2 * y b) * (1 / roundQ n y ^ 3) :=
    funext (pd_roundF r b)
  have hA : DifferentiableAt ℝ (fun y : Fin n → ℝ => -64 * r ^ 2 * y b) 0 := by fun_prop
  have hB : DifferentiableAt ℝ (fun y : Fin n → ℝ => 1 / roundQ n y ^ 3) 0 :=
    ((contDiff_const.div (contDiff_roundQ.pow 3)
      (fun y => pow_ne_zero 3 (roundQ_pos y).ne')).differentiable (by simp)) 0
  rw [hfun, pd_mul a hA hB]
  have hQ : roundQ n 0 = 4 := by simp [roundQ]
  have hA' : pd a (fun y : Fin n → ℝ => -64 * r ^ 2 * y b) 0 = if a = b then -64 * r ^ 2 else 0 := by
    have := pd_coord a b 0
    unfold pd at this ⊢
    rw [fderiv_const_mul (by fun_prop), _root_.smul_apply, this]
    by_cases h : a = b <;> simp [h]
  rw [hA', hQ]
  by_cases h : a = b
  · simp [h]; ring
  · simp [h]

/-- **The scalar curvature of the round 2-sphere of radius `r`** in a stereographic chart, at the origin, computed with
the coordinate `scalarCurvature`: `2 / r²`. -/
theorem scalarCurvature_roundF_zero {r : ℝ} (hr : r ≠ 0) :
    scalarCurvature (confMetric (roundF 2 r)) 0 = 2 / r ^ 2 := by
  rw [scalarCurvature_conf (contDiff_roundF r) (roundF_ne_zero hr) 0 (pd_roundF_zero r) (-r ^ 2)
    (hess_roundF r), roundF_zero]
  field_simp
  push_cast
  ring

end Lightlike.HeatKernel
