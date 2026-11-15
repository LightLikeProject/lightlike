import Mathlib
import Lightlike.Regge.CMS.StarFlat
import Lightlike.Regge.CMS.PerTriangle

/-!
# Fatness bounds the angles of a star (RC6b)

If two neighbour offsets `a`, `b` of a vertex have sup norm at most `h` and span a triangle of
signed area `det2 a b ≥ ρ h²`, then the angle between them is at most `π - arcsin (min (ρ/2) 1)`.
The sine of the angle times the product of the Euclidean norms equals `|det2 a b|`, and the
Euclidean norm is at most `√2 h`.
-/

open Real

namespace Lightlike.CMS

theorem sin_angle_toC_mul (a b : Fin 2 → ℝ) :
    Real.sin (InnerProductGeometry.angle (toC a) (toC b)) * (‖toC a‖ * ‖toC b‖) = |det2 a b| := by
  rw [InnerProductGeometry.sin_angle_mul_norm_mul_norm, ← Real.sqrt_sq_eq_abs]
  congr 1
  simp [Complex.inner, toC, det2, Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem norm_toC_sq_le {a : Fin 2 → ℝ} {h : ℝ} (ha : ‖a‖ ≤ h) : ‖toC a‖ ^ 2 ≤ 2 * h ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have h0 : |a 0| ≤ h := (norm_le_pi_norm a 0).trans ha
  have h1 : |a 1| ≤ h := (norm_le_pi_norm a 1).trans ha
  have e0 := sq_le_sq' (abs_le.mp h0).1 (abs_le.mp h0).2
  have e1 := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  simp only [toC]
  nlinarith

/-- **Fat stars have angles bounded away from `π`.** -/
theorem angle_le_of_fat {a b : Fin 2 → ℝ} {h ρ : ℝ} (hh : 0 < h) (hρ : 0 < ρ)
    (ha : ‖a‖ ≤ h) (hb : ‖b‖ ≤ h) (hd : ρ * h ^ 2 ≤ det2 a b) :
    InnerProductGeometry.angle (toC a) (toC b) ≤ π - arcsin (min (ρ / 2) 1) := by
  set t := InnerProductGeometry.angle (toC a) (toC b) with ht
  have hs := sin_angle_toC_mul a b
  have hsn : 0 ≤ Real.sin t := InnerProductGeometry.sin_angle_nonneg _ _
  have hna := norm_toC_sq_le ha
  have hnb := norm_toC_sq_le hb
  have hprod : ‖toC a‖ * ‖toC b‖ ≤ 2 * h ^ 2 := by
    have : (‖toC a‖ * ‖toC b‖) ^ 2 ≤ (2 * h ^ 2) ^ 2 := by
      rw [mul_pow]; nlinarith [norm_nonneg (toC a), norm_nonneg (toC b), sq_nonneg ‖toC a‖,
        sq_nonneg ‖toC b‖, mul_le_mul hna hnb (sq_nonneg _) (by positivity)]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 this
  have hsin : ρ / 2 ≤ Real.sin t := by
    have h1 : ρ * h ^ 2 ≤ Real.sin t * (2 * h ^ 2) := by
      calc ρ * h ^ 2 ≤ det2 a b := hd
        _ ≤ |det2 a b| := le_abs_self _
        _ = Real.sin t * (‖toC a‖ * ‖toC b‖) := hs.symm
        _ ≤ Real.sin t * (2 * h ^ 2) := mul_le_mul_of_nonneg_left hprod hsn
    have : 0 < h ^ 2 := by positivity
    nlinarith
  by_contra hcon
  rw [not_le] at hcon
  have hπ : t ≤ π := InnerProductGeometry.angle_le_pi _ _
  have hlt : π - t < arcsin (min (ρ / 2) 1) := by linarith
  have hpos : 0 ≤ π - t := by linarith
  have hle : arcsin (min (ρ / 2) 1) ≤ π / 2 := arcsin_le_pi_div_two _
  have : Real.sin (π - t) < Real.sin (arcsin (min (ρ / 2) 1)) := by
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two <;> linarith
  rw [Real.sin_pi_sub, Real.sin_arcsin (by
    have := le_min (by linarith : (-1:ℝ) ≤ ρ / 2) (by norm_num : (-1:ℝ) ≤ 1); exact this)
    (min_le_right _ _)] at this
  have := min_le_left (ρ / 2) 1
  linarith
end Lightlike.CMS
