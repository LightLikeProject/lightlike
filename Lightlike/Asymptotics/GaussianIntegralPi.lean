import Mathlib

/-!
# The Gaussian integral on `ℝⁿ = Fin n → ℝ`

`∫ exp(−b Σᵢ yᵢ²) dy = (π/b)^{n/2}` for `b > 0` (`integral_exp_neg_mul_sum_sq`), with Lebesgue measure on
`Fin n → ℝ`; the integral of a product of functions of the coordinates is the product of the one-dimensional integrals
(`MeasureTheory.integral_fintype_prod_eq_prod`) and each factor is Mathlib's `integral_gaussian`. Translated to any
centre (`integral_exp_neg_mul_sum_sq_sub`). These normalize the Gaussian factor `(4πt)^{-n/2} e^{-|y−p|²/4t}` of the
heat-kernel parametrix: its integral is `1`.
-/

open MeasureTheory Real

noncomputable section

namespace Lightlike

/-- **The Gaussian integral on `ℝⁿ`**: `∫ exp(−b Σ yᵢ²) dy = (π/b)^{n/2}`. -/
theorem integral_exp_neg_mul_sum_sq (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ y : Fin n → ℝ, Real.exp (-b * ∑ i, y i ^ 2) = (π / b) ^ ((n : ℝ) / 2) := by
  have hprod : (fun y : Fin n → ℝ => Real.exp (-b * ∑ i, y i ^ 2)) =
      fun y => ∏ i, Real.exp (-b * y i ^ 2) := by
    funext y
    rw [← Real.exp_sum, Finset.mul_sum]
  rw [hprod, volume_pi, integral_fintype_prod_eq_prod (f := fun _ x => Real.exp (-b * x ^ 2))]
  simp only [integral_gaussian, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  ring_nf

/-- The same about any centre `p`. -/
theorem integral_exp_neg_mul_sum_sq_sub (n : ℕ) {b : ℝ} (hb : 0 < b) (p : Fin n → ℝ) :
    ∫ y : Fin n → ℝ, Real.exp (-b * ∑ i, (y i - p i) ^ 2) = (π / b) ^ ((n : ℝ) / 2) := by
  have := integral_sub_right_eq_self (μ := volume) (fun y : Fin n → ℝ => Real.exp (-b * ∑ i, y i ^ 2)) p
  simp only [Pi.sub_apply] at this
  rw [this, integral_exp_neg_mul_sum_sq n hb]

/-- The Gaussian is integrable. -/
theorem integrable_exp_neg_mul_sum_sq_sub (n : ℕ) {b : ℝ} (hb : 0 < b) (p : Fin n → ℝ) :
    Integrable (fun y : Fin n → ℝ => Real.exp (-b * ∑ i, (y i - p i) ^ 2)) := by
  have hprod : (fun y : Fin n → ℝ => Real.exp (-b * ∑ i, (y i - p i) ^ 2)) =
      fun y => ∏ i, Real.exp (-b * (y i - p i) ^ 2) := by
    funext y
    rw [← Real.exp_sum, Finset.mul_sum]
  rw [hprod, volume_pi]
  exact Integrable.fintype_prod (f := fun i x => Real.exp (-b * (x - p i) ^ 2)) fun i =>
    (integrable_exp_neg_mul_sq hb).comp_sub_right (p i)

end Lightlike
