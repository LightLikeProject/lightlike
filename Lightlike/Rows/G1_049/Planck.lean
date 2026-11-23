import Lightlike.Rows.G1_049.Continuation
import Lightlike.OperatorAlgebras.TestsShaleSqueeze
import Lightlike.OperatorAlgebras.TestsFockReduction

/-!
# The Planck spectrum from the Minkowski-Rindler Bogoliubov coefficients

Row G1-049 (milestone SC1).  For a Rindler mode of frequency `ω > 0` and acceleration `a > 0` the Bogoliubov
coefficients between the Minkowski and the Rindler modes are
`α = 1/√(1 - e^{-2πω/a})` and `β = e^{-πω/a} α` (Unruh 1976; Crispino-Higuchi-Matsas 2008, §II).
The ratio `β/α = e^{-πω/a}` is the weight found in `Lightlike.Rows.G1_049.unruhMode_rindler_left`.
Here the coefficients are written through the Planck factor `n(ω) = 1/(e^{2πω/a} - 1)`:
`β² = n`, `α² = 1 + n`, so `α² - β² = 1` and `β/α = e^{-πω/a}`.  The one-mode squeezing with these
coefficients (`Bogoliubov.squeeze`) has `‖β z‖² = n ‖z‖²`.  Writing `2πω/a = ω/T`, the factor
`n` is the Bose-Einstein factor at the Unruh temperature `T = a/2π`.

## Main statements

* `planck_eq_bose`: `n = 1/(e^{ω/T} - 1)` with `T = a/(2π)`.
* `unruhBeta_eq_exp_mul_unruhAlpha`: `β = e^{-πω/a} α`.
* `unruhAlpha_sq_sub_unruhBeta_sq`: `α² - β² = 1`.
* `unruhSqueeze_norm_betaPart_sq`: `‖β z‖² = n ‖z‖²` for the squeeze built from `α, β`.
* `planck_tendsto_zero`: `n(ω) → 0` as `ω → ∞`.
* `betaPart_id`, `squeeze_one_zero_betaPart`: the inertial (trivial) transformation has `β = 0`.
-/

namespace Lightlike.Rows.G1_049

open Real
open scoped Complex
open Lightlike.OperatorAlgebras

/-- The Unruh temperature `T = a/(2π)` of an observer of acceleration `a` (units `ħ = c = k_B = 1`). -/
noncomputable def unruhTemp (a : ℝ) : ℝ := a / (2 * π)

/-- The Planck factor `n(ω) = 1/(e^{2πω/a} - 1)`. -/
noncomputable def planck (ω a : ℝ) : ℝ := 1 / (Real.exp (2 * π * ω / a) - 1)

theorem one_lt_exp_planck {ω a : ℝ} (hω : 0 < ω) (ha : 0 < a) : 1 < Real.exp (2 * π * ω / a) :=
  Real.one_lt_exp_iff.2 (by positivity)

theorem planck_pos {ω a : ℝ} (hω : 0 < ω) (ha : 0 < a) : 0 < planck ω a := by
  have := one_lt_exp_planck hω ha
  unfold planck
  have : 0 < Real.exp (2 * π * ω / a) - 1 := by linarith
  positivity

/-- **The factor is the Bose-Einstein factor `1/(e^{ω/T} - 1)` at `T = a/2π`.** -/
theorem planck_eq_bose {ω a : ℝ} (ha : 0 < a) :
    planck ω a = 1 / (Real.exp (ω / unruhTemp a) - 1) := by
  unfold planck unruhTemp
  have : 2 * π * ω / a = ω / (a / (2 * π)) := by
    field_simp
  rw [this]

/-- The Bogoliubov coefficient `α = √(1 + n)` (a real number, `= 1/√(1 - e^{-2πω/a})`). -/
noncomputable def unruhAlpha (ω a : ℝ) : ℝ := Real.sqrt (1 + planck ω a)

/-- The Bogoliubov coefficient `β = √n`. -/
noncomputable def unruhBeta (ω a : ℝ) : ℝ := Real.sqrt (planck ω a)

/-- **`α² - β² = 1`**: the Bogoliubov normalisation. -/
theorem unruhAlpha_sq_sub_unruhBeta_sq {ω a : ℝ} (hω : 0 < ω) (ha : 0 < a) :
    unruhAlpha ω a ^ 2 - unruhBeta ω a ^ 2 = 1 := by
  have h := planck_pos hω ha
  unfold unruhAlpha unruhBeta
  rw [Real.sq_sqrt (by linarith), Real.sq_sqrt h.le]
  ring

/-- `β² = n`: the squared coefficient is the Planck factor. -/
theorem unruhBeta_sq {ω a : ℝ} (hω : 0 < ω) (ha : 0 < a) :
    unruhBeta ω a ^ 2 = 1 / (Real.exp (2 * π * ω / a) - 1) :=
  Real.sq_sqrt (planck_pos hω ha).le

/-- **The ratio `β/α = e^{-πω/a}`**, the weight of `unruhMode_rindler_left`. -/
theorem unruhBeta_eq_exp_mul_unruhAlpha {ω a : ℝ} (hω : 0 < ω) (ha : 0 < a) :
    unruhBeta ω a = Real.exp (-(π * ω / a)) * unruhAlpha ω a := by
  have h := planck_pos hω ha
  have hE := one_lt_exp_planck hω ha
  have hne : Real.exp (2 * π * ω / a) - 1 ≠ 0 := by linarith
  have hsq : unruhBeta ω a ^ 2 = (Real.exp (-(π * ω / a)) * unruhAlpha ω a) ^ 2 := by
    have e1 : Real.exp (-(π * ω / a)) ^ 2 = (Real.exp (2 * π * ω / a))⁻¹ := by
      rw [sq, ← Real.exp_add, ← Real.exp_neg]
      congr 1
      ring
    rw [mul_pow, e1]
    unfold unruhAlpha unruhBeta
    rw [Real.sq_sqrt (show 0 ≤ 1 + planck ω a by linarith), Real.sq_sqrt h.le]
    unfold planck
    have hE0 : Real.exp (2 * π * ω / a) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
    ring
  refine (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))).1 hsq

/-- The one-mode squeezing with the Unruh coefficients `α, β`. -/
noncomputable def unruhSqueeze (ω a : ℝ) (hω : 0 < ω) (ha : 0 < a) : Bogoliubov ℂ :=
  Bogoliubov.squeeze (unruhAlpha ω a) (unruhBeta ω a) (unruhAlpha_sq_sub_unruhBeta_sq hω ha)

/-- **Particle number**: the antilinear part of the Unruh squeezing has `‖β z‖² = n ‖z‖²`, with `n` the Planck
factor `1/(e^{2πω/a} - 1)`. -/
theorem unruhSqueeze_norm_betaPart_sq {ω a : ℝ} (hω : 0 < ω) (ha : 0 < a) (z : ℂ) :
    ‖(unruhSqueeze ω a hω ha).betaPart z‖ ^ 2 = (1 / (Real.exp (2 * π * ω / a) - 1)) * ‖z‖ ^ 2 := by
  unfold unruhSqueeze
  rw [Bogoliubov.squeeze_betaPart, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs,
    unruhBeta_sq hω ha]
  simp

/-- The complex-linear part of the Unruh squeezing is multiplication by `α`. -/
theorem unruhSqueeze_alphaPart {ω a : ℝ} (hω : 0 < ω) (ha : 0 < a) (z : ℂ) :
    (unruhSqueeze ω a hω ha).alphaPart z = (unruhAlpha ω a : ℂ) * z := by
  unfold unruhSqueeze Bogoliubov.alphaPart
  rw [Bogoliubov.squeeze_apply, Bogoliubov.squeeze_apply]
  simp only [smul_eq_mul, map_mul, Complex.conj_I]
  linear_combination (-(1 / 2 : ℂ) * (unruhAlpha ω a : ℂ) * z + (1 / 2 : ℂ) * (unruhBeta ω a : ℂ) *
    (starRingEnd ℂ) z) * Complex.I_mul_I

/-- **The Planck factor vanishes at high frequency.** -/
theorem planck_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun ω => planck ω a) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun ω : ℝ => 2 * π * ω / a) Filter.atTop Filter.atTop := by
    have : (fun ω : ℝ => 2 * π * ω / a) = fun ω => ω * (2 * π / a) := by
      funext ω; ring
    rw [this]
    exact Filter.tendsto_id.atTop_mul_const (by positivity)
  have h2 := (Real.tendsto_exp_atTop.comp h1)
  have h3 : Filter.Tendsto (fun ω : ℝ => Real.exp (2 * π * ω / a) - 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ (-1) h2
  have h4 := h3.inv_tendsto_atTop
  unfold planck
  simp only [one_div]
  exact h4

/-- **An inertial observer sees no particles (identity case).** The identity Bogoliubov transformation has
vanishing antilinear part. -/
theorem betaPart_id {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h] (f : h) :
    (Bogoliubov.id h).betaPart f = 0 := by
  unfold Bogoliubov.betaPart
  show (1 / 2 : ℂ) • (f + Complex.I • Complex.I • f) = 0
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp

/-- **The squeeze with `a = 1`, `b = 0` has no antilinear part**: no particles. -/
theorem squeeze_one_zero_betaPart (z : ℂ) :
    (Bogoliubov.squeeze 1 0 (by norm_num)).betaPart z = 0 := by
  rw [Bogoliubov.squeeze_betaPart]
  simp

end Lightlike.Rows.G1_049
