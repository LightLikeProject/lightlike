module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileODE

/-!
# Decay of the radial profiles of the discrete series

For `n ≥ 1` the profile `ψ_{jl}(ξ) = κ cosh(ξ/2)^{-n} P_{jl}(tanh(ξ/2))` is continuous on `ℝ` and bounded by
`C e^{-nξ/2}` for `ξ ≥ 0` (`norm_profileFun_le`), so the products `ψ conj χ sinh` of two profiles with
`n + n' ≥ 4` are integrable on `(0, ∞)` and tend to `0` at infinity.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real Filter Topology Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

lemma norm_genFun_le (n l : ℕ) {t : ℝ} (ht : |t| ≤ 1) {w : ℂ} (hw : ‖w‖ = 1 / 2) :
    ‖genFun n l t w‖ ≤ (3 / 2) ^ l * 2 ^ (n + l) := by
  have hv := norm_one_add_mul_ge ht hw
  have hA : ‖(t : ℂ) + w‖ ≤ 3 / 2 := by
    calc ‖(t : ℂ) + w‖ ≤ ‖(t : ℂ)‖ + ‖w‖ := norm_add_le _ _
      _ ≤ 1 + 1 / 2 := by rw [Complex.norm_real, Real.norm_eq_abs, hw]; linarith
      _ = 3 / 2 := by norm_num
  unfold genFun
  rw [norm_mul, norm_pow]
  have h1 := norm_inv_pow_le hv (n + l)
  have h2 : ‖(t : ℂ) + w‖ ^ l ≤ (3 / 2) ^ l := pow_le_pow_left₀ (norm_nonneg _) hA _
  gcongr

lemma norm_discCoeff_le {h : ℂ → ℂ} (B : ℝ) (hB : ∀ θ : ℝ, ‖h (circleMap 0 (1 / 2) θ)‖ ≤ B) (m : ℕ) :
    ‖discCoeff h m‖ ≤ B * 2 ^ m := by
  unfold discCoeff
  have h1 := (cauchyPowerSeries h 0 (1 / 2) m).le_opNorm (fun _ => (1 : ℂ))
  simp only [Finset.prod_const, norm_one, one_pow, mul_one] at h1
  have h2 := norm_cauchyPowerSeries_le h 0 (1 / 2) m
  have h3 : ∫ θ in (0 : ℝ)..2 * π, ‖h (circleMap 0 (1 / 2) θ)‖ ≤ B * (2 * π) := by
    have h4 := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun θ => ‖h (circleMap 0 (1 / 2) θ)‖) (a := 0) (b := 2 * π) (C := B)
      (fun θ _ => by simpa using hB θ)
    have h5 : 0 ≤ ∫ θ in (0 : ℝ)..2 * π, ‖h (circleMap 0 (1 / 2) θ)‖ :=
      intervalIntegral.integral_nonneg (by positivity) (fun θ _ => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg h5] at h4
    have h6 : |2 * π - 0| = 2 * π := by rw [sub_zero]; exact abs_of_pos (by positivity)
    rw [h6] at h4
    exact h4
  have hpi : 0 < π := Real.pi_pos
  have h7 : ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖h (circleMap 0 (1 / 2) θ)‖) ≤ B := by
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith
  have h8 : |(1 / 2 : ℝ)|⁻¹ ^ m = 2 ^ m := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num
  calc ‖cauchyPowerSeries h 0 (1 / 2) m (fun _ => (1 : ℂ))‖ ≤ ‖cauchyPowerSeries h 0 (1 / 2) m‖ := h1
    _ ≤ ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖h (circleMap 0 (1 / 2) θ)‖) * |(1 / 2 : ℝ)|⁻¹ ^ m := h2
    _ ≤ B * 2 ^ m := by
      rw [h8]
      exact mul_le_mul_of_nonneg_right h7 (by positivity)

/-- **A bound for the profile polynomials**, from the Cauchy estimate on the circle of radius `1/2`. -/
lemma norm_profPoly_le (n l j : ℕ) {t : ℝ} (ht : |t| < 1) :
    ‖profPoly n l j t‖ ≤ ((3 / 2) ^ l * 2 ^ (n + l)) * 2 ^ j :=
  norm_discCoeff_le _ (fun θ => norm_genFun_le n l ht.le (norm_circleMap_half θ)) j

lemma cosh_half_pow_inv_le (n : ℕ) (ξ : ℝ) :
    (Real.cosh (ξ / 2) ^ n)⁻¹ ≤ 2 ^ n * Real.exp (-((n : ℝ) * ξ / 2)) := by
  have h1 : Real.exp (ξ / 2) / 2 ≤ Real.cosh (ξ / 2) := by
    rw [Real.cosh_eq]
    have := Real.exp_pos (-(ξ / 2))
    linarith
  have h2 : (0 : ℝ) < Real.exp (ξ / 2) / 2 := by positivity
  have h3 : (Real.exp (ξ / 2) / 2) ^ n ≤ Real.cosh (ξ / 2) ^ n := pow_le_pow_left₀ h2.le h1 n
  have h4 : (Real.cosh (ξ / 2) ^ n)⁻¹ ≤ ((Real.exp (ξ / 2) / 2) ^ n)⁻¹ := inv_anti₀ (by positivity) h3
  refine h4.trans (le_of_eq ?_)
  rw [div_pow, inv_div, ← Real.exp_nat_mul, show -((n : ℝ) * ξ / 2) = -((n : ℝ) * (ξ / 2)) by ring,
    Real.exp_neg, div_eq_mul_inv]

/-- **The decay of the profile**: `|ψ(ξ)| ≤ C e^{-nξ/2}` for `ξ ≥ 0`. -/
lemma norm_profileFun_le (n l j : ℕ) (κ : ℂ) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    ‖profileFun n l j κ ξ‖ ≤
      ‖κ‖ * (2 ^ n * (2 ^ j * ((3 / 2) ^ l * 2 ^ (n + l)))) * Real.exp (-((n : ℝ) * ξ / 2)) := by
  unfold profileFun
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 := cosh_half_pow_inv_le n ξ
  have h2 := norm_profPoly_le n l j (abs_tanh_half_lt_one ξ)
  have h3 : 0 ≤ ‖κ‖ := norm_nonneg _
  calc ‖κ‖ * (Real.cosh (ξ / 2) ^ n)⁻¹ * ‖profPoly n l j (Real.tanh (ξ / 2))‖
      ≤ ‖κ‖ * (2 ^ n * Real.exp (-((n : ℝ) * ξ / 2))) * (((3 / 2) ^ l * 2 ^ (n + l)) * 2 ^ j) := by
        gcongr
    _ = ‖κ‖ * (2 ^ n * (2 ^ j * ((3 / 2) ^ l * 2 ^ (n + l)))) * Real.exp (-((n : ℝ) * ξ / 2)) := by ring

lemma continuous_profileFun (n l j : ℕ) (hn : 1 ≤ n) (κ : ℂ) : Continuous (profileFun n l j κ) :=
  continuous_iff_continuousAt.2 fun ξ => (hasDerivAt_profileFun n l j hn κ ξ).continuousAt

end Lightlike.Lorentz.SL2RPlancherel
