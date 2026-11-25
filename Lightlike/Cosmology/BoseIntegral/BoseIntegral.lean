module

public import Mathlib

/-!
# The Bose integral `∫₀^∞ xᵏ/(eˣ − 1) dx = k! ζ(k+1)`

Row G1-033 (milestone CO6, Bose and Fermi densities).  The black-body integrals are expanded as
`1/(eˣ − 1) = ∑ₙ e^{-(n+1)x}` and integrated termwise against the Gamma integral.
-/

open MeasureTheory Set Real
open scoped Nat

public section

namespace Lightlike.Cosmology.BoseIntegral

/-- The Gamma integral for integer powers: `∫₀^∞ xᵏ e^{-c x} dx = k!/c^{k+1}`, `c > 0`. -/
lemma integral_pow_mul_exp_neg (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ x in Ioi (0 : ℝ), x ^ k * rexp (-(c * x)) = k ! / c ^ (k + 1) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have key := integral_rpow_mul_exp_neg_mul_Ioi hk hc
  simp_rw [add_sub_cancel_right, rpow_natCast] at key
  rw [key, Gamma_nat_eq_factorial, one_div, Real.inv_rpow hc.le, ← rpow_natCast]
  push_cast
  rw [div_eq_inv_mul]

/-- Integrability of `xᵏ e^{-c x}` on `(0, ∞)`. -/
lemma integrableOn_pow_mul_exp_neg (k : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ k * rexp (-(c * x))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_pow_mul_exp_neg k hc]
  positivity

/-- For `x > 0`, the geometric expansion `1/(eˣ − 1) = ∑ₙ e^{-(n+1)x}`. -/
lemma hasSum_exp_neg_succ {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => rexp (-(((n : ℝ) + 1) * x))) (1 / (rexp x - 1)) := by
  have hr0 : 0 < rexp (-x) := exp_pos _
  have hr1 : rexp (-x) < 1 := by
    rw [← exp_zero]; exact exp_lt_exp.mpr (by linarith)
  have h := (hasSum_geometric_of_lt_one hr0.le hr1).mul_left (rexp (-x))
  have e1 : ∀ n : ℕ, rexp (-x) * rexp (-x) ^ n = rexp (-(((n : ℝ) + 1) * x)) := by
    intro n
    rw [← exp_nat_mul, ← exp_add]
    congr 1
    ring
  have hex : 1 < rexp x := by
    rw [← exp_zero]; exact exp_lt_exp.mpr hx
  have e2 : rexp (-x) * (1 - rexp (-x))⁻¹ = 1 / (rexp x - 1) := by
    rw [exp_neg]
    have : rexp x - 1 ≠ 0 := by linarith
    have h2 : (1 - (rexp x)⁻¹) = (rexp x - 1) / rexp x := by field_simp
    rw [h2]
    field_simp
  simpa only [e1, e2] using h

/-- The Bose integral as a series: for `k ≥ 1`,
`∫₀^∞ xᵏ/(eˣ − 1) dx = k! ∑ₙ 1/(n+1)^{k+1}`  (that is, `k! ζ(k+1)`). -/
theorem integral_pow_div_exp_sub_one (k : ℕ) (hk : 1 ≤ k) :
    ∫ x in Ioi (0 : ℝ), x ^ k / (rexp x - 1) =
      k ! * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (k + 1) := by
  set F : ℕ → ℝ → ℝ := fun n x => x ^ k * rexp (-(((n : ℝ) + 1) * x)) with hF
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi (0 : ℝ))) :=
    fun n => integrableOn_pow_mul_exp_neg k (hpos n)
  have hnorm : ∀ n, ∫ x in Ioi (0 : ℝ), ‖F n x‖ = k ! / ((n : ℝ) + 1) ^ (k + 1) := by
    intro n
    rw [← integral_pow_mul_exp_neg k (hpos n)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    exact Real.norm_of_nonneg (mul_nonneg (pow_nonneg (le_of_lt hx) _) (exp_pos _).le)
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (k + 1)) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k + 1))
    simpa using this
  have hsum : Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖F n x‖) := by
    simp_rw [hnorm, div_eq_mul_one_div (k ! : ℝ)]
    exact hs.mul_left _
  have key := integral_tsum_of_summable_integral_norm hint hsum
  have hL : ∑' n, ∫ x in Ioi (0 : ℝ), F n x = k ! * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (k + 1) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    rw [hF]
    simp only
    rw [integral_pow_mul_exp_neg k (hpos n), div_eq_mul_one_div]
  rw [← hL, key]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  simp only [hF]
  rw [tsum_mul_left, (hasSum_exp_neg_succ hx).tsum_eq, mul_one_div]

/-- Euler's evaluation `∑ₙ 1/(n+1)⁴ = π⁴/90` (shift of Mathlib's `hasSum_zeta_four`). -/
lemma tsum_one_div_succ_pow_four :
    ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 4 = π ^ 4 / 90 := by
  have h := hasSum_zeta_four
  have h' := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h'
  exact h'.tsum_eq

/-- **The Bose integral** `∫₀^∞ x³/(eˣ − 1) dx = π⁴/15`. -/
theorem integral_cube_div_exp_sub_one :
    ∫ x in Ioi (0 : ℝ), x ^ 3 / (rexp x - 1) = π ^ 4 / 15 := by
  rw [integral_pow_div_exp_sub_one 3 (by norm_num), tsum_one_div_succ_pow_four]
  norm_num [Nat.factorial]
  ring

end Lightlike.Cosmology.BoseIntegral

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_033.hasSum_exp_neg_succ := _root_.Lightlike.Cosmology.BoseIntegral.hasSum_exp_neg_succ
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_033.integrableOn_pow_mul_exp_neg := _root_.Lightlike.Cosmology.BoseIntegral.integrableOn_pow_mul_exp_neg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_033.integral_cube_div_exp_sub_one := _root_.Lightlike.Cosmology.BoseIntegral.integral_cube_div_exp_sub_one
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_033.integral_pow_div_exp_sub_one := _root_.Lightlike.Cosmology.BoseIntegral.integral_pow_div_exp_sub_one
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_033.integral_pow_mul_exp_neg := _root_.Lightlike.Cosmology.BoseIntegral.integral_pow_mul_exp_neg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_033.tsum_one_div_succ_pow_four := _root_.Lightlike.Cosmology.BoseIntegral.tsum_one_div_succ_pow_four
