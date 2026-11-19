import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The quartic zero-dimensional field theory: the asymptotic expansion

`integral_pow_mul_gauss`: `∫ x^{2n} e^{-x²/2} dx = √(2π) (2n - 1)!!`; `integral_pow_mul_gauss_scaled` with variance
`s`; `wick_one_variable`: the one-variable Wick identity `∫ dx/√(2πħ) e^{-x²/(2aħ)} x^{2n} = √a (aħ)^n (2n - 1)!!`
exactly as in Borinsky (2018), §3.1, p. 22, before Definition 3.1.1.

`abs_exp_neg_sub_sum_le`: for `t ≥ 0`, `|e^{-t} - ∑_{m<M} (-t)^m/m!| ≤ t^M/M!`.

`quartic_expansion`: for `g ≥ 0` and every `M`,
`|∫ e^{-x²/2 - g x⁴/24} dx - √(2π) ∑_{m<M} (-g/24)^m (4m - 1)!!/m!| ≤ √(2π) (g/24)^M (4M - 1)!!/M!`:
the series is the asymptotic expansion of the integral as `g → 0⁺`, with the next term as error bound.
-/

open MeasureTheory Set Real Nat

noncomputable section

namespace Lightlike.FieldTheory

/-- **The Gaussian moments in one variable**: `∫ x^{2n} e^{-x²/2} dx = √(2π) (2n - 1)!!`. -/
theorem integral_pow_mul_gauss (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) * Real.exp (-(x ^ 2 / 2)) = √(2 * π) * ((2 * n - 1)‼ : ℕ) := by
  have h1 : ∀ x : ℝ, x ^ (2 * n) * Real.exp (-(x ^ 2 / 2)) =
      |x| ^ ((2 * n : ℕ) : ℝ) * Real.exp (-(1 / 2) * |x| ^ (2 : ℝ)) := by
    intro x
    have e1 : |x| ^ ((2 * n : ℕ) : ℝ) = x ^ (2 * n) := by
      rw [Real.rpow_natCast, pow_mul, pow_mul, sq_abs]
    have e2 : |x| ^ (2 : ℝ) = x ^ 2 := by rw [Real.rpow_two, sq_abs]
    rw [e1, e2]
    congr 2
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h1),
    integral_comp_abs (f := fun y : ℝ => y ^ ((2 * n : ℕ) : ℝ) * Real.exp (-(1 / 2) * y ^ (2 : ℝ))),
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num)
      (by have : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) (by norm_num)]
  have hG : Real.Gamma ((((2 * n : ℕ) : ℝ) + 1) / 2) = (2 * n - 1 : ℕ)‼ * √π / 2 ^ n := by
    rw [← Real.Gamma_nat_add_half n]; congr 1; push_cast; ring
  have hp : ((1 : ℝ) / 2) ^ (-(((2 * n : ℕ) : ℝ) + 1) / 2) = 2 ^ n * √2 := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_div, neg_neg,
      show (((2 * n : ℕ) : ℝ) + 1) / 2 = (n : ℝ) + 1 / 2 by push_cast; ring,
      Real.rpow_add (by norm_num), Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  rw [hG, hp, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

/-- **The Gaussian moments with variance `s`**: `∫ x^{2n} e^{-x²/(2s)} dx = √(2π s) s^n (2n - 1)!!` for `s > 0`. -/
theorem integral_pow_mul_gauss_scaled (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ∫ x : ℝ, x ^ (2 * n) * Real.exp (-(x ^ 2 / (2 * s))) = √(2 * π * s) * s ^ n * ((2 * n - 1)‼ : ℕ) := by
  have hq : 0 < √s := Real.sqrt_pos.2 hs
  have hss : √s ^ 2 = s := Real.sq_sqrt hs.le
  have h := Measure.integral_comp_mul_left (fun x : ℝ => x ^ (2 * n) * Real.exp (-(x ^ 2 / (2 * s)))) (√s)
  have e : ∀ y : ℝ, (√s * y) ^ (2 * n) * Real.exp (-((√s * y) ^ 2 / (2 * s))) =
      s ^ n * (y ^ (2 * n) * Real.exp (-(y ^ 2 / 2))) := by
    intro y
    have he : (√s * y) ^ 2 / (2 * s) = y ^ 2 / 2 := by
      rw [mul_pow, hss]; field_simp
    rw [he, mul_pow, pow_mul (√s) 2 n, hss, mul_assoc]
  simp only [e] at h
  rw [integral_const_mul, integral_pow_mul_gauss, abs_inv, abs_of_pos hq, smul_eq_mul] at h
  have hI : ∫ x : ℝ, x ^ (2 * n) * Real.exp (-(x ^ 2 / (2 * s))) =
      √s * (s ^ n * (√(2 * π) * ((2 * n - 1)‼ : ℕ))) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
  rw [hI, Real.sqrt_mul (by positivity) s]; ring

/-- **The zero-dimensional Wick identity** in the form of Borinsky (2018), §3.1, p. 22 (before Definition 3.1.1):
`∫ dx/√(2πħ) e^{-x²/(2aħ)} x^{2n} = √a (aħ)^n (2n - 1)!!` for `a, ħ > 0`. -/
theorem wick_one_variable (n : ℕ) {a ħ : ℝ} (ha : 0 < a) (hħ : 0 < ħ) :
    ∫ x : ℝ, Real.exp (-(x ^ 2 / (2 * a * ħ))) * x ^ (2 * n) / √(2 * π * ħ) =
      √a * (a * ħ) ^ n * ((2 * n - 1)‼ : ℕ) := by
  have hs : 0 < a * ħ := mul_pos ha hħ
  have h := integral_pow_mul_gauss_scaled n hs
  have hc : (fun x : ℝ => Real.exp (-(x ^ 2 / (2 * a * ħ))) * x ^ (2 * n) / √(2 * π * ħ)) =
      fun x => x ^ (2 * n) * Real.exp (-(x ^ 2 / (2 * (a * ħ)))) / √(2 * π * ħ) := by
    funext x; rw [mul_comm, ← mul_assoc 2 a ħ]
  rw [hc, integral_div, h, show 2 * π * (a * ħ) = (2 * π * ħ) * a by ring,
    Real.sqrt_mul (by positivity) a]
  have hp : 0 < √(2 * π * ħ) := Real.sqrt_pos.2 (by positivity)
  field_simp

/-- The Taylor remainder of `e^{-t}`. -/
def expNegRem (M : ℕ) (t : ℝ) : ℝ := Real.exp (-t) - ∑ m ∈ Finset.range M, (-t) ^ m / (m.factorial : ℝ)

lemma hasDerivAt_expNegRem (M : ℕ) (t : ℝ) : HasDerivAt (expNegRem (M + 1)) (-expNegRem M t) t := by
  unfold expNegRem
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    have := (hasDerivAt_neg t).exp
    simpa using this
  have h2 : HasDerivAt (fun s : ℝ => ∑ m ∈ Finset.range (M + 1), (-s) ^ m / (m.factorial : ℝ))
      (-∑ m ∈ Finset.range M, (-t) ^ m / (m.factorial : ℝ)) t := by
    have hterm : ∀ m ∈ Finset.range (M + 1), HasDerivAt (fun s : ℝ => (-s) ^ m / (m.factorial : ℝ))
        ((m : ℝ) * (-t) ^ (m - 1) * (-1) / (m.factorial : ℝ)) t := by
      intro m _
      have := ((hasDerivAt_neg t).pow m).div_const (m.factorial : ℝ)
      convert this using 1
    have hs := HasDerivAt.sum hterm
    convert hs using 1
    · ext s; simp [Finset.sum_apply]
    · rw [Finset.sum_range_succ', ← Finset.sum_neg_distrib]
      simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Nat.factorial_succ, Nat.add_sub_cancel]
      push_cast
      have : (m.factorial : ℝ) ≠ 0 := by positivity
      field_simp
  have := h1.sub h2
  convert this using 1
  ring

lemma expNegRem_zero_point (M : ℕ) : expNegRem (M + 1) 0 = 0 := by
  unfold expNegRem
  rw [Finset.sum_range_succ']
  simp

lemma continuous_expNegRem (M : ℕ) : Continuous (expNegRem M) := by
  unfold expNegRem; fun_prop

/-- **The alternating Taylor bound**: for `t ≥ 0`, `|e^{-t} - ∑_{m<M} (-t)^m/m!| ≤ t^M/M!`. -/
theorem abs_exp_neg_sub_sum_le (M : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |expNegRem M t| ≤ t ^ M / (M.factorial : ℝ) := by
  induction M generalizing t with
  | zero =>
    unfold expNegRem
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one]
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  | succ M ih =>
    have hFTC : expNegRem (M + 1) t = ∫ s in (0 : ℝ)..t, -expNegRem M s := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_expNegRem M s)
        ((continuous_expNegRem M).neg.intervalIntegrable _ _), expNegRem_zero_point, sub_zero]
    rw [hFTC]
    calc |∫ s in (0 : ℝ)..t, -expNegRem M s| ≤ ∫ s in (0 : ℝ)..t, |-expNegRem M s| :=
          intervalIntegral.abs_integral_le_integral_abs ht
      _ ≤ ∫ s in (0 : ℝ)..t, s ^ M / (M.factorial : ℝ) := by
          refine intervalIntegral.integral_mono_on ht ((continuous_expNegRem M).neg.abs.intervalIntegrable _ _)
            ((by fun_prop : Continuous fun s : ℝ => s ^ M / (M.factorial : ℝ)).intervalIntegrable _ _)
            fun s hs => ?_
          rw [abs_neg]; exact ih hs.1
      _ = t ^ (M + 1) / ((M + 1).factorial : ℝ) := by
          rw [intervalIntegral.integral_div, integral_pow, Nat.factorial_succ]
          push_cast
          have : (M.factorial : ℝ) ≠ 0 := by positivity
          field_simp
          ring

/-- `x^{2k} e^{-x²/2}` is integrable (bounded by `k! 4^k e^{-x²/4}`). -/
lemma integrable_pow_mul_gauss (k : ℕ) : Integrable (fun x : ℝ => x ^ (2 * k) * Real.exp (-(x ^ 2 / 2))) := by
  have hI : Integrable (fun x : ℝ => ((k.factorial : ℝ) * 4 ^ k) * Real.exp (-(1 / 4) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _
  refine hI.mono' (by fun_prop : Continuous fun x : ℝ => x ^ (2 * k) * Real.exp (-(x ^ 2 / 2))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hy : 0 ≤ x ^ 2 / 4 := by positivity
  have h1 := Real.pow_div_factorial_le_exp _ hy k
  have hf : (0 : ℝ) < k.factorial := by positivity
  rw [Real.norm_of_nonneg (by rw [pow_mul]; positivity)]
  have h2 : x ^ (2 * k) ≤ (k.factorial : ℝ) * 4 ^ k * Real.exp (x ^ 2 / 4) := by
    rw [div_le_iff₀ hf] at h1
    calc x ^ (2 * k) = 4 ^ k * (x ^ 2 / 4) ^ k := by rw [div_pow, pow_mul]; field_simp
      _ ≤ 4 ^ k * (Real.exp (x ^ 2 / 4) * k.factorial) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have e1 : Real.exp (-(x ^ 2 / 2)) = Real.exp (-(1 / 4) * x ^ 2) * Real.exp (-(x ^ 2 / 4)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc x ^ (2 * k) * Real.exp (-(x ^ 2 / 2))
      ≤ ((k.factorial : ℝ) * 4 ^ k * Real.exp (x ^ 2 / 4)) * Real.exp (-(x ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = ((k.factorial : ℝ) * 4 ^ k) * Real.exp (-(1 / 4) * x ^ 2) := by
        have e2 : Real.exp (x ^ 2 / 4) * Real.exp (-(x ^ 2 / 4)) = 1 := by rw [← Real.exp_add]; simp
        rw [e1]
        calc (k.factorial : ℝ) * 4 ^ k * Real.exp (x ^ 2 / 4) *
              (Real.exp (-(1 / 4) * x ^ 2) * Real.exp (-(x ^ 2 / 4)))
            = (k.factorial : ℝ) * 4 ^ k * Real.exp (-(1 / 4) * x ^ 2) *
              (Real.exp (x ^ 2 / 4) * Real.exp (-(x ^ 2 / 4))) := by ring
          _ = _ := by rw [e2, mul_one]

/-- **The asymptotic expansion of the quartic integral**: for `g ≥ 0` and every `M`,
`|∫ e^{-x²/2 - g x⁴/24} dx - √(2π) ∑_{m<M} (-g/24)^m (4m - 1)!!/m!| ≤ √(2π) (g/24)^M (4M - 1)!!/M!`. -/
theorem quartic_expansion {g : ℝ} (hg : 0 ≤ g) (M : ℕ) :
    |(∫ x : ℝ, Real.exp (-(x ^ 2 / 2) - g * x ^ 4 / 24)) -
        √(2 * π) * ∑ m ∈ Finset.range M, (-g / 24) ^ m * ((4 * m - 1)‼ : ℕ) / (m.factorial : ℝ)| ≤
      √(2 * π) * ((g / 24) ^ M * ((4 * M - 1)‼ : ℕ) / (M.factorial : ℝ)) := by
  set t : ℝ → ℝ := fun x => g * x ^ 4 / 24 with ht
  have ht0 : ∀ x, 0 ≤ t x := fun x => by simp only [ht]; positivity
  have hpow : ∀ (m : ℕ) (x : ℝ), (-t x) ^ m = (-g / 24) ^ m * x ^ (2 * (2 * m)) := by
    intro m x; simp only [ht]; rw [show 2 * (2 * m) = 4 * m by ring, pow_mul, ← mul_pow]; congr 1; ring
  -- the integrand split
  have hsplit : ∀ x : ℝ, Real.exp (-(x ^ 2 / 2) - g * x ^ 4 / 24) =
      (∑ m ∈ Finset.range M, (-g / 24) ^ m / (m.factorial : ℝ) * (x ^ (2 * (2 * m)) * Real.exp (-(x ^ 2 / 2)))) +
        Real.exp (-(x ^ 2 / 2)) * expNegRem M (t x) := by
    intro x
    have e0 : Real.exp (-(x ^ 2 / 2) - g * x ^ 4 / 24) = Real.exp (-(x ^ 2 / 2)) * Real.exp (-t x) := by
      rw [← Real.exp_add]; congr 1
    rw [e0]
    unfold expNegRem
    rw [mul_sub, Finset.mul_sum]
    have e : ∀ m ∈ Finset.range M, Real.exp (-(x ^ 2 / 2)) * ((-t x) ^ m / (m.factorial : ℝ)) =
        (-g / 24) ^ m / (m.factorial : ℝ) * (x ^ (2 * (2 * m)) * Real.exp (-(x ^ 2 / 2))) := fun m _ => by
      rw [hpow]; ring
    rw [Finset.sum_congr rfl e]
    ring
  have hI : ∀ m : ℕ, Integrable (fun x : ℝ => (-g / 24) ^ m / (m.factorial : ℝ) *
      (x ^ (2 * (2 * m)) * Real.exp (-(x ^ 2 / 2)))) := fun m => (integrable_pow_mul_gauss (2 * m)).const_mul _
  have hR : Integrable (fun x : ℝ => Real.exp (-(x ^ 2 / 2)) * expNegRem M (t x)) := by
    refine (((integrable_pow_mul_gauss (2 * M)).const_mul ((g / 24) ^ M / (M.factorial : ℝ)))).mono'
      ((by fun_prop : Continuous fun x : ℝ => Real.exp (-(x ^ 2 / 2))).mul
        ((continuous_expNegRem M).comp (by fun_prop : Continuous t))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
    have h1 := abs_exp_neg_sub_sum_le M (ht0 x)
    have h2 : t x ^ M = (g / 24) ^ M * x ^ (2 * (2 * M)) := by
      simp only [ht]; rw [show 2 * (2 * M) = 4 * M by ring, pow_mul, ← mul_pow]; congr 1; ring
    rw [h2] at h1
    calc Real.exp (-(x ^ 2 / 2)) * |expNegRem M (t x)|
        ≤ Real.exp (-(x ^ 2 / 2)) * ((g / 24) ^ M * x ^ (2 * (2 * M)) / (M.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = _ := by ring
  simp_rw [hsplit]
  rw [integral_add (integrable_finsetSum _ fun m _ => hI m) hR, integral_finsetSum _ fun m _ => hI m]
  have hmom : ∀ m ∈ Finset.range M, ∫ x : ℝ, (-g / 24) ^ m / (m.factorial : ℝ) *
      (x ^ (2 * (2 * m)) * Real.exp (-(x ^ 2 / 2))) =
      √(2 * π) * ((-g / 24) ^ m * ((4 * m - 1)‼ : ℕ) / (m.factorial : ℝ)) := by
    intro m _
    rw [integral_const_mul, integral_pow_mul_gauss, show 2 * (2 * m) - 1 = 4 * m - 1 by omega]
    ring
  rw [Finset.sum_congr rfl hmom, ← Finset.mul_sum, add_sub_cancel_left]
  calc |∫ x : ℝ, Real.exp (-(x ^ 2 / 2)) * expNegRem M (t x)|
      ≤ ∫ x : ℝ, |Real.exp (-(x ^ 2 / 2)) * expNegRem M (t x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x : ℝ, (g / 24) ^ M / (M.factorial : ℝ) * (x ^ (2 * (2 * M)) * Real.exp (-(x ^ 2 / 2))) := by
        refine integral_mono hR.abs ((integrable_pow_mul_gauss (2 * M)).const_mul _) fun x => ?_
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        have h1 := abs_exp_neg_sub_sum_le M (ht0 x)
        have h2 : t x ^ M = (g / 24) ^ M * x ^ (2 * (2 * M)) := by
          simp only [ht]; rw [show 2 * (2 * M) = 4 * M by ring, pow_mul, ← mul_pow]; congr 1; ring
        rw [h2] at h1
        calc Real.exp (-(x ^ 2 / 2)) * |expNegRem M (t x)|
            ≤ Real.exp (-(x ^ 2 / 2)) * ((g / 24) ^ M * x ^ (2 * (2 * M)) / (M.factorial : ℝ)) :=
              mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
          _ = _ := by ring
    _ = √(2 * π) * ((g / 24) ^ M * ((4 * M - 1)‼ : ℕ) / (M.factorial : ℝ)) := by
        rw [integral_const_mul, integral_pow_mul_gauss, show 2 * (2 * M) - 1 = 4 * M - 1 by omega]
        ring

end Lightlike.FieldTheory
