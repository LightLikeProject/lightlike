import Mathlib
import Lightlike.Geometry.HeatKernel.Torus

/-!
# The shifted Gaussian sum

For `a > 0` and a real shift `s`, `Σ_{n∈ℤ} e^{-π a (n+s)²} = a^{-1/2} Σ_{n∈ℤ} e^{-π n²/a} e^{2π i n s}` (Poisson
summation with a real shift). The right side differs from `a^{-1/2}` by at most `a^{-1/2} Σ_{n≠0} e^{-π n²/a}`,
uniformly in `s`.
-/

open Complex Real

noncomputable section

namespace Lightlike.HeatKernel

/-- **Poisson summation with a real shift** (complex-valued). -/
theorem tsum_exp_neg_shift {a : ℝ} (ha : 0 < a) (s : ℝ) :
    ∑' n : ℤ, cexp (-(π : ℂ) * a * ((n : ℂ) + s) ^ 2) =
      (1 / (a : ℂ) ^ (1 / 2 : ℂ)) * ∑' n : ℤ, cexp (-(π : ℂ) / a * (n : ℂ) ^ 2 + 2 * π * Complex.I * n * s) := by
  have h := Complex.tsum_exp_neg_quadratic (a := (a : ℂ)) (by simpa using ha) (b := -(a : ℂ) * s)
  set E : ℂ := cexp (-(π : ℂ) * a * (s : ℂ) ^ 2) with hE
  have hA : ∀ n : ℤ, cexp (-(π : ℂ) * a * ((n : ℂ) + s) ^ 2) =
      cexp (-(π : ℂ) * a * (n : ℂ) ^ 2 + 2 * π * (-(a : ℂ) * s) * n) * E := by
    intro n
    rw [hE, ← Complex.exp_add]
    congr 1
    ring
  have hB : ∀ n : ℤ, cexp (-(π : ℂ) / a * (n : ℂ) ^ 2 + 2 * π * Complex.I * n * s) =
      cexp (-(π : ℂ) / a * ((n : ℂ) + Complex.I * (-(a : ℂ) * s)) ^ 2) * E := by
    intro n
    rw [hE, ← Complex.exp_add]
    congr 1
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    field_simp
    ring_nf
    simp [Complex.I_sq]
  simp only [hA, hB]
  rw [tsum_mul_right, tsum_mul_right, h]
  ring

/-- The Gaussian tail `Σ_{n≠0} e^{-π n²/a}`. -/
def gaussTail (a : ℝ) : ℝ := ∑' n : ℤ, if n = 0 then 0 else Real.exp (-π * (n : ℝ) ^ 2 / a)

/-- **The shifted Gaussian sum is within `a^{-1/2} Σ_{n≠0} e^{-π n²/a}` of `a^{-1/2}`, uniformly in the shift.** -/
theorem abs_tsum_shift_sub_le {a : ℝ} (ha : 0 < a) (s : ℝ) :
    |(∑' n : ℤ, Real.exp (-π * a * ((n : ℝ) + s) ^ 2)) - 1 / Real.sqrt a| ≤ 1 / Real.sqrt a * gaussTail a := by
  have h := tsum_exp_neg_shift ha s
  have hsq : (a : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt a : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    have := Complex.ofReal_cpow ha.le (1 / 2 : ℝ)
    push_cast at this
    exact this.symm
  have hsum : Summable fun n : ℤ => Real.exp (-π * (n : ℝ) ^ 2 / a) := by
    have := summable_exp_neg_int_sq (t := π / a) (by positivity)
    refine this.congr fun n => ?_
    congr 1; ring
  -- the real left side
  have hL : (∑' n : ℤ, cexp (-(π : ℂ) * a * ((n : ℂ) + s) ^ 2)) =
      ((∑' n : ℤ, Real.exp (-π * a * ((n : ℝ) + s) ^ 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    push_cast
    rfl
  set f : ℤ → ℂ := fun n => cexp (-(π : ℂ) / a * (n : ℂ) ^ 2 + 2 * π * Complex.I * n * s) with hf
  have hfn : ∀ n : ℤ, ‖f n‖ = Real.exp (-π * (n : ℝ) ^ 2 / a) := by
    intro n
    rw [hf]
    simp only [Complex.norm_exp]
    congr 1
    simp [Complex.add_re, Complex.mul_re, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, pow_two]
    field_simp
  have hfs : Summable f := Summable.of_norm (by simpa [hfn] using hsum)
  have hf0 : f 0 = 1 := by simp [hf]
  have hT : ∑' n : ℤ, f n = 1 + ∑' n : ℤ, (if n = 0 then (0 : ℂ) else f n) := by
    rw [hfs.tsum_eq_add_tsum_ite (0 : ℤ), hf0]
  set R : ℂ := ∑' n : ℤ, (if n = 0 then (0 : ℂ) else f n) with hR
  have hRle : ‖R‖ ≤ gaussTail a := by
    unfold gaussTail
    refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
    · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hsum
      by_cases hn : n = 0 <;> simp [hn, hfn]
    · refine tsum_congr fun n => ?_
      by_cases hn : n = 0 <;> simp [hn, hfn]
  have hmain : (((∑' n : ℤ, Real.exp (-π * a * ((n : ℝ) + s) ^ 2) : ℝ) : ℂ)) =
      ((1 / Real.sqrt a : ℝ) : ℂ) * (1 + R) := by
    rw [← hL, h, hsq, hT]
    push_cast
    ring
  have hdiff : (((∑' n : ℤ, Real.exp (-π * a * ((n : ℝ) + s) ^ 2) - 1 / Real.sqrt a : ℝ)) : ℂ) =
      ((1 / Real.sqrt a : ℝ) : ℂ) * R := by
    push_cast at hmain ⊢
    rw [hmain]; ring
  have := congrArg (fun z : ℂ => ‖z‖) hdiff
  simp only [Complex.norm_real, norm_mul, Real.norm_eq_abs] at this
  rw [this, abs_of_pos (by positivity : 0 < 1 / Real.sqrt a)]
  exact mul_le_mul_of_nonneg_left hRle (by positivity)

end Lightlike.HeatKernel
