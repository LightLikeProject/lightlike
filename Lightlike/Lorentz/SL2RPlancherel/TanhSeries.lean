import Mathlib

/-!
# The series `∑ ρ/(ρ² + (2m+1)²) = (π/4) tanh (πρ/2)`

This is the source of the `tanh` in the Plancherel density `ρ tanh (πρ)` of the principal
series of `SL(2,ℝ)`: after the Abel transform, the kernel is `1/sinh`, whose sine transform
is `(π/2) tanh (πρ/2)` (expanded as `1/sinh t = 2 ∑ e^{-(2m+1)t}`).  Here the series itself
is derived from Mathlib's Mittag-Leffler expansion of the cotangent at `x = (1 + iρ)/2`.
-/

namespace Lightlike.Lorentz.SL2RPlancherel

open Complex Filter Topology

/-- The point `(1 + iρ)/2`, which is not an integer. -/
private noncomputable def xpt (ρ : ℝ) : ℂ := (1 + ρ * I) / 2

private lemma xpt_mem (ρ : ℝ) : xpt ρ ∈ integerComplement := by
  rintro ⟨n, hn⟩
  have := congrArg Complex.re hn
  simp [xpt] at this
  have h2 : (2 * (n : ℝ)) = 1 := by linarith
  have : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

private lemma xpt_add_ne (ρ : ℝ) (m : ℕ) : xpt ρ + m ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [xpt] at this
  have : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith

private lemma xpt_sub_ne (ρ : ℝ) (m : ℕ) : xpt ρ - (m + 1) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [xpt] at this
  have : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith

private lemma pair_eq (ρ : ℝ) (m : ℕ) :
    1 / (xpt ρ + m) + 1 / (xpt ρ - (m + 1)) =
      -4 * I * ((ρ / (ρ ^ 2 + (2 * m + 1) ^ 2) : ℝ) : ℂ) := by
  have h1 := xpt_add_ne ρ m
  have h2 := xpt_sub_ne ρ m
  have hd : ((ρ : ℂ) ^ 2 + (2 * m + 1) ^ 2) ≠ 0 := by
    have : (ρ ^ 2 + (2 * m + 1) ^ 2 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have h1' : (2 * m + 1 + ρ * I : ℂ) ≠ 0 := by
    intro h; apply h1; simp only [xpt]; linear_combination h / 2
  have h2' : (ρ * I - 2 * m - 1 : ℂ) ≠ 0 := by
    intro h; apply h2; simp only [xpt]; linear_combination h / 2
  push_cast
  simp only [xpt] at *
  have h3 : (1 + ρ * I + 2 * m : ℂ) ≠ 0 := by
    intro h; apply h1'; linear_combination h
  have h4 : (1 + ρ * I - 2 * (m + 1) : ℂ) ≠ 0 := by
    intro h; apply h2'; linear_combination h
  field_simp
  ring_nf
  linear_combination (4 * (ρ : ℂ) ^ 3 * I) * Complex.I_sq

private lemma partial_sum_eq (ρ : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 / (xpt ρ - (n + 1)) + 1 / (xpt ρ + (n + 1))) + 1 / xpt ρ =
      ∑ m ∈ Finset.range N, (-4 * I * ((ρ / (ρ ^ 2 + (2 * m + 1) ^ 2) : ℝ) : ℂ))
        + 1 / (xpt ρ + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, add_right_comm, ih, ← pair_eq ρ N]
    push_cast
    ring

private lemma cot_xpt (ρ : ℝ) :
    (Real.pi : ℂ) * cot (Real.pi * xpt ρ) =
      -(I * ((Real.pi * Real.tanh (Real.pi * ρ / 2) : ℝ) : ℂ)) := by
  have : (Real.pi : ℂ) * xpt ρ = ((Real.pi * ρ / 2 : ℝ) : ℂ) * I + Real.pi / 2 := by
    simp [xpt]; ring
  rw [this, Complex.cot_eq_cos_div_sin, Complex.cos_add_pi_div_two,
    Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.sin_mul_I]
  have hc : Complex.cosh ((Real.pi : ℂ) * ρ / 2) ≠ 0 := by
    have e : ((Real.pi : ℂ) * ρ / 2) = ((Real.pi * ρ / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, ← Complex.ofReal_cosh]; exact_mod_cast (Real.cosh_pos _).ne'
  push_cast
  rw [Complex.tanh_eq_sinh_div_cosh]
  field_simp

/-- `∑_{m ≥ 0} ρ/(ρ² + (2m+1)²) = (π/4) tanh (πρ/2)`, for `ρ ≥ 0` (both sides are odd in `ρ`;
the hypothesis is only used to show the terms are nonnegative). -/
theorem hasSum_tanh_series {ρ : ℝ} (hρ : 0 ≤ ρ) :
    HasSum (fun m : ℕ => ρ / (ρ ^ 2 + (2 * m + 1) ^ 2))
      (Real.pi / 4 * Real.tanh (Real.pi * ρ / 2)) := by
  have hT := tendsto_logDeriv_euler_cot_sub (xpt_mem ρ)
  have hN : Tendsto (fun N : ℕ => 1 / (xpt ρ + N)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : Tendsto (fun N : ℕ => 2 * (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hb
    have hre : ((N : ℝ) + 1) / 2 ≤ ‖xpt ρ + N‖ := by
      have := Complex.abs_re_le_norm (xpt ρ + N)
      have h2 : (xpt ρ + N).re = 1 / 2 + N := by simp [xpt]
      rw [h2, abs_of_nonneg (by positivity)] at this
      linarith
    rw [norm_div, norm_one]
    have hp : (0:ℝ) < ((N : ℝ) + 1) / 2 := by positivity
    calc 1 / ‖xpt ρ + N‖ ≤ 1 / (((N : ℝ) + 1) / 2) :=
          one_div_le_one_div_of_le hp hre
      _ = 2 * (1 / ((N : ℝ) + 1)) := by field_simp
  have hS : Tendsto (fun N : ℕ => (I / 4) *
      (∑ n ∈ Finset.range N, (1 / (xpt ρ - (n + 1)) + 1 / (xpt ρ + (n + 1)))
        + 1 / xpt ρ - 1 / (xpt ρ + N))) atTop
      (𝓝 ((I / 4) * (-(I * ((Real.pi * Real.tanh (Real.pi * ρ / 2) : ℝ) : ℂ))))) := by
    have h1 := (hT.add_const (1 / xpt ρ)).sub hN
    have e : (Real.pi : ℂ) * cot (Real.pi * xpt ρ) - 1 / xpt ρ + 1 / xpt ρ - 0 =
        -(I * ((Real.pi * Real.tanh (Real.pi * ρ / 2) : ℝ) : ℂ)) := by
      rw [sub_zero, sub_add_cancel]; exact cot_xpt ρ
    rw [e] at h1
    exact h1.const_mul _
  have hS' : Tendsto (fun N : ℕ => ((∑ m ∈ Finset.range N,
      (ρ / (ρ ^ 2 + (2 * m + 1) ^ 2)) : ℝ) : ℂ)) atTop
      (𝓝 (((Real.pi / 4 * Real.tanh (Real.pi * ρ / 2) : ℝ) : ℂ))) := by
    have e1 : ∀ N : ℕ, ((∑ m ∈ Finset.range N,
        (ρ / (ρ ^ 2 + (2 * m + 1) ^ 2)) : ℝ) : ℂ) = (I / 4) *
        (∑ n ∈ Finset.range N, (1 / (xpt ρ - (n + 1)) + 1 / (xpt ρ + (n + 1)))
          + 1 / xpt ρ - 1 / (xpt ρ + N)) := by
      intro N
      rw [partial_sum_eq, add_sub_cancel_right, Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      linear_combination (((ρ / (ρ ^ 2 + (2 * m + 1) ^ 2) : ℝ) : ℂ)) * Complex.I_sq
    have e2 : (I / 4) * (-(I * ((Real.pi * Real.tanh (Real.pi * ρ / 2) : ℝ) : ℂ))) =
        ((Real.pi / 4 * Real.tanh (Real.pi * ρ / 2) : ℝ) : ℂ) := by
      rw [show Real.pi / 4 * Real.tanh (Real.pi * ρ / 2) =
        (Real.pi * Real.tanh (Real.pi * ρ / 2)) / 4 by ring, Complex.ofReal_div]
      have h4 : ((4 : ℝ) : ℂ) = 4 := by norm_num
      rw [h4]
      linear_combination (-((Real.pi * Real.tanh (Real.pi * ρ / 2) : ℝ) : ℂ) / 4) * Complex.I_sq
    rw [← e2]
    exact hS.congr (fun N => (e1 N).symm)
  have hR : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N,
      (ρ / (ρ ^ 2 + (2 * m + 1) ^ 2))) atTop (𝓝 (Real.pi / 4 * Real.tanh (Real.pi * ρ / 2))) :=
    by
      have := (Complex.continuous_re.tendsto _).comp hS'
      simp only [Function.comp_def, Complex.ofReal_re] at this
      exact this
  have hnn : ∀ m : ℕ, 0 ≤ ρ / (ρ ^ 2 + (2 * m + 1) ^ 2) := by
    intro m
    positivity
  exact (hasSum_iff_tendsto_nat_of_nonneg hnn _).mpr hR

end Lightlike.Lorentz.SL2RPlancherel
