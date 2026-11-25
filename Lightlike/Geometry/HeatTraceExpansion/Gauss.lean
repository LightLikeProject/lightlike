import Mathlib
import Lightlike.Geometry.HeatTraceExpansion.Taylor

/-!
# The Gaussian derivative chain

`gu i y = (pp i).eval y * exp (-y^2)` is the `i`-th derivative of `-exp (-y^2)`.  In particular
`gu 1 y = 2 y exp (-y^2)` is the function whose midpoint Riemann sums give the sphere heat trace
(`Sphere.lean`).  We prove that `gu` is a derivative chain, its values at `0`, and the decay bound
`|gu i y| ≤ C / (1 + y^2)`.
-/

open Polynomial Set

namespace Lightlike.Rows.G1_062

lemma gauss_pow_le (M : ℕ) (y : ℝ) :
    (1 + y ^ 2) ^ M * Real.exp (-y ^ 2) ≤ Real.exp 1 * M.factorial := by
  have h := Real.pow_div_factorial_le_exp (1 + y ^ 2) (by positivity) M
  have hf : (0 : ℝ) < M.factorial := by exact_mod_cast M.factorial_pos
  rw [div_le_iff₀ hf, Real.exp_add] at h
  have h1 : Real.exp (y ^ 2) * Real.exp (-y ^ 2) = 1 := by rw [← Real.exp_add]; simp
  calc (1 + y ^ 2) ^ M * Real.exp (-y ^ 2)
      ≤ (Real.exp 1 * Real.exp (y ^ 2) * M.factorial) * Real.exp (-y ^ 2) := by
        gcongr
    _ = Real.exp 1 * M.factorial * (Real.exp (y ^ 2) * Real.exp (-y ^ 2)) := by ring
    _ = _ := by rw [h1, mul_one]

lemma poly_le (p : ℝ[X]) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℝ, |p.eval y| ≤ A * (1 + y ^ 2) ^ p.natDegree := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), fun y => ?_⟩
  rw [eval_eq_sum_range, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_pow]
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : |y| ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg (|y| - 1), sq_abs y]
  have h2 : |y| ^ i ≤ (1 + y ^ 2) ^ p.natDegree :=
    calc |y| ^ i ≤ (1 + y ^ 2) ^ i := pow_le_pow_left₀ (abs_nonneg _) h1 i
      _ ≤ _ := pow_le_pow_right₀ (by nlinarith [sq_nonneg y]) hi'
  exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

/-- A polynomial times the Gaussian decays faster than any `(1 + y^2)^{-k}`. -/
lemma polyGauss_bound (p : ℝ[X]) (k : ℕ) :
    ∃ C : ℝ, ∀ y : ℝ, |p.eval y * Real.exp (-y ^ 2)| * (1 + y ^ 2) ^ k ≤ C := by
  obtain ⟨A, hA0, hA⟩ := poly_le p
  refine ⟨A * (Real.exp 1 * ((p.natDegree + k).factorial : ℝ)), fun y => ?_⟩
  have he : 0 < Real.exp (-y ^ 2) := Real.exp_pos _
  rw [abs_mul, abs_of_pos he]
  have h1 := gauss_pow_le (p.natDegree + k) y
  have hpos : 0 < (1 + y ^ 2) ^ k := by positivity
  calc |p.eval y| * Real.exp (-y ^ 2) * (1 + y ^ 2) ^ k
      ≤ (A * (1 + y ^ 2) ^ p.natDegree) * Real.exp (-y ^ 2) * (1 + y ^ 2) ^ k := by
        gcongr; exact hA y
    _ = A * ((1 + y ^ 2) ^ (p.natDegree + k) * Real.exp (-y ^ 2)) := by ring
    _ ≤ _ := by gcongr

/-- Polynomials with `pp i * exp (-y^2)` the `i`-th derivative of `-exp(-y^2)`. -/
noncomputable def pp : ℕ → ℝ[X]
  | 0 => -1
  | n + 1 => derivative (pp n) - 2 * X * pp n

/-- The derivative chain of `y ↦ -exp (-y^2)`. -/
noncomputable def gu (i : ℕ) (y : ℝ) : ℝ := (pp i).eval y * Real.exp (-y ^ 2)

lemma gu_chain : IsChain gu := by
  intro i y
  have h1 := (pp i).hasDerivAt y
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2)) (Real.exp (-y ^ 2) * (-(2 * y))) y := by
    have := ((hasDerivAt_pow 2 y).neg).exp
    simpa using this
  have h3 := h1.mul h2
  unfold gu
  refine h3.congr_deriv ?_
  simp only [pp, eval_sub, eval_mul, eval_ofNat, eval_X]
  ring

lemma gu_one (y : ℝ) : gu 1 y = 2 * y * Real.exp (-y ^ 2) := by
  simp [gu, pp]

lemma gu_zero_zero : gu 0 0 = -1 := by simp [gu, pp]

lemma gu_two_zero : gu 2 0 = 2 := by simp [gu, pp]

lemma gu_four_zero : gu 4 0 = -12 := by simp [gu, pp]; norm_num

/-- decay: `|gu i y| ≤ C / (1 + y²)` in the form `|gu i y| * (1 + y²) ≤ C`. -/
lemma gu_decay (i : ℕ) : ∃ C : ℝ, ∀ y : ℝ, |gu i y| * (1 + y ^ 2) ≤ C := by
  obtain ⟨C, hC⟩ := polyGauss_bound (pp i) 1
  exact ⟨C, fun y => by simpa [gu] using hC y⟩

end Lightlike.Rows.G1_062
