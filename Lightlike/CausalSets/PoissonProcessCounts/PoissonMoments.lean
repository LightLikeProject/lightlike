import Mathlib

/-!
# Moments of the Poisson distribution on `ℕ`

Mathlib has `poissonMeasure r` on `ℕ` and its integral formula, but no moments. This file proves the
first two factorial moments, used for the Poisson point process of
`Lightlike/CausalSets/PoissonProcessCounts/Poisson.lean`:

* `integral_poissonMeasure_id`: `∫ n ∂Po(r) = r`;
* `integral_poissonMeasure_descFactorial`: `∫ n (n - 1) ∂Po(r) = r²`.

Both are integrable (`integrable_poissonMeasure_id`, `integrable_poissonMeasure_pair`).

## References

* G. Last, M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press (2017).
-/

open MeasureTheory ProbabilityTheory Real NNReal Nat

namespace Lightlike.Rows.G2_063

/-- The Poisson weights times `n` sum to `r`. -/
lemma hasSum_poisson_mean (r : ℝ≥0) :
    HasSum (fun n : ℕ => exp (-(r : ℝ)) * (r : ℝ) ^ n / (n)! * (n : ℝ)) (r : ℝ) := by
  have h1 := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, sub_zero]
  convert h1 using 1
  · funext n
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · simp

/-- The Poisson weights times `n (n - 1)` sum to `r²`. -/
lemma hasSum_poisson_pair (r : ℝ≥0) :
    HasSum (fun n : ℕ => exp (-(r : ℝ)) * (r : ℝ) ^ n / (n)! * ((n : ℝ) * ((n : ℝ) - 1)))
      ((r : ℝ) ^ 2) := by
  have h1 := (hasSum_one_poissonMeasure r).mul_left ((r : ℝ) ^ 2)
  rw [← hasSum_nat_add_iff' 2]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
    Nat.cast_one, zero_sub, mul_zero, sub_self, zero_add, mul_neg, mul_one, add_zero]
  convert h1 using 1
  · funext n
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · simp

lemma integrable_poissonMeasure_id (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  refine (hasSum_poisson_mean r).summable.congr fun n => ?_
  rw [Real.norm_natCast]

lemma integrable_poissonMeasure_pair (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  refine (hasSum_poisson_pair r).summable.congr fun n => ?_
  congr 1
  rw [Real.norm_of_nonneg]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg (by linarith) (by linarith)

/-- **Mean of the Poisson law**: `∫ n ∂Po(r) = r`. -/
theorem integral_poissonMeasure_id (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ∂poissonMeasure r = r := by
  rw [integral_poissonMeasure]
  simpa [smul_eq_mul] using (hasSum_poisson_mean r).tsum_eq

/-- **Second factorial moment of the Poisson law**: `∫ n (n - 1) ∂Po(r) = r²`. -/
theorem integral_poissonMeasure_descFactorial (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) * ((n : ℝ) - 1) ∂poissonMeasure r = (r : ℝ) ^ 2 := by
  rw [integral_poissonMeasure]
  simpa [smul_eq_mul] using (hasSum_poisson_pair r).tsum_eq

end Lightlike.Rows.G2_063
