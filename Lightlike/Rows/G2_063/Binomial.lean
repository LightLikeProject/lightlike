import Mathlib
import Lightlike.Rows.G2_063.Poisson2

/-!
# The binomial process has dependent counts

For a fixed number `n` of independent points of law `ν` (the *binomial process*), the counts in two
disjoint sets `A`, `B` are *negatively correlated*:
`Cov(N_A, N_B) = - n ν(A) ν(B) < 0` when `n ≥ 1` and `ν A, ν B > 0`. So they are not independent,
in contrast to the Poisson process (`cov_poissonProcess_ptCount`: covariance `0` on disjoint sets).

## Main results

* `integral_sample_ptCount_mul`: `E[N_A N_B] = n ν(A ∩ B) + n (n - 1) ν(A) ν(B)`.
* `cov_sample_ptCount_disjoint`: for disjoint `A`, `B`, `E[N_A N_B] - E N_A E N_B = - n ν(A) ν(B)`.
* `not_indepCount_sample`: the counts of two disjoint sets of positive measure are not
  uncorrelated, hence not independent, for `n ≥ 1`.

## References

* G. Last, M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press (2017).
-/

open MeasureTheory ProbabilityTheory

namespace Lightlike.Rows.G2_063

variable {α : Type*} [MeasurableSpace α]

lemma integrable_sample_ptCount (ν : Measure α) [IsProbabilityMeasure ν] {A : Set α}
    (hA : MeasurableSet A) (n : ℕ) :
    Integrable (fun x : ℕ → α => (ptCount A n x : ℝ)) (sample ν) :=
  Integrable.of_bound (measurable_ptCount_real A hA n).aestronglyMeasurable (n : ℝ)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast ptCount_le A n x)

lemma integrable_sample_pairCount (ν : Measure α) [IsProbabilityMeasure ν] {R : Set (α × α)}
    (hR : MeasurableSet R) (n : ℕ) :
    Integrable (fun x : ℕ → α => (pairCount R n x : ℝ)) (sample ν) :=
  Integrable.of_bound (measurable_pairCount_real R hR n).aestronglyMeasurable ((n : ℝ) * n)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast pairCount_le R n x)

/-- **Second moment of two counts of a binomial process**:
`E[N_A N_B] = n ν(A ∩ B) + n (n - 1) ν(A) ν(B)`. -/
theorem integral_sample_ptCount_mul (ν : Measure α) [IsProbabilityMeasure ν]
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    ∫ x, (ptCount A n x : ℝ) * (ptCount B n x : ℝ) ∂sample ν =
      n * ν.real (A ∩ B) + n * (n - 1) * (ν.real A * ν.real B) := by
  have hpt : ∀ x : ℕ → α, (ptCount A n x : ℝ) * (ptCount B n x : ℝ) =
      (ptCount (A ∩ B) n x : ℝ) + (pairCount (A ×ˢ B) n x : ℝ) := by
    intro x
    exact_mod_cast ptCount_mul_ptCount A B n x
  simp_rw [hpt]
  rw [integral_add (integrable_sample_ptCount ν (hA.inter hB) n)
    (integrable_sample_pairCount ν (hA.prod hB) n),
    integral_ptCount ν (hA.inter hB), integral_pairCount ν (hA.prod hB), real_prod_prod_eq]

/-- **Covariance of the counts of two disjoint sets in a binomial process**:
`E[N_A N_B] - E N_A E N_B = - n ν(A) ν(B)`. -/
theorem cov_sample_ptCount_disjoint (ν : Measure α) [IsProbabilityMeasure ν]
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) (n : ℕ) :
    ∫ x, (ptCount A n x : ℝ) * (ptCount B n x : ℝ) ∂sample ν -
      (∫ x, (ptCount A n x : ℝ) ∂sample ν) * ∫ x, (ptCount B n x : ℝ) ∂sample ν =
      -(n * (ν.real A * ν.real B)) := by
  rw [integral_sample_ptCount_mul ν hA hB, integral_ptCount ν hA, integral_ptCount ν hB,
    hAB.inter_eq]
  simp only [measureReal_empty]
  ring

/-- **The binomial process has dependent counts**: for `n ≥ 1` and disjoint measurable `A`, `B` of
positive `ν`-measure, `E[N_A N_B] ≠ E N_A · E N_B`, so `N_A`, `N_B` are not independent. -/
theorem not_indepCount_sample (ν : Measure α) [IsProbabilityMeasure ν]
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) {n : ℕ}
    (hn : 1 ≤ n) (hA0 : 0 < ν.real A) (hB0 : 0 < ν.real B) :
    ∫ x, (ptCount A n x : ℝ) * (ptCount B n x : ℝ) ∂sample ν ≠
      (∫ x, (ptCount A n x : ℝ) ∂sample ν) * ∫ x, (ptCount B n x : ℝ) ∂sample ν := by
  intro h
  have h1 := cov_sample_ptCount_disjoint ν hA hB hAB n
  rw [h, sub_self] at h1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : 0 < (n : ℝ) * (ν.real A * ν.real B) := by positivity
  linarith

end Lightlike.Rows.G2_063
