import Mathlib
import Lightlike.CausalSets.PoissonProcessCounts.FixedCount
import Lightlike.CausalSets.PoissonProcessCounts.PoissonMoments

/-!
# The Poisson point process as a mixed binomial process

For a probability measure `ν` on `α` and a rate `lam : ℝ≥0`, the **Poisson point process of
intensity `lam ν`** is realised on `ℕ × (ℕ → α)`: draw the number of points `n` from `Po(lam)`
(Mathlib's `poissonMeasure`, which lives on `ℕ` only), and independently an i.i.d. sequence
`x` of law `ν`; the points are `x 0, …, x (n - 1)`. Conditionally on `n` the points are `n`
i.i.d. points of law `ν`, as in Last–Penrose, *Lectures on the Poisson Process*.

This file gives the process and, by Fubini over the mixing law, the means of the point count
`ptCount A` and the pair count `pairCount R`.

## Main results

* `poissonProcess lam ν`: the law of the process.
* `integral_poissonProcess_ptCount`: `E N_A = lam ν(A)`.
* `integral_poissonProcess_pairCount`: `E[# ordered pairs of distinct points in R] = lam² (ν ⊗ ν)(R)`.

## References

* G. Last, M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press (2017).
-/

open MeasureTheory ProbabilityTheory NNReal

namespace Lightlike.CausalSets.PoissonProcessCounts

variable {α : Type*} [MeasurableSpace α]

/-- The **Poisson point process** of rate `lam` and base law `ν`: a Poisson number `n` of points
(`poissonMeasure lam`), independent of an i.i.d. sequence of law `ν`, whose first `n` terms are
the points. -/
noncomputable abbrev poissonProcess (lam : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν] :
    Measure (ℕ × (ℕ → α)) :=
  (poissonMeasure lam).prod (sample ν)

/-- **Fubini over the Poisson mixing law**: a family `g n` of measurable functions of the sample,
dominated by a Poisson-integrable function of `n`, is integrable on the process space and its
integral is the Poisson average of the sample integrals. -/
lemma integral_poissonProcess_of_bound (lam : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν]
    (g : ℕ → (ℕ → α) → ℝ) (hg : ∀ n, Measurable (g n)) (C : ℕ → ℝ)
    (hC : Integrable C (poissonMeasure lam)) (hb : ∀ n x, |g n x| ≤ C n) :
    Integrable (fun p : ℕ × (ℕ → α) => g p.1 p.2) (poissonProcess lam ν) ∧
    ∫ p, g p.1 p.2 ∂poissonProcess lam ν = ∫ n, ∫ x, g n x ∂sample ν ∂poissonMeasure lam := by
  have hm : Measurable fun p : ℕ × (ℕ → α) => g p.1 p.2 :=
    measurable_from_prod_countable_right (f := fun p : ℕ × (ℕ → α) => g p.1 p.2) fun n => hg n
  have hint : Integrable (fun p : ℕ × (ℕ → α) => g p.1 p.2) (poissonProcess lam ν) := by
    refine Integrable.mono' (hC.comp_fst (sample ν)) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    simpa using hb p.1 p.2
  exact ⟨hint, integral_prod _ hint⟩

omit [MeasurableSpace α] in
lemma ptCount_le (A : Set α) (n : ℕ) (x : ℕ → α) : ptCount A n x ≤ n := by
  classical
  unfold ptCount
  calc _ ≤ (Finset.range n).card := Finset.card_filter_le _ _
    _ = n := Finset.card_range n

omit [MeasurableSpace α] in
lemma pairCount_le (R : Set (α × α)) (n : ℕ) (x : ℕ → α) : pairCount R n x ≤ n * n := by
  classical
  unfold pairCount
  calc _ ≤ ((Finset.range n) ×ˢ (Finset.range n)).card := Finset.card_filter_le _ _
    _ = n * n := by simp

/-- **Mean count of the Poisson process**: `E N_A = lam ν(A)`. -/
theorem integral_poissonProcess_ptCount (lam : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν]
    {A : Set α} (hA : MeasurableSet A) :
    ∫ p, (ptCount A p.1 p.2 : ℝ) ∂poissonProcess lam ν = lam * ν.real A := by
  have h := integral_poissonProcess_of_bound lam ν (fun n x => (ptCount A n x : ℝ))
    (measurable_ptCount_real A hA) (fun n => (n : ℝ)) (integrable_poissonMeasure_id lam)
    (fun n x => by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast ptCount_le A n x)
  rw [h.2]
  simp_rw [integral_ptCount ν hA]
  rw [integral_mul_const, integral_poissonMeasure_id]

/-- **Mean pair count of the Poisson process**:
`E[# ordered pairs of distinct points in R] = lam² (ν ⊗ ν)(R)`. -/
theorem integral_poissonProcess_pairCount (lam : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν]
    {R : Set (α × α)} (hR : MeasurableSet R) :
    ∫ p, (pairCount R p.1 p.2 : ℝ) ∂poissonProcess lam ν = (lam : ℝ) ^ 2 * (ν.prod ν).real R := by
  have hC : Integrable (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) + n) (poissonMeasure lam) :=
    (integrable_poissonMeasure_pair lam).add (integrable_poissonMeasure_id lam)
  have h := integral_poissonProcess_of_bound lam ν (fun n x => (pairCount R n x : ℝ))
    (measurable_pairCount_real R hR) (fun n => (n : ℝ) * ((n : ℝ) - 1) + n) hC
    (fun n x => by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      have := pairCount_le R n x
      have h2 : (pairCount R n x : ℝ) ≤ (n : ℝ) * n := by exact_mod_cast this
      nlinarith)
  rw [h.2]
  simp_rw [integral_pairCount ν hR]
  rw [integral_mul_const, integral_poissonMeasure_descFactorial]

end Lightlike.CausalSets.PoissonProcessCounts

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_063.integral_poissonProcess_of_bound := _root_.Lightlike.CausalSets.PoissonProcessCounts.integral_poissonProcess_of_bound
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_063.integral_poissonProcess_pairCount := _root_.Lightlike.CausalSets.PoissonProcessCounts.integral_poissonProcess_pairCount
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_063.integral_poissonProcess_ptCount := _root_.Lightlike.CausalSets.PoissonProcessCounts.integral_poissonProcess_ptCount
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_063.pairCount_le := _root_.Lightlike.CausalSets.PoissonProcessCounts.pairCount_le
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_063.poissonProcess := _root_.Lightlike.CausalSets.PoissonProcessCounts.poissonProcess
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_063.ptCount_le := _root_.Lightlike.CausalSets.PoissonProcessCounts.ptCount_le
