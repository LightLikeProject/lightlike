import Mathlib

/-!
# Counting points of an independent sample: the fixed-size moments

Let `ν` be a probability measure on a measurable space `α` and `x : ℕ → α` an independent sample
with law `ν` in each coordinate (`Measure.infinitePi`). The first `n` coordinates are the points of a
*binomial process*. This file computes the first two moments of two counts, for fixed `n`:

* `ptCount A n x`, the number of `i < n` with `x i ∈ A`;
* `pairCount R n x`, the number of ordered pairs `i ≠ j`, `i, j < n`, with `(x i, x j) ∈ R`.

Their means are `n ν(A)` and `n (n - 1) (ν ⊗ ν)(R)`. They are the input of the Poisson point
process of `Lightlike/CausalSets/PoissonProcessCounts/Poisson.lean` (mix over a Poisson number `n`) and of the binomial
process comparison. Both are for a sample of `n` points in a region, the relation count of
`Lightlike/CausalSets/Expected.lean` in the form with an infinite sample.

## References

* G. Last, M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press (2017).
-/

open MeasureTheory ProbabilityTheory

namespace Lightlike.CausalSets.PoissonProcessCounts

variable {α : Type*} [MeasurableSpace α]

open Classical in
/-- The **number of points in `A`** among the first `n` points `x 0, …, x (n - 1)` of a sample. -/
noncomputable def ptCount (A : Set α) (n : ℕ) (x : ℕ → α) : ℕ :=
  ((Finset.range n).filter fun i => x i ∈ A).card

open Classical in
/-- The **number of ordered pairs of different points** `(x i, x j)`, `i ≠ j < n`, that lie in the
relation `R`. -/
noncomputable def pairCount (R : Set (α × α)) (n : ℕ) (x : ℕ → α) : ℕ :=
  (((Finset.range n) ×ˢ (Finset.range n)).filter fun p => p.1 ≠ p.2 ∧ (x p.1, x p.2) ∈ R).card

/-- The sample measure: independent coordinates with law `ν`. -/
noncomputable abbrev sample (ν : Measure α) [IsProbabilityMeasure ν] : Measure (ℕ → α) :=
  Measure.infinitePi (fun _ : ℕ => ν)

lemma measurable_ptCount_real (A : Set α) (hA : MeasurableSet A) (n : ℕ) :
    Measurable fun x : ℕ → α => (ptCount A n x : ℝ) := by
  classical
  have : (fun x : ℕ → α => (ptCount A n x : ℝ)) =
      fun x => ∑ i ∈ Finset.range n, Set.indicator A (1 : α → ℝ) (x i) := by
    funext x
    simp only [ptCount, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : x i ∈ A <;> simp [h, Set.indicator]
  rw [this]
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_one.indicator hA).comp (measurable_pi_apply i)

lemma measurable_pairCount_real (R : Set (α × α)) (hR : MeasurableSet R) (n : ℕ) :
    Measurable fun x : ℕ → α => (pairCount R n x : ℝ) := by
  classical
  have : (fun x : ℕ → α => (pairCount R n x : ℝ)) =
      fun x => ∑ p ∈ ((Finset.range n) ×ˢ (Finset.range n)).filter (fun p => p.1 ≠ p.2),
        Set.indicator R (1 : α × α → ℝ) (x p.1, x p.2) := by
    funext x
    simp only [pairCount, Finset.card_filter, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h1 : p.1 ≠ p.2 <;> by_cases h2 : (x p.1, x p.2) ∈ R <;> simp [h1, h2, Set.indicator]
  rw [this]
  exact Finset.measurable_sum _ fun p _ =>
    (measurable_one.indicator hR).comp
      ((measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2))

/-- **Mean of a point count in a sample**: `n` independent points of law `ν` have `n ν(A)` points in
`A` in expectation. -/
theorem integral_ptCount (ν : Measure α) [IsProbabilityMeasure ν] {A : Set α} (hA : MeasurableSet A)
    (n : ℕ) : ∫ x, (ptCount A n x : ℝ) ∂sample ν = n * ν.real A := by
  classical
  have hc : ∀ x : ℕ → α, (ptCount A n x : ℝ) =
      ∑ i ∈ Finset.range n, Set.indicator A (1 : α → ℝ) (x i) := by
    intro x
    simp only [ptCount, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : x i ∈ A <;> simp [h, Set.indicator]
  simp_rw [hc]
  rw [integral_finsetSum]
  · have : ∀ i ∈ Finset.range n,
        ∫ x, Set.indicator A (1 : α → ℝ) (x i) ∂sample ν = ν.real A := by
      intro i _
      have hm : Measurable fun x : ℕ → α => x i := measurable_pi_apply i
      have h1 : ∫ x, Set.indicator A (1 : α → ℝ) (x i) ∂sample ν =
          ∫ a, Set.indicator A (1 : α → ℝ) a ∂ν := by
        have e : (sample ν).map (fun x : ℕ → α => x i) = ν :=
          Measure.infinitePi_map_eval (fun _ : ℕ => ν) i
        have h2 := integral_map (f := Set.indicator A (1 : α → ℝ)) hm.aemeasurable
          (measurable_one.indicator hA).aestronglyMeasurable (μ := sample ν)
        rw [e] at h2
        exact h2.symm
      rw [h1, integral_indicator_one hA]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · intro i _
    exact (integrable_const (1 : ℝ)).indicator ((measurable_pi_apply i) hA)

/-- **Mean of a pair count in a sample**: `n` independent points of law `ν` have
`n (n - 1) (ν ⊗ ν)(R)` ordered pairs of different points in the relation `R` in expectation. -/
theorem integral_pairCount (ν : Measure α) [IsProbabilityMeasure ν] {R : Set (α × α)}
    (hR : MeasurableSet R) (n : ℕ) :
    ∫ x, (pairCount R n x : ℝ) ∂sample ν = n * (n - 1) * (ν.prod ν).real R := by
  classical
  have hc : ∀ x : ℕ → α, (pairCount R n x : ℝ) =
      ∑ p ∈ ((Finset.range n) ×ˢ (Finset.range n)).filter (fun p => p.1 ≠ p.2),
        Set.indicator R (1 : α × α → ℝ) (x p.1, x p.2) := by
    intro x
    simp only [pairCount, Finset.card_filter, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h1 : p.1 ≠ p.2 <;> by_cases h2 : (x p.1, x p.2) ∈ R <;> simp [h1, h2, Set.indicator]
  simp_rw [hc]
  rw [integral_finsetSum]
  · have : ∀ p ∈ ((Finset.range n) ×ˢ (Finset.range n)).filter (fun p => p.1 ≠ p.2),
        ∫ x, Set.indicator R (1 : α × α → ℝ) (x p.1, x p.2) ∂sample ν = (ν.prod ν).real R := by
      intro p hp
      have hne : p.1 ≠ p.2 := (Finset.mem_filter.1 hp).2
      have hm : Measurable fun x : ℕ → α => (x p.1, x p.2) :=
        (measurable_pi_apply _).prodMk (measurable_pi_apply _)
      have h1 : ∫ x, Set.indicator R (1 : α × α → ℝ) (x p.1, x p.2) ∂sample ν =
          ∫ a, Set.indicator R (1 : α × α → ℝ) a ∂(ν.prod ν) := by
        have e : (sample ν).map (fun x : ℕ → α => (x p.1, x p.2)) = ν.prod ν :=
          Measure.infinitePi_map_eval_prod (P := fun _ : ℕ => ν) hne
        have h2 := integral_map (f := Set.indicator R (1 : α × α → ℝ)) hm.aemeasurable
          (measurable_one.indicator hR).aestronglyMeasurable (μ := sample ν)
        rw [e] at h2
        exact h2.symm
      rw [h1, integral_indicator_one hR]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
    have hcard : (((Finset.range n) ×ˢ (Finset.range n)).filter (fun p => p.1 ≠ p.2)).card =
        n * n - n := by
      have : ((Finset.range n) ×ˢ (Finset.range n)).filter (fun p => p.1 ≠ p.2) =
          (Finset.range n).offDiag := by
        ext p; simp [Finset.mem_offDiag, and_assoc]
      rw [this, Finset.offDiag_card]; simp
    rw [hcard, Nat.cast_sub (Nat.le_mul_self n)]
    push_cast; ring
  · intro p hp
    have hm : Measurable fun x : ℕ → α => (x p.1, x p.2) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact (integrable_const (1 : ℝ)).indicator (hm hR)

end Lightlike.CausalSets.PoissonProcessCounts

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_063.integral_pairCount := _root_.Lightlike.CausalSets.PoissonProcessCounts.integral_pairCount
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_063.integral_ptCount := _root_.Lightlike.CausalSets.PoissonProcessCounts.integral_ptCount
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_063.measurable_pairCount_real := _root_.Lightlike.CausalSets.PoissonProcessCounts.measurable_pairCount_real
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_063.measurable_ptCount_real := _root_.Lightlike.CausalSets.PoissonProcessCounts.measurable_ptCount_real
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_063.pairCount := _root_.Lightlike.CausalSets.PoissonProcessCounts.pairCount
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_063.ptCount := _root_.Lightlike.CausalSets.PoissonProcessCounts.ptCount
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_063.sample := _root_.Lightlike.CausalSets.PoissonProcessCounts.sample
