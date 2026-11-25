import Mathlib
import Lightlike.CausalSets.PoissonProcessCounts.Independence

/-!
# The Poisson process: law of a count, and conditioning on the number of points

* `map_poissonProcess_ptCount`: the count `N_A` of the Poisson process has the Poisson law of
  parameter `lam ν(A)`.
* `variance_poissonProcess_ptCount`: `Var N_A = lam ν(A)`.
* `cond_poissonProcess_count`: conditionally on `N = n` total points, the sample is the i.i.d.
  sample of law `ν` (its first `n` points are the `n` points of the process).

## References

* G. Last, M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press (2017).
-/

open MeasureTheory ProbabilityTheory NNReal Complex

namespace Lightlike.Rows.G2_063

variable {α : Type*} [MeasurableSpace α]

/-- **The count of a Poisson process is Poisson**: `N_A ∼ Po(lam ν(A))`. -/
theorem map_poissonProcess_ptCount (lam : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν]
    {A : Set α} (hA : MeasurableSet A) :
    (poissonProcess lam ν).map (fun p : ℕ × (ℕ → α) => (ptCount A p.1 p.2 : ℝ)) =
      (poissonMeasure (lam * (ν A).toNNReal)).map (Nat.cast : ℕ → ℝ) := by
  have : IsProbabilityMeasure ((poissonProcess lam ν).map
      (fun p : ℕ × (ℕ → α) => (ptCount A p.1 p.2 : ℝ))) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_poissonProcess_ptCount hA).aemeasurable).2 inferInstance
  apply Measure.ext_of_charFun
  ext t
  have e : ((lam * (ν A).toNNReal : ℝ≥0) : ℝ) = lam * ν.real A := by
    simp only [Measure.real, NNReal.coe_mul]
    rfl
  rw [charFun_map_poissonProcess_ptCount lam ν hA, charFun_map_cast_poissonMeasure, e]
  congr 1
  push_cast
  ring

/-- **Variance of a Poisson count equals its mean**, the volume: `Var N_A = lam ν(A)`. -/
theorem variance_poissonProcess_ptCount (lam : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν]
    {A : Set α} (hA : MeasurableSet A) :
    variance (fun p : ℕ × (ℕ → α) => (ptCount A p.1 p.2 : ℝ)) (poissonProcess lam ν) =
      lam * ν.real A := by
  have hsq : ∀ p : ℕ × (ℕ → α), (ptCount A p.1 p.2 : ℝ) ^ 2 =
      (ptCount (A ∩ A) p.1 p.2 : ℝ) + (pairCount (A ×ˢ A) p.1 p.2 : ℝ) := by
    intro p
    rw [sq]
    exact_mod_cast ptCount_mul_ptCount A A p.1 p.2
  have hmem : MemLp (fun p : ℕ × (ℕ → α) => (ptCount A p.1 p.2 : ℝ)) 2 (poissonProcess lam ν) := by
    refine (memLp_two_iff_integrable_sq
      (measurable_poissonProcess_ptCount hA).aestronglyMeasurable).2 ?_
    simp_rw [hsq]
    exact (integrable_poissonProcess_ptCount lam ν (hA.inter hA)).add
      (integrable_poissonProcess_pairCount lam ν (hA.prod hA))
  rw [variance_eq_sub hmem]
  have h := integral_poissonProcess_ptCount_mul lam ν hA hA
  have h1 := integral_poissonProcess_ptCount lam ν hA
  simp only [Pi.pow_apply, sq] at *
  rw [h, h1, Set.inter_self]
  ring

/-- **Conditioning on the count**: given that the Poisson process has exactly `n` points (positive
rate), the law of the underlying i.i.d. sample is `sample ν`, whatever `n`. -/
theorem cond_poissonProcess_count {lam : ℝ≥0} (hlam : 0 < lam) (ν : Measure α)
    [IsProbabilityMeasure ν] (n : ℕ) (S : Set (ℕ → α)) :
    (poissonProcess lam ν)[(Set.univ : Set ℕ) ×ˢ S | ({n} : Set ℕ) ×ˢ (Set.univ : Set (ℕ → α))] =
      sample ν S := by
  have hs : MeasurableSet (({n} : Set ℕ) ×ˢ (Set.univ : Set (ℕ → α))) :=
    (measurableSet_singleton n).prod MeasurableSet.univ
  have hi : (({n} : Set ℕ) ×ˢ (Set.univ : Set (ℕ → α))) ∩ ((Set.univ : Set ℕ) ×ˢ S) =
      ({n} : Set ℕ) ×ˢ S := by
    ext p; simp
  have h0 : poissonMeasure lam {n} ≠ 0 := by
    rw [poissonMeasure_singleton]
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have ht : poissonMeasure lam {n} ≠ ⊤ := measure_ne_top _ _
  rw [cond_apply hs, hi, poissonProcess, Measure.prod_prod, Measure.prod_prod, measure_univ,
    mul_one, ← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]

end Lightlike.Rows.G2_063
