import Mathlib
import Lightlike.Rows.G2_063.Poisson

/-!
# Second moments of the Poisson process: counts in disjoint sets are uncorrelated

For the Poisson process `poissonProcess lam ν` of `Lightlike/Rows/G2_063/Poisson.lean` the product of
two point counts splits into the count in the intersection (diagonal terms) and a pair count
(off-diagonal terms): `N_A N_B = N_{A ∩ B} + #{(i, j) : i ≠ j, x i ∈ A, x j ∈ B}`.
Taking means gives `E[N_A N_B] = lam ν(A ∩ B) + lam² ν(A) ν(B)`, hence
`Cov(N_A, N_B) = lam ν(A ∩ B)`: zero for disjoint `A`, `B`, and `Var N_A = lam ν(A)`
(the count variance equals the volume).

## Main results

* `ptCount_mul_ptCount`: the pointwise identity above.
* `integral_poissonProcess_ptCount_mul`: `E[N_A N_B] = lam ν(A ∩ B) + lam² ν(A) ν(B)`.
* `cov_poissonProcess_ptCount`: `E[N_A N_B] - E N_A E N_B = lam ν(A ∩ B)`.

## References

* G. Last, M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press (2017).
-/

open MeasureTheory ProbabilityTheory NNReal

namespace Lightlike.Rows.G2_063

variable {α : Type*} [MeasurableSpace α]

omit [MeasurableSpace α] in
/-- **Diagonal/off-diagonal split of a product of counts**:
`N_A N_B = N_{A ∩ B} + #{i ≠ j : x i ∈ A, x j ∈ B}`. -/
lemma ptCount_mul_ptCount (A B : Set α) (n : ℕ) (x : ℕ → α) :
    ptCount A n x * ptCount B n x = ptCount (A ∩ B) n x + pairCount (A ×ˢ B) n x := by
  classical
  set S : Finset (ℕ × ℕ) := (Finset.range n) ×ˢ (Finset.range n) with hS
  have h1 : ptCount A n x * ptCount B n x =
      (S.filter fun p => x p.1 ∈ A ∧ x p.2 ∈ B).card := by
    unfold ptCount
    rw [← Finset.card_product]
    congr 1
    ext p
    simp [hS, and_assoc, and_left_comm]
  have h2 := Finset.card_filter_add_card_filter_not (s := S.filter fun p => x p.1 ∈ A ∧ x p.2 ∈ B)
    (fun p : ℕ × ℕ => p.1 = p.2)
  have e1 : ptCount (A ∩ B) n x = ((S.filter fun p => x p.1 ∈ A ∧ x p.2 ∈ B).filter
      fun p => p.1 = p.2).card := by
    unfold ptCount
    have : ((S.filter fun p => x p.1 ∈ A ∧ x p.2 ∈ B).filter fun p => p.1 = p.2) =
        ((Finset.range n).filter fun i => x i ∈ A ∩ B).image fun i => (i, i) := by
      ext p
      obtain ⟨a, b⟩ := p
      simp only [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
        Set.mem_inter_iff, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨ha, hb⟩, hA, hB⟩, hab⟩
        subst hab
        exact ⟨a, ⟨ha, hA, hB⟩, rfl, rfl⟩
      · rintro ⟨i, ⟨hi, hA, hB⟩, rfl, rfl⟩
        exact ⟨⟨⟨hi, hi⟩, hA, hB⟩, rfl⟩
    rw [this, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
    convert rfl
  have e2 : pairCount (A ×ˢ B) n x = ((S.filter fun p => x p.1 ∈ A ∧ x p.2 ∈ B).filter
      fun p => ¬ p.1 = p.2).card := by
    unfold pairCount
    congr 1
    ext p
    simp only [hS, Finset.mem_filter, Set.mem_prod]
    tauto
  rw [h1, e1, e2]
  exact h2.symm

lemma integrable_poissonProcess_ptCount (lam : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν]
    {A : Set α} (hA : MeasurableSet A) :
    Integrable (fun p : ℕ × (ℕ → α) => (ptCount A p.1 p.2 : ℝ)) (poissonProcess lam ν) :=
  (integral_poissonProcess_of_bound lam ν (fun n x => (ptCount A n x : ℝ))
    (measurable_ptCount_real A hA) (fun n => (n : ℝ)) (integrable_poissonMeasure_id lam)
    (fun n x => by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast ptCount_le A n x)).1

lemma integrable_poissonProcess_pairCount (lam : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν]
    {R : Set (α × α)} (hR : MeasurableSet R) :
    Integrable (fun p : ℕ × (ℕ → α) => (pairCount R p.1 p.2 : ℝ)) (poissonProcess lam ν) := by
  have hC : Integrable (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) + n) (poissonMeasure lam) :=
    (integrable_poissonMeasure_pair lam).add (integrable_poissonMeasure_id lam)
  exact (integral_poissonProcess_of_bound lam ν (fun n x => (pairCount R n x : ℝ))
    (measurable_pairCount_real R hR) (fun n => (n : ℝ) * ((n : ℝ) - 1) + n) hC
    (fun n x => by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      have := pairCount_le R n x
      have h2 : (pairCount R n x : ℝ) ≤ (n : ℝ) * n := by exact_mod_cast this
      nlinarith)).1

lemma real_prod_prod_eq (ν : Measure α) [IsProbabilityMeasure ν] (A B : Set α) :
    (ν.prod ν).real (A ×ˢ B) = ν.real A * ν.real B := by
  simp [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]

/-- **Second moment of two counts of the Poisson process**:
`E[N_A N_B] = lam ν(A ∩ B) + lam² ν(A) ν(B)`. -/
theorem integral_poissonProcess_ptCount_mul (lam : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν]
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫ p, (ptCount A p.1 p.2 : ℝ) * (ptCount B p.1 p.2 : ℝ) ∂poissonProcess lam ν =
      lam * ν.real (A ∩ B) + (lam : ℝ) ^ 2 * (ν.real A * ν.real B) := by
  have hpt : ∀ p : ℕ × (ℕ → α), (ptCount A p.1 p.2 : ℝ) * (ptCount B p.1 p.2 : ℝ) =
      (ptCount (A ∩ B) p.1 p.2 : ℝ) + (pairCount (A ×ˢ B) p.1 p.2 : ℝ) := by
    intro p
    exact_mod_cast ptCount_mul_ptCount A B p.1 p.2
  simp_rw [hpt]
  rw [integral_add (integrable_poissonProcess_ptCount lam ν (hA.inter hB))
    (integrable_poissonProcess_pairCount lam ν (hA.prod hB)),
    integral_poissonProcess_ptCount lam ν (hA.inter hB),
    integral_poissonProcess_pairCount lam ν (hA.prod hB), real_prod_prod_eq]

/-- **Covariance of two counts of the Poisson process**:
`E[N_A N_B] - E N_A · E N_B = lam ν(A ∩ B)`. In particular the counts of disjoint sets are
uncorrelated, and `Var N_A = lam ν(A)`. -/
theorem cov_poissonProcess_ptCount (lam : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν]
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫ p, (ptCount A p.1 p.2 : ℝ) * (ptCount B p.1 p.2 : ℝ) ∂poissonProcess lam ν -
      (∫ p, (ptCount A p.1 p.2 : ℝ) ∂poissonProcess lam ν) *
        ∫ p, (ptCount B p.1 p.2 : ℝ) ∂poissonProcess lam ν = lam * ν.real (A ∩ B) := by
  rw [integral_poissonProcess_ptCount_mul lam ν hA hB, integral_poissonProcess_ptCount lam ν hA,
    integral_poissonProcess_ptCount lam ν hB]
  ring

end Lightlike.Rows.G2_063
