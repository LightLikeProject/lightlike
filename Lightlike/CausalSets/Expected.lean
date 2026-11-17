import Mathlib

/-!
# The expected number of relations of independent points

For `n` independent points drawn from a probability measure `μ` and a measurable relation `R`, the
expected number of ordered pairs `(i, j)`, `i ≠ j`, with `(xᵢ, xⱼ) ∈ R` is `n (n - 1) p`, where
`p = (μ ⊗ μ)(R)` is the probability that two independent points are related
(`expected_relCount`). This is the measure-theoretic step of the Myrheim–Meyer relation count of a
sprinkling into a region of Minkowski space (`Lightlike/CausalSets/Sprinkling.lean`), a bridge
between Lorentzian geometry and causal sets; it uses `n` uniform points and no Poisson process.

## References

* J. Myrheim, *Statistical geometry*, CERN preprint TH-2538 (1978).
* D. A. Meyer, *The dimension of causal sets*, PhD thesis, MIT (1988).
* S. Surya, *The causal set approach to the problem of quantum gravity*, Living Reviews in
  Relativity 22 (2019), section 2.
-/

open MeasureTheory ProbabilityTheory

namespace Lightlike.CausalSets

variable {α : Type*} [MeasurableSpace α] {n : ℕ}

/-- **The law of two different coordinates** of `n` independent points drawn from `μ` is the
product measure `μ ⊗ μ`. -/
lemma pair_marginal (μ : Measure α) [IsProbabilityMeasure μ] {i j : Fin n} (hij : i ≠ j) :
    (Measure.pi (fun _ : Fin n => μ)).map (fun ω => (ω i, ω j)) = μ.prod μ := by
  have hind := iIndepFun_pi (μ := fun _ : Fin n => μ) (X := fun _ => id) (fun _ => aemeasurable_id)
  have h2 := (hind.indepFun hij)
  have := (indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable).1 h2
  rw [this]
  rw [(measurePreserving_eval _ i).map_eq, (measurePreserving_eval _ j).map_eq]

open Classical in
/-- The **number of related pairs** of a sample `ω` of `n` points for the relation `R`: the number
of ordered pairs `(i, j)` of different indices with `(ω i, ω j) ∈ R`. For the strict order of a
partial order this counts every related pair once. -/
noncomputable def relCount (R : Set (α × α)) (ω : Fin n → α) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ (ω p.1, ω p.2) ∈ R).card

/-- **Expected number of relations** of `n` independent points: for a probability measure `μ` and a
measurable relation `R`, `n` independent points drawn from `μ` have `n (n - 1) p` related pairs in
expectation, where `p = (μ ⊗ μ)(R)` is the probability that two independent points are related.
This is linearity of the expectation over the `n (n - 1)` ordered pairs, and needs no Poisson
process. -/
theorem expected_relCount (μ : Measure α) [IsProbabilityMeasure μ] {R : Set (α × α)}
    (hR : MeasurableSet R) :
    ∫ ω, (relCount R ω : ℝ) ∂Measure.pi (fun _ : Fin n => μ) =
      (n : ℝ) * (n - 1) * (μ.prod μ R).toReal := by
  classical
  have hcount : ∀ ω : Fin n → α, (relCount R ω : ℝ) =
      ∑ p ∈ (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2),
        (Set.indicator ((fun ω : Fin n → α => (ω p.1, ω p.2)) ⁻¹' R) (1 : (Fin n → α) → ℝ) ω) := by
    intro ω
    unfold relCount
    simp only [Finset.card_filter, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h1 : p.1 ≠ p.2 <;> by_cases h2 : (ω p.1, ω p.2) ∈ R <;>
      simp [h1, h2, Set.indicator]
  simp_rw [hcount]
  rw [integral_finsetSum]
  · have : ∀ p ∈ (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2),
        ∫ ω, Set.indicator ((fun ω : Fin n → α => (ω p.1, ω p.2)) ⁻¹' R) (1 : (Fin n → α) → ℝ) ω
          ∂Measure.pi (fun _ : Fin n => μ) = (μ.prod μ R).toReal := by
      intro p hp
      have hne : p.1 ≠ p.2 := (Finset.mem_filter.1 hp).2
      have hm : Measurable (fun ω : Fin n → α => (ω p.1, ω p.2)) :=
        (measurable_pi_apply _).prodMk (measurable_pi_apply _)
      rw [integral_indicator_one (hm hR), Measure.real, ← Measure.map_apply hm hR, pair_marginal μ hne]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2).card = n * n - n := by
      have : (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2) = Finset.univ.offDiag := by
        ext p; simp [Finset.mem_offDiag]
      rw [this, Finset.offDiag_card]; simp
    rw [hcard, Nat.cast_sub (Nat.le_mul_self n)]
    push_cast; ring
  · intro p hp
    have hm : Measurable (fun ω : Fin n → α => (ω p.1, ω p.2)) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact (integrable_const (1 : ℝ)).indicator (hm hR)

end Lightlike.CausalSets
