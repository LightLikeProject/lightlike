import Mathlib
import Lightlike.CausalSets.PoissonProcessCounts.Poisson
import Lightlike.CausalSets.Rectangle
import Lightlike.CausalSets.Myrheim4D

/-!
# Poisson sprinkling into Minkowski regions: the expected relation count

A Poisson sprinkling of density `ρ` into a region `A ⊂ ℝ^{d+1}` of volume `V` is the Poisson point
process `poissonProcess lam (regionMeasure A)` with `lam = ρ V`: a Poisson number of independent
uniform points of `A`. The number of relations `x ≺ y` (`coneLT`) among the points is the
`pairCount` of the relation set. Its mean is `lam² p` where `p = regionRelProb A` is the probability
that two uniform points of `A` are related.

## Main results

* `expected_relations_poisson_region`: `E[#relations] = lam² · regionRelProb A`.
* `expected_relations_poisson_diamond_two`: `lam² / 4` in `1 + 1` dimensions.
* `expected_relations_poisson_diamond_four`: `lam² / 20` in `3 + 1` dimensions.
* `expected_relations_poisson_rect`: `7 lam² / 48` for the `1 × 2` rectangle in `1 + 1` dimensions
  (not the diamond's `1/4`).

## References

* G. Last, M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press (2017).
-/

open MeasureTheory NNReal Lightlike.CausalSets

namespace Lightlike.Rows.G2_063

/-- **Expected relation count of a Poisson sprinkling into a region.** -/
theorem expected_relations_poisson_region {d : ℕ} (lam : ℝ≥0) (A : Set (Fin (d + 1) → ℝ))
    [IsProbabilityMeasure (regionMeasure A)] :
    ∫ p, (pairCount {q : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) | coneLT q.1 q.2} p.1 p.2 : ℝ)
        ∂poissonProcess lam (regionMeasure A) = (lam : ℝ) ^ 2 * regionRelProb A := by
  rw [integral_poissonProcess_pairCount lam (regionMeasure A) (coneLT_measurableSet d)]
  rfl

/-- **Poisson sprinkling into the `1 + 1`-dimensional causal diamond**: the expected number of
relations is `lam² / 4`. -/
theorem expected_relations_poisson_diamond_two (lam : ℝ≥0) :
    ∫ p, (pairCount {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | coneLT q.1 q.2} p.1 p.2 : ℝ)
        ∂poissonProcess lam (diamondMeasure 1) = (lam : ℝ) ^ 2 / 4 := by
  have : IsProbabilityMeasure (regionMeasure (diamond 1)) := diamondMeasure_isProbability 1
  have h := expected_relations_poisson_region (d := 1) lam (diamond 1)
  have h2 : regionRelProb (diamond 1) = 1 / 4 := relProb_one
  exact h.trans (by rw [h2]; ring)

/-- **Poisson sprinkling into the `3 + 1`-dimensional causal diamond**: the expected number of
relations is `lam² / 20`. -/
theorem expected_relations_poisson_diamond_four (lam : ℝ≥0) :
    ∫ p, (pairCount {q : (Fin 4 → ℝ) × (Fin 4 → ℝ) | coneLT q.1 q.2} p.1 p.2 : ℝ)
        ∂poissonProcess lam (diamondMeasure 3) = (lam : ℝ) ^ 2 / 20 := by
  have : IsProbabilityMeasure (regionMeasure (diamond 3)) := diamondMeasure_isProbability 3
  have h := expected_relations_poisson_region (d := 3) lam (diamond 3)
  have h2 : regionRelProb (diamond 3) = 1 / 20 := relProb_three_eq
  exact h.trans (by rw [h2]; ring)

instance isProbabilityMeasure_regionMeasure_rect : IsProbabilityMeasure (regionMeasure rectSet) :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite (by simp [volume_rectSet])
    (by simp [volume_rectSet])

/-- **Poisson sprinkling into a `1 × 2` rectangle** (`1 + 1` dimensions): the expected number of
relations is `7 lam² / 48`, not the `lam² / 4` of the diamond. -/
theorem expected_relations_poisson_rect (lam : ℝ≥0) :
    ∫ p, (pairCount {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | coneLT q.1 q.2} p.1 p.2 : ℝ)
        ∂poissonProcess lam (regionMeasure rectSet) = 7 * (lam : ℝ) ^ 2 / 48 := by
  have h := expected_relations_poisson_region (d := 1) lam rectSet
  exact h.trans (by rw [regionRelProb_rect]; ring)

end Lightlike.Rows.G2_063
