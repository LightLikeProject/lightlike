import Lightlike.OperatorAlgebras.MongeKantorovich

/-!
# Tests for Monge-Kantorovich duality

For a separable cost `h(x, y) = a(x) + b(y)` every coupling has the same cost `∫ a dμ + ∫ b dν`, so the duality must
give `sup {∫ f dμ + ∫ g dν | f ⊕ g ≤ a ⊕ b} = ∫ a dμ + ∫ b dν`, with `(f, g) = (a, b)` attaining it.

* `sepCost`, `integral_sepCost`, `sSup_dualValues_sepCost`.
-/

open MeasureTheory

namespace Lightlike.OperatorAlgebras.Transport

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The separable cost `(x, y) ↦ a(x) + b(y)`. -/
def sepCost (a b : C(X, ℝ)) : C(X × X, ℝ) :=
  ⟨fun p => a p.1 + b p.2, (a.continuous.comp continuous_fst).add (b.continuous.comp continuous_snd)⟩

/-- Every coupling has cost `∫ a dμ + ∫ b dν` for the separable cost. -/
lemma integral_sepCost {π : Measure (X × X)} (hπ : π ∈ couplings μ ν) (a b : C(X, ℝ)) :
    ∫ p, sepCost a b p ∂π = ∫ x, a x ∂μ + ∫ x, b x ∂ν := by
  have := hπ.1
  rw [integral_comp_fst hπ.2.1 a a.continuous, integral_comp_snd hπ.2.2 b b.continuous,
    ← integral_add (integrable_of_continuous (f := fun p : X × X => a p.1) (a.continuous.comp continuous_fst))
      (integrable_of_continuous (f := fun p : X × X => b p.2) (b.continuous.comp continuous_snd))]
  rfl

/-- **The dual value of a separable cost** is `∫ a dμ + ∫ b dν`. -/
theorem sSup_dualValues_sepCost (a b : C(X, ℝ)) :
    sSup (dualValues μ ν (sepCost a b)) = ∫ x, a x ∂μ + ∫ x, b x ∂ν := by
  obtain ⟨σ, hσ, -, he⟩ := integral_optimal_eq_sSup (μ := μ) (ν := ν) (sepCost a b)
  rw [← he, integral_sepCost hσ]

end Lightlike.OperatorAlgebras.Transport
