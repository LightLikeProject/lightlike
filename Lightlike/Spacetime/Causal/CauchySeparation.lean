import Lightlike.Spacetime.Causal.Ladder
import Lightlike.Spacetime.Causal.BasicRelations

/-!
# Separation by an achronal set

Let `S` be achronal. The chronological future `I⁺(S) = ⋃ x ∈ S, I⁺(x)` and the chronological past
`I⁻(S)` of `S` are disjoint (`chronFutureSet_disjoint_chronPastSet`): a point in both would give two points
of `S` joined by a timelike curve. If both are open (the openness of `I⁺` and of `I⁻`), a preconnected set
`C` that misses `S` and lies in `I⁺(S) ∪ I⁻(S)` is contained in one of them
(`subset_chronFutureSet_of_preconnected`). This is the first step of the proof that a curve through a
point of `I⁺(S)` that misses `S` stays in `I⁺(S)`.

Supporting lemma for the causal structure; no catalogue entry.
-/

open Set Bundle Manifold
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- The chronological past of a set. -/
def chronPastSet (S : Set M) : Set M := ⋃ x ∈ S, chronPast T x

/-- **The chronological future and past of an achronal set are disjoint.** -/
theorem chronFutureSet_disjoint_chronPastSet {S : Set M} (hA : IsAchronal T S) :
    Disjoint (chronFutureSet T S) (chronPastSet T S) := by
  rw [Set.disjoint_left]
  intro p hpF hpP
  obtain ⟨x, hx, hpx⟩ := Set.mem_iUnion₂.1 hpF
  obtain ⟨y, hy, hpy⟩ := Set.mem_iUnion₂.1 hpP
  -- `x ≪ p ≪ y`
  exact hA x hx y hy (chron_trans T hpx hpy)

/-- **A preconnected set that misses an achronal set `S`, lies in `I⁺(S) ∪ I⁻(S)` and meets `I⁺(S)`
is contained in `I⁺(S)`**, when `I⁺(S)` and `I⁻(S)` are open. -/
theorem subset_chronFutureSet_of_preconnected {S C : Set M} (hA : IsAchronal T S)
    (hFo : IsOpen (chronFutureSet T S)) (hPo : IsOpen (chronPastSet T S))
    (hcov : ∀ p ∈ C, p ∈ chronFutureSet T S ∨ p ∈ chronPastSet T S) (hC : IsPreconnected C)
    {p : M} (hp : p ∈ C) (hpF : p ∈ chronFutureSet T S) : C ⊆ chronFutureSet T S := by
  have hsub : C ⊆ chronFutureSet T S ∪ chronPastSet T S := fun q hq => hcov q hq
  rcases hC.subset_or_subset hFo hPo (chronFutureSet_disjoint_chronPastSet T hA) hsub with h | h
  · exact h
  · exact absurd (h hp) (Set.disjoint_left.1 (chronFutureSet_disjoint_chronPastSet T hA) hpF)

end Lightlike.Causal
