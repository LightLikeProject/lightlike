import Lightlike.PL.UnionLemma

/-!
# Checks of the union lemma for two compact sets meeting in one point

Non-vacuity of `joinedIn_union_compl`: two copies of the compact set `{(0, 1)}`, which meet in
`{(0, 1)}`, and two points joined by a path on the first axis that avoids it. Wrong-model checks:
the hypothesis `K₁ ∩ K₂ = {R}` is false for two disjoint sets.
-/

open Set

namespace Lightlike.PL

/-- Non-vacuity: the hypotheses of `joinedIn_union_compl` hold for `K₁ = K₂ = {(0, 1)}`. -/
example : JoinedIn (({((0 : ℝ), (1 : ℝ))} : Set (ℝ × ℝ)) ∪ {((0 : ℝ), (1 : ℝ))})ᶜ (0, 0) (2, 0) := by
  have hseg : JoinedIn (({((0 : ℝ), (1 : ℝ))} : Set (ℝ × ℝ))ᶜ) (0, 0) (2, 0) := by
    refine JoinedIn.of_segment_subset ?_
    intro p hp hp1
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hp
    simp at hp1
  exact joinedIn_union_compl isCompact_singleton isCompact_singleton (R := (0, 1))
    (by simp) hseg hseg |>.mono (by simp)

/-- Wrong model: two disjoint singletons do not meet in one point, so the hypothesis of the lemma
does not hold for them. -/
example : ({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) ∩ {((1 : ℝ), (0 : ℝ))} ≠ {((0 : ℝ), (0 : ℝ))} := by
  intro h
  have : ((0 : ℝ), (0 : ℝ)) ∈ ({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) ∩ {((1 : ℝ), (0 : ℝ))} := by
    rw [h]; rfl
  simp at this

end Lightlike.PL
