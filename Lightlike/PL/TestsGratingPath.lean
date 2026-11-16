import Lightlike.PL.GratingPath
import Lightlike.PL.TestsGrating

/-!
# Checks of the path-to-chain step on a grating

Values of the grid distance and of the box on the `2 × 2` grating `G0` of `TestsGrating.lean`,
non-vacuity of `exists_chain_of_joinedIn` for a compact set and a path in its complement, and
wrong-model checks: a compact set that contains an endpoint admits no path in its complement, and
the box of two points does not contain a point outside their coordinate ranges.
-/

open Set

namespace Lightlike.PL

namespace Grating

/-- The grid distance of two vertices is the sum of the index differences. -/
example : G0.gdist (0, 0) (2, 1) = 3 := by decide

/-- A point between two vertices lies in their box. -/
example : ((1 : ℝ), (1 : ℝ) / 2) ∈ Box ((0 : ℝ), (0 : ℝ)) (2, 1) := by
  refine ⟨?_, ?_⟩
  · simp
  · simp; norm_num

/-- Wrong model: a point above the range of the second coordinates is not in the box. -/
example : ((1 : ℝ), (2 : ℝ)) ∉ Box ((0 : ℝ), (0 : ℝ)) (2, 1) := by
  intro h
  have := h.2
  simp at this

/-- Non-vacuity of `exists_chain_of_joinedIn`: the compact set `{(1, 1)}` and the points `(0, 0)`,
`(2, 0)`, which are joined by the segment on the first axis. -/
example : ∃ ρ > 0, ∃ Xs Ys : Finset ℝ, ∀ G : Grating, ↑Xs ⊆ G.xs → ↑Ys ⊆ G.ys →
    ∃ (x y : G.Vert) (c : Finset G.Edge), G.pt x = ((0 : ℝ), (0 : ℝ)) ∧ G.pt y = ((2 : ℝ), (0 : ℝ)) ∧
      (∀ p ∈ G.locus c, ∀ a ∈ ({((1 : ℝ), (1 : ℝ))} : Set (ℝ × ℝ)), ρ ≤ dist p a) ∧
      G.bdy c = symmDiff {x} {y} := by
  refine exists_chain_of_joinedIn (isCompact_singleton) ?_
  refine JoinedIn.of_segment_subset ?_
  intro p hp hp1
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hp
  simp at hp1

/-- Wrong model: the hypothesis of `exists_chain_of_joinedIn` fails when an endpoint lies in the
compact set. -/
example : ¬ JoinedIn ({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ))ᶜ (0, 0) (1, 1) := fun h => h.source_mem rfl

end Grating

end Lightlike.PL
