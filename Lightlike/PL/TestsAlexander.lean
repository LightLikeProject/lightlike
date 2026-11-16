import Lightlike.PL.Alexander
import Lightlike.PL.TestsGrating

/-!
# Checks of 2-chains, the cycle theorem and Alexander's theorem

On the `2 × 2` grating `G0` of `TestsGrating.lean`: the boundary of a single cell is its four
sides, a cycle bounds a 2-chain, and wrong-model checks: a single edge is not the boundary of any
2-chain, and the 2-chain of all cells has a nonempty boundary (the outer rectangle). Non-vacuity of
`alexander`: its hypotheses hold for empty chains and a far compact set.
-/

open Set

namespace Lightlike.PL

namespace Grating

/-- The boundary of a single cell is its four sides. -/
example : G0.bdy₂ {((0 : Fin 2), (0 : Fin 2))} = G0.sides (0, 0) := bdy₂_singleton G0 _

/-- The four sides of the cell `(0, 0)` form a cycle, so they bound a 2-chain. -/
example : ∃ w : Finset G0.Cell, G0.bdy₂ w = G0.sides (0, 0) :=
  G0.exists_bdy₂ (bdy_sides G0 _)

/-- Wrong model: a single edge has a nonempty boundary, so it is the boundary of no 2-chain. -/
example : ∀ w : Finset G0.Cell, G0.bdy₂ w ≠ {Edge.h 0 0} := by
  intro w h
  have h1 := bdy_bdy₂ G0 w
  rw [h, bdy_singleton] at h1
  have h2 : ({(G0.ends (Edge.h (0 : Fin 2) (0 : Fin 3))).1} : Finset G0.Vert) =
      {(G0.ends (Edge.h (0 : Fin 2) (0 : Fin 3))).2} := symmDiff_eq_bot.1 h1
  exact G0.ends_ne _ (Finset.singleton_inj.1 h2)

/-- Wrong model: the 2-chain of all cells is not a cycle-free chain: its boundary is the outer
rectangle, which is not empty. -/
example : G0.bdy₂ Finset.univ ≠ ∅ := by decide

/-- Non-vacuity of `alexander`: the hypotheses hold for empty chains, a point, and the empty 2-chain. -/
example : JoinedIn (({((5 : ℝ), (5 : ℝ))} : Set (ℝ × ℝ)) ∪ ∅)ᶜ (G0.pt (0, 0)) (G0.pt (0, 0)) := by
  refine G0.alexander (x := (0, 0)) (y := (0, 0)) (l₁ := ∅) (l₂ := ∅) (w := ∅) (E := ∅) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [pt]
  · simp [bdy, deg]
  · simp
  · simp [bdy, deg]
  · simp
  · simp
  · simp [bdy₂]
  · simp

end Grating

end Lightlike.PL
