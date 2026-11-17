import Lightlike.PL.Grating

/-!
# Checks of the gratings and mod-2 chains

Values of the boundary on a `2 × 2` grating with unit squares, the non-vacuity of
`Grating.joinedIn_of_bdy`, and wrong-model checks: chains that do not join their points have a
boundary that is not a pair, or whose ends are not linked.
-/

open Finset

namespace Lightlike.PL

namespace Grating

/-- The `2 × 2` grating with vertices `{0, 1, 2}²`. -/
abbrev G0 : Grating where
  n := 2
  m := 2
  a := fun i => (i : ℝ)
  b := fun j => (j : ℝ)
  ha := fun i j h => by
    show ((i : ℕ) : ℝ) < (j : ℕ)
    exact_mod_cast Fin.lt_def.1 h
  hb := fun i j h => by
    show ((i : ℕ) : ℝ) < (j : ℕ)
    exact_mod_cast Fin.lt_def.1 h

/-- A single edge has its two ends as boundary. -/
example : G0.bdy {.h 0 0} = {(0, 0), (1, 0)} := by decide

/-- A path of two edges has its two outer ends as boundary. -/
example : G0.bdy {.h 0 0, .h 1 0} = {(0, 0), (2, 0)} := by decide

/-- A closed unit square has empty boundary. -/
example : G0.bdy {.h 0 0, .h 0 1, .v 0 0, .v 1 0} = ∅ := by decide

/-- Non-vacuity of `joinedIn_of_bdy`: its hypothesis holds for the path of two edges. -/
example : JoinedIn (G0.locus {.h 0 0, .h 1 0}) (G0.pt (0, 0)) (G0.pt (2, 0)) :=
  G0.joinedIn_of_bdy (by decide)

/-- Wrong model: two disjoint edges have four boundary vertices, so their boundary is not a pair. -/
example : ∀ x y, G0.bdy {.h 0 0, .h 0 2} ≠ {x, y} := by
  intro x y h
  have : (G0.bdy {.h 0 0, .h 0 2}).card = 4 := by decide
  rw [h] at this
  have := Finset.card_le_two (a := x) (b := y)
  omega

/-- Wrong model: the two disjoint edges do not link their ends: everything reachable from `(0, 0)`
stays on the row `0`, while `(1, 2)` is on the row `2`. -/
example : ¬ G0.Reach {.h 0 0, .h 0 2} (0, 0) (1, 2) := by
  intro h
  have key : ∀ y, G0.Reach {.h 0 0, .h 0 2} (0, 0) y → y.2 = 0 := by
    intro y hy
    induction hy with
    | refl => rfl
    | tail _ hs ih =>
      obtain ⟨e, he, h'⟩ := hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;> simp [ends, Prod.ext_iff] at h' <;>
        first | omega | (rcases h' with h' | h' <;> simp_all [Fin.ext_iff])
  have := key _ h
  simp [Fin.ext_iff] at this

end Grating

end Lightlike.PL
