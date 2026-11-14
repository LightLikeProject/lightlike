module

public import Lightlike.PonzanoRegge.InverseMoves

/-!
# Tests for the 3-2 and 4-1 moves

* `hmove32`, `move32_K32`: the three tetrahedra `0134, 1234, 2034` around the edge `34` satisfy
  the 3-2 preconditions, and the move gives the two tetrahedra `0123, 0124`.
* `hmove41`, `move41_K41`: the four tetrahedra `0124, 0134, 0234, 1234` around the vertex `4`
  satisfy the 4-1 preconditions, and the move gives the single tetrahedron `0123`.
* `move23_move32_K32`, `move14_move41_K41`: the forward moves give the original complexes back.
* Wrong inputs are rejected: `not_isMove32_star` (a fourth tetrahedron `3456` on the edge `34`),
  `not_isMove32_fresh` (the triangle `012` already present), `not_isMove41_boundary` (the boundary
  of the 4-simplex: removing `4` would duplicate the tetrahedron `0123`).
* `gf_move32_example`, `gf_move41_example`: the amplitude theorems apply (their hypotheses are
  satisfiable).
-/

@[expose] public section

open Finset

namespace Lightlike.PR.Test.Inverse

-- `decide` on explicit complexes over `Fin 6`, `Fin 7` needs more recursion depth.
set_option maxRecDepth 10000

/-- Three tetrahedra around the edge `34`. -/
def K32 : Complex3 (Fin 5) := ⟨{{0, 1, 3, 4}, {1, 2, 3, 4}, {2, 0, 3, 4}}, by decide⟩

/-- The 3-2 preconditions hold for `K32` with `A, B, C, D, E = 0, 1, 2, 3, 4`. -/
theorem hmove32 : IsMove32 K32 0 1 2 3 4 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The 3-2 move turns the three tetrahedra into `0123, 0124`. -/
theorem move32_K32 : (move32 K32 hmove32).tets = {{0, 1, 2, 3}, {0, 1, 2, 4}} := by decide

/-- The 2-3 move gives `K32` back. -/
theorem move23_move32_K32 : move23 (move32 K32 hmove32) (isMove23_move32 hmove32) = K32 :=
  move23_move32 hmove32

/-- Four tetrahedra around the vertex `4`. -/
def K41 : Complex3 (Fin 5) := ⟨{{0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}}, by decide⟩

/-- The 4-1 preconditions hold for `K41` with `A, B, C, D, E = 0, 1, 2, 3, 4`. -/
theorem hmove41 : IsMove41 K41 0 1 2 3 4 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The 4-1 move turns the four tetrahedra into `0123`. -/
theorem move41_K41 : (move41 K41 hmove41).tets = {{0, 1, 2, 3}} := by decide

/-- The 1-4 move gives `K41` back. -/
theorem move14_move41_K41 : move14 (move41 K41 hmove41) (isMove14_move41 hmove41) = K41 :=
  move14_move41 hmove41

/-- **Wrong input:** a fourth tetrahedron `3456` on the edge `34` blocks the 3-2 move. -/
theorem not_isMove32_star :
    ¬ IsMove32 (⟨{{0, 1, 3, 4}, {1, 2, 3, 4}, {2, 0, 3, 4}, {3, 4, 5, 6}}, by decide⟩ :
      Complex3 (Fin 7)) 0 1 2 3 4 := by
  intro h
  have := h.star {3, 4, 5, 6} (by decide) (by decide)
  revert this
  decide

/-- **Wrong input:** if the triangle `012` already lies in a tetrahedron `0125`, the 3-2 move is
blocked (it would create a second copy of that triangle's neighbourhood). -/
theorem not_isMove32_fresh :
    ¬ IsMove32 (⟨{{0, 1, 3, 4}, {1, 2, 3, 4}, {2, 0, 3, 4}, {0, 1, 2, 5}}, by decide⟩ :
      Complex3 (Fin 6)) 0 1 2 3 4 := by
  intro h
  exact h.fresh {0, 1, 2, 5} (by decide) (by decide)

/-- **Wrong input:** on the boundary of the 4-simplex the 4-1 move removing `4` is blocked:
`0123` is already a tetrahedron. -/
theorem not_isMove41_boundary :
    ¬ IsMove41 (⟨{{0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}},
      by decide⟩ : Complex3 (Fin 5)) 0 1 2 3 4 := by
  intro h
  exact h.fresh (by decide)

/-- The 3-2 amplitude theorem applies to `K32` (cutoff 4 on the removed edge `34`, 2 elsewhere). -/
theorem gf_move32_example :
    amplitudeGF (move32 K32 hmove32) ∅ (fun e => if e = {3, 4} then 4 else 2) =
      amplitudeGF K32 ∅ (fun e => if e = {3, 4} then 4 else 2) :=
  amplitudeGF_move32 K32 hmove32 ∅ (empty_subset _) (notMem_empty _) _ (by decide)

/-- The 4-1 amplitude theorem applies to `K41` with the gauge edge `34` (uniform cutoff 1). -/
theorem gf_move41_example :
    amplitudeGF (move41 K41 hmove41) ∅ (fun _ => 1) =
      amplitudeGF K41 (insert {3, 4} ∅) (fun _ => 1) :=
  amplitudeGF_move41 K41 hmove41 ∅ (empty_subset _) (by simp) _ le_rfl le_rfl le_rfl

end Lightlike.PR.Test.Inverse
