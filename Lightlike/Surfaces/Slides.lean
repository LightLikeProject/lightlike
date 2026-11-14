import Lightlike.Surfaces.Glue
import Lightlike.Surfaces.Models

/-!
# The two pieces are good

The 6-vertex projective plane `P6` and the 9-vertex torus `T9` satisfy `GoodPiece`: every
condition is a finite check, proved by `decide +kernel`. The slide chains (21 moves for `P6`,
44 for `T9`) move the piece across the edge `12` of the surrounding triangle; they were found and
checked by `scripts/pl/surf_chains.py` and are checked again here by the kernel. The
automorphisms of `P6 − {0, 1, 2}` and `T9 − {0, 1, 2}` realising each order of `0, 1, 2` are given
as tables (`surf_chains.py auts`).

With `GoodPiece.homog` this gives: a connected sum with `P6` or `T9` does not depend, up to
moves, on the triangle or the labelling used.
-/

open Finset

namespace Lightlike.Surfaces

open Lightlike.PR

set_option maxRecDepth 100000

/-- `P6` is a good piece with interior labels below `6`. -/
theorem goodPiece_P6 : GoodPiece P6 6 where
  three_le := by norm_num
  closed := isClosed2_P6
  tri := isTri2_P6
  mem₀ := by decide
  verts := by decide +kernel
  inner := by decide +kernel
  surgOK := by decide +kernel
  reach := ⟨0, by decide +kernel⟩
  slide := ⟨[.flip 1 2 4 6, .flip 4 2 5 6, .flip 3 0 4 2, .flip 2 5 3 6, .flip 4 0 5 2,
    .flip 5 0 1 2, .sub 4 1 3 7, .flip 4 3 7 2, .flip 4 1 7 6, .flip 4 2 5 7, .unsub 5 6 7 4,
    .sub 3 1 5 8, .flip 3 5 8 6, .flip 3 1 7 8, .flip 3 6 8 2, .unsub 2 7 8 3, .sub 5 1 2 9,
    .flip 5 2 9 7, .flip 5 1 8 9, .flip 5 7 9 6, .unsub 6 8 9 5], by decide +kernel⟩
  aut := by
    intro i j l hi hj hl hij hil hjl
    interval_cases i <;> interval_cases j <;> interval_cases l
    all_goals try first
      | exact absurd rfl hij
      | exact absurd rfl hil
      | exact absurd rfl hjl
    · exact ⟨tabE [0, 1, 2, 3, 4, 5] 0 (by decide), rfl, rfl, rfl, by decide +kernel⟩
    · exact ⟨tabE [0, 2, 1, 5, 4, 3] 0 (by decide), rfl, rfl, rfl, by decide +kernel⟩
    · exact ⟨tabE [1, 0, 2, 4, 3, 5] 0 (by decide), rfl, rfl, rfl, by decide +kernel⟩
    · exact ⟨tabE [1, 2, 0, 5, 3, 4] 0 (by decide), rfl, rfl, rfl, by decide +kernel⟩
    · exact ⟨tabE [2, 0, 1, 4, 5, 3] 0 (by decide), rfl, rfl, rfl, by decide +kernel⟩
    · exact ⟨tabE [2, 1, 0, 3, 5, 4] 0 (by decide), rfl, rfl, rfl, by decide +kernel⟩

/-- `T9` is a good piece with interior labels below `9`. -/
theorem goodPiece_T9 : GoodPiece T9 9 where
  three_le := by norm_num
  closed := isClosed2_T9
  tri := isTri2_T9
  mem₀ := by decide
  verts := by decide +kernel
  inner := by decide +kernel
  surgOK := by decide +kernel
  reach := ⟨0, by decide +kernel⟩
  slide := ⟨[.flip 1 2 9 4, .flip 4 1 3 9, .flip 3 1 8 9, .flip 8 1 9 7, .flip 7 0 6 1,
    .flip 0 6 3 1, .flip 0 3 5 1, .flip 0 5 1 2, .sub 6 1 3 10, .flip 6 3 10 8, .flip 6 1 10 7,
    .flip 6 7 4 10, .flip 6 4 10 2, .unsub 2 8 10 6, .sub 4 2 9 11, .flip 4 9 11 3,
    .flip 4 2 10 11, .flip 4 3 11 5, .flip 4 5 11 7, .unsub 7 10 11 4, .sub 7 1 9 12,
    .flip 7 9 12 8, .flip 7 1 10 12, .flip 7 8 12 5, .flip 7 5 11 12, .unsub 10 11 12 7,
    .sub 3 1 5 13, .flip 3 5 13 11, .flip 3 1 10 13, .flip 3 10 8 13, .flip 3 8 9 13,
    .unsub 9 11 13 3, .sub 5 1 2 14, .flip 5 2 14 8, .flip 5 1 14 13, .flip 5 8 12 14,
    .flip 5 12 14 11, .unsub 11 13 14 5, .sub 8 2 10 15, .flip 8 10 15 13, .flip 8 2 14 15,
    .flip 8 13 15 9, .flip 8 9 12 15, .unsub 12 14 15 8], by decide +kernel⟩
  aut := by
    intro i j l hi hj hl hij hil hjl
    interval_cases i <;> interval_cases j <;> interval_cases l
    all_goals try first
      | exact absurd rfl hij
      | exact absurd rfl hil
      | exact absurd rfl hjl
    · exact ⟨tabE [0, 1, 2, 3, 4, 5, 6, 7, 8] 0 (by decide), rfl, rfl, rfl, by decide +kernel⟩
    · exact ⟨tabE [0, 2, 1, 6, 4, 7, 3, 5, 8] 0 (by decide), rfl, rfl, rfl, by decide +kernel⟩
    · exact ⟨tabE [1, 0, 2, 3, 5, 4, 8, 7, 6] 0 (by decide), rfl, rfl, rfl, by decide +kernel⟩
    · exact ⟨tabE [1, 2, 0, 8, 5, 7, 3, 4, 6] 0 (by decide), rfl, rfl, rfl, by decide +kernel⟩
    · exact ⟨tabE [2, 0, 1, 6, 7, 4, 8, 5, 3] 0 (by decide), rfl, rfl, rfl, by decide +kernel⟩
    · exact ⟨tabE [2, 1, 0, 8, 7, 5, 6, 4, 3] 0 (by decide), rfl, rfl, rfl, by decide +kernel⟩

end Lightlike.Surfaces
