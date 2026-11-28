import Lightlike.PL.MoveDimension
import Lightlike.PL.TestsPachner

/-!
# Trust checks for the dimension of a bistellar move

* On the boundary of the tetrahedron (a closed combinatorial 2-manifold) the 1-3 move on the
  triangle `012` with the new vertex `4` has `#A + #B = 3 + 1 = 4 = n + 2`, as
  `IsClosedCombManifold.card_add_card_of_isBistellar` says (non-vacuity).
* Wrong input: on the closed segment `simplex {0, 1}`, which is not a closed combinatorial
  manifold, the move subdividing the edge at the new vertex `2` exists and has `#A + #B = 3`, so the
  manifold hypothesis is not idle: for `n = 0` it would predict `2`.
-/

open Finset

namespace Lightlike.PL

open SComplex

/-- Non-vacuity: the theorem on the 1-3 move of the tetrahedron boundary. -/
example : #({0, 1, 2} : Finset (Fin 6)) + #({4} : Finset (Fin 6)) = 2 + 2 :=
  (isClosedCombManifold_boundary (n := 2) (by decide +kernel)).card_add_card_of_isBistellar oct₁

/-- The edge subdivision of a closed segment: a bistellar move with `#A + #B = 3`. -/
lemma segment_move : (simplex ({0, 1} : Finset (Fin 3))).IsBistellar {0, 1} {2} where
  nonempty_left := by decide +kernel
  nonempty_right := by decide +kernel
  disjoint := by decide +kernel
  link_eq := by apply SComplex.ext; decide +kernel
  notMem := by decide +kernel

/-- The closed segment is not a closed combinatorial `0`-manifold: the conclusion `#A + #B = 2`
fails for its edge subdivision. -/
example : ¬ IsClosedCombManifold 0 (simplex ({0, 1} : Finset (Fin 3))) := fun h => by
  have := h.card_add_card_of_isBistellar segment_move
  simp at this

end Lightlike.PL
