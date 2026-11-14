import Lightlike.PL.Complex4
import Lightlike.FourD.Tests

/-!
# Trust checks for the 4D bridge (milestone PL2)

* `isCombManifold4_K0`, `isCombManifold4_K3`: the boundary of the 5-simplex of the tests of `FourD/`
  is a closed combinatorial 4-manifold, and so is the result of its 1-5, 2-4 and 3-3 moves (by
  `isCombManifold4_move_iff`).
* `ofComplex4_K1`: the 1-5 move of those tests is the bistellar move `κ(01234, 6)`;
  `isMove_of_isBistellar_K0`: the bistellar conditions give back the 4D move.
* `not_isCombManifold4_badDrop`, `not_isCombManifold4_badVertex`: **wrong models** - the malformed
  moves of those tests do not give combinatorial 4-manifolds (they are not closed
  pseudo-manifolds, and combinatorial 4-manifolds are).
-/

open Finset Lightlike.FourD Lightlike.FourD.Tests

namespace Lightlike.PL

/-- The boundary of the 5-simplex `012345` (inside `Fin 8`) is a closed combinatorial 4-manifold. -/
theorem isCombManifold4_K0 : IsCombManifold4 K0 := isCombManifold4_sphere (by decide +kernel)

/-- After the 1-5, 2-4 and 3-3 moves of the tests of `FourD/` it still is one. -/
theorem isCombManifold4_K3 : IsCombManifold4 K3 :=
  (isCombManifold4_move_iff isMove33).2 ((isCombManifold4_move_iff isMove24).2
    ((isCombManifold4_move_iff isMove15).2 isCombManifold4_K0))

/-- The 1-5 move of the tests of `FourD/` is the bistellar move `κ(01234, 6)`. -/
theorem ofComplex4_K1 :
    ofComplex4 K1 = (ofComplex4 K0).bistellar {0, 1, 2, 3, 4} {6} (isBistellar_move4 isMove15) :=
  ofComplex4_move isMove15

/-- The bistellar conditions of `κ(01234, 6)` on `K0` give back the 4D move. -/
theorem isMove_of_isBistellar_K0 : K0.IsMove {0, 1, 2, 3, 4} {6} :=
  isMove_of_isBistellar (isBistellar_move4 isMove15) (by decide +kernel)

/-- **Wrong model**: leaving out a new 4-simplex of a 2-4 move does not give a combinatorial
4-manifold. -/
theorem not_isCombManifold4_badDrop : ¬ IsCombManifold4 badDrop := fun h =>
  badDrop_fails.1 h.isClosed4

/-- **Wrong model**: a 1-5 move onto an existing vertex does not give a combinatorial 4-manifold. -/
theorem not_isCombManifold4_badVertex : ¬ IsCombManifold4 badVertex := fun h =>
  badVertex_fails.2 h.isClosed4

end Lightlike.PL
