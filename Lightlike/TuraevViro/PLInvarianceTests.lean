import Lightlike.TuraevViro.PLInvariance
import Lightlike.PL.TestsPachner

/-!
# Trust check for `turaevViro3_plHomeomorphic`

The hypotheses are satisfiable on an actual pair of complexes: the boundary of the 4-simplex
(`simplex4`, 5 tetrahedra) and the boundary of the 16-cell (`cell16`, 16 tetrahedra) are stellar
equivalent (`stellarEquiv_cell16`), hence PL homeomorphic, `simplex4` is a closed combinatorial
3-manifold, and both are nonempty. So the theorem applies and gives equal `r = 3` state sums
for two triangulations with different numbers of tetrahedra.
-/

open Lightlike.PL Lightlike.PR

namespace Lightlike.TV

/-- The `r = 3` state sums of the boundary of the 4-simplex and of the boundary of the 16-cell
agree, by `turaevViro3_plHomeomorphic`. -/
theorem turaevViro3_simplex4_cell16 :
    turaevViro (r := 3) (by norm_num) simplex4 = turaevViro (r := 3) (by norm_num) cell16 :=
  turaevViro3_plHomeomorphic isCombManifold_simplex4
    ⟨{0, 1, 2, 3}, by simp [simplex4]⟩
    (Finset.card_pos.1 (by rw [card_cell16]; norm_num))
    (SComplex.PLHomeomorphic.of_stellarEquiv stellarEquiv_cell16)

end Lightlike.TV
