import Lightlike.SpinFoam.Tests
import Lightlike.SpinFoam.OoguriGaugeFixed.ForcingClosureAlgebra

/-!
# Tests for the forcing closure of the gauge-fixed Ooguri state sum

Concrete checks of `forcedTris`, `forces_iff_subset_forcedTris`, `forcedTris_forcedTris` and
`amplitudeGF_eq_of_forcedTris_eq` on the boundary `∂Δ⁵` of the 5-simplex, with the gauge sets
`starT` (cone from a vertex), `twistT` (not a star) and the too small set `gauge9`.
-/

namespace Lightlike.SpinFoam

open Lightlike.FourD Lightlike.FourD.Tests

/-- `starT` forces every triangle of `∂Δ⁵`. -/
theorem forces_starT : Forces sphere6 sphere6.tris starT :=
  forces_of_forcesBy
    (l := [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}),
      ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}),
      ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}),
      ({2, 3, 4, 5}, {2, 3, 4})])
    (by decide +kernel)

/-- `twistT` forces every triangle of `∂Δ⁵`. -/
theorem forces_twistT : Forces sphere6 sphere6.tris twistT :=
  forces_of_forcesBy
    (l := [({0, 1, 2, 3}, {1, 2, 3}), ({0, 1, 2, 4}, {0, 2, 4}), ({0, 1, 3, 4}, {0, 3, 4}),
      ({0, 1, 3, 5}, {0, 3, 5}), ({0, 2, 3, 4}, {2, 3, 4}), ({0, 2, 3, 5}, {0, 2, 5}),
      ({0, 3, 4, 5}, {0, 4, 5}), ({1, 2, 3, 5}, {1, 2, 5}), ({1, 3, 4, 5}, {1, 4, 5}),
      ({2, 3, 4, 5}, {2, 4, 5})])
    (by decide +kernel)

/-- The forcing closure of `starT` is all of the triangles of `∂Δ⁵`. -/
theorem forcedTris_starT : forcedTris sphere6 starT = sphere6.tris :=
  Finset.Subset.antisymm (forcedTris_subset_tris _ _)
    ((forces_iff_subset_forcedTris subset_rfl).mp forces_starT)

/-- The forcing closure of `twistT` is all of the triangles of `∂Δ⁵`. -/
theorem forcedTris_twistT : forcedTris sphere6 twistT = sphere6.tris :=
  Finset.Subset.antisymm (forcedTris_subset_tris _ _)
    ((forces_iff_subset_forcedTris subset_rfl).mp forces_twistT)

/-- Gauge independence through closures: `starT` and `twistT` give the same state sum, deduced
from the equality of their forcing closures and not from the value `1`. -/
theorem amplitudeGF_starT_eq_twistT (cut : Finset (Fin 6) → ℕ) :
    amplitudeGF sphere6 starT cut = amplitudeGF sphere6 twistT cut :=
  amplitudeGF_eq_of_forcedTris_eq (Finset.filter_subset _ _) (by decide +kernel)
    (forcedTris_starT.trans forcedTris_twistT.symm) cut

/-- The closure is idempotent on a concrete example. -/
example : forcedTris sphere6 (forcedTris sphere6 starT) = sphere6.tris := by
  rw [forcedTris_forcedTris, forcedTris_starT]

/-- The gauge set `gauge9` has a smaller closure than `starT` (the sum differs, so the closures
must differ, by `amplitudeGF_eq_of_forcedTris_eq`). -/
theorem forcedTris_gauge9_ne : forcedTris sphere6 gauge9 ≠ forcedTris sphere6 starT := fun h => by
  have := amplitudeGF_eq_of_forcedTris_eq (K := sphere6) (T := gauge9) (T' := starT)
    (fun f hf => (Finset.filter_subset _ _) (Finset.mem_of_mem_erase hf)) (Finset.filter_subset _ _)
    h (fun _ => 1)
  rw [amplitudeGF_gauge9_one, amplitudeGF_starT] at this
  norm_num at this

end Lightlike.SpinFoam
