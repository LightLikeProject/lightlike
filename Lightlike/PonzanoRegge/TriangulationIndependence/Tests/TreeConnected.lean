module

public import Lightlike.PonzanoRegge.TriangulationIndependence.TreeConnected
public import Lightlike.Tests.TreeDependence

/-!
# Trust check: the ring of three tetrahedra and tree-connectedness

The ring `R` has maximal trees `T1`, `T2` with different amplitudes (`-7`, `-15`), so `R` is not
`TreeConnected`. It is also not a combinatorial 3-manifold. This is consistent with the open
closed-manifold statement: nothing here says that a closed manifold fails `TreeConnected`.
-/

@[expose] public section

namespace Lightlike.PR.Test.Ring

/-- The ring of three tetrahedra is not tree-connected (wrong-input control for
`TreeConnected.amplitudeGF_eq`: it would force `-7 = -15`). -/
theorem not_treeConnected_R : ¬ TreeConnected R :=
  not_treeConnected_of_dependent isMaxTree_T1 isMaxTree_T2 half
    (by rw [amplitudeGF_R_T1, amplitudeGF_R_T2]; norm_num)

/-- The ring is neither a manifold nor tree-connected: both facts together. -/
theorem R_not_manifold_not_treeConnected : ¬ IsCombManifold R ∧ ¬ TreeConnected R :=
  ⟨not_isCombManifold_R, not_treeConnected_R⟩

end Lightlike.PR.Test.Ring
