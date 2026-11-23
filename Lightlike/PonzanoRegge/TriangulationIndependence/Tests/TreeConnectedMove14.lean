module

public import Lightlike.PonzanoRegge.TriangulationIndependence.TreeConnectedMove14
public import Lightlike.Tests.Manifold

/-!
# Trust check: tree-independence after a 1-4 move on the boundary of the 4-simplex

`Lightlike.PR.Test.Manifold.S3` is the boundary of the 4-simplex inside `Fin 6`. It has a complete
2-skeleton, hence is tree-connected; the stacked sphere `move14 S3 _` is tree-connected by
`treeConnected_move14`, so its gauge-fixed amplitude does not depend on the maximal tree.
-/

@[expose] public section

namespace Lightlike.PR.Test.Move14

open Finset Lightlike.PR.Test.Manifold

set_option maxRecDepth 10000

/-- `S3` has a complete 2-skeleton. -/
theorem S3_complete : ∀ ⦃x y z : Fin 6⦄, x ∈ S3.verts → y ∈ S3.verts → z ∈ S3.verts →
    x ≠ y → y ≠ z → x ≠ z → ({x, y, z} : Finset (Fin 6)) ∈ S3.tris := by
  decide +kernel

theorem treeConnected_S3 : TreeConnected S3 :=
  treeConnected_of_complete_triangles S3 S3_complete

/-- The stacked 3-sphere (boundary of the 4-simplex with one tetrahedron subdivided). -/
theorem treeConnected_S3_14 : TreeConnected (move14 S3 hmove14_S3) :=
  treeConnected_move14 hmove14_S3 treeConnected_S3

theorem stacked_S3_14 : Stacked S3 (move14 S3 hmove14_S3) :=
  Stacked.step Stacked.base hmove14_S3

/-- The stacked sphere is a closed combinatorial 3-manifold with tree-independent amplitude. -/
theorem stacked_S3_14_spec :
    IsCombManifold (move14 S3 hmove14_S3) ∧ TreeConnected (move14 S3 hmove14_S3) :=
  ⟨isCombManifold_S3_14, treeConnected_S3_14⟩

end Lightlike.PR.Test.Move14
