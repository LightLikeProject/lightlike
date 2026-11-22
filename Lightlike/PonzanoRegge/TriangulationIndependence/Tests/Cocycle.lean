module

public import Lightlike.PonzanoRegge.TriangulationIndependence.Cocycle
public import Lightlike.Tests.TreeDependence

/-!
# Trust check: the cohomological obstruction sees the ring of three tetrahedra

On the ring `R` (tetrahedra `0123`, `2345`, `4501`) the cochain `ω` that is `1` on the four edges
joining `{4,5}` to `{0,1}` is a `ZMod 2`-cocycle. It is not a coboundary: the potential `g` that
makes the star `T1` flat is `1` on `4, 5` and `0` elsewhere, and the maximal tree `T2` of the same
ring is not flat for it (the edge `25` of `T2` has `g 2 + g 5 = 1` but `ω 25 = 0`). So
`not_treeConnected_of_cocycle` proves `¬ TreeConnected R` without computing any amplitude; the
pair `(T1, T2)` is the pair that has different amplitudes (`-7`, `-15`) in
`Lightlike/Tests/TreeDependence.lean`. This is a third derivation of the same fact and agrees
with it.
-/

@[expose] public section

namespace Lightlike.PR.Test.Ring

open Finset

/-- The winding cochain: `1` on the four edges between `{4,5}` and `{0,1}`. -/
def ω : Finset (Fin 6) → ZMod 2 :=
  fun s => if s ∈ ({{4, 0}, {4, 1}, {5, 0}, {5, 1}} : Finset (Finset (Fin 6))) then 1 else 0

/-- The potential that makes the star `T1` flat. -/
def gT1 : Fin 6 → ZMod 2 := ![0, 0, 0, 0, 1, 1]

/-- `ω` is a cocycle on the 2-skeleton of the ring. -/
theorem cocycle2_R : Cocycle2 R ω := by
  unfold Cocycle2 ω
  decide +revert

/-- The star `T1` is flat for `gT1`. -/
theorem flatOn_T1 : FlatOn ω gT1 T1 := by
  unfold FlatOn ω gT1 T1
  decide +revert

/-- The maximal tree `T2` is not flat for `gT1`. -/
theorem not_flatOn_T2 : ¬ FlatOn ω gT1 T2 := by
  intro h
  have := @h 2 5 (by decide)
  revert this
  unfold ω gT1
  decide

/-- The cohomological obstruction gives `¬ TreeConnected R`, in agreement with
`not_treeConnected_R`. -/
theorem not_treeConnected_R_of_cocycle : ¬ TreeConnected R :=
  not_treeConnected_of_cocycle cocycle2_R isMaxTree_T1 isMaxTree_T2 flatOn_T1 not_flatOn_T2

end Lightlike.PR.Test.Ring
