import Mathlib

/-!
# Chart targets are open in a manifold without boundary

For a manifold `M` without boundary (`BoundarylessManifold I M`) every point is an interior point, in
every chart of the atlas around it (`ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`). Hence the target
of every extended chart `extChartAt I x` is open in the model space `E`, and so a neighbourhood of each
of its points. Mathlib has this only for `I.Boundaryless` (`isOpen_extChartAt_target`), a stronger
hypothesis, since `range I` is then all of `E`.

Supporting lemma for the causal structure; no catalogue entry.
-/

open Set Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **In a manifold without boundary every extended chart has an open target.** -/
theorem isOpen_extChartAt_target_of_boundaryless [BoundarylessManifold I M] (x : M) :
    IsOpen (extChartAt I x).target := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  set q := (extChartAt I x).symm w with hq
  have hqs : q ∈ (chartAt H x).source := by
    rw [← extChartAt_source I x]; exact (extChartAt I x).map_target hw
  have hint := (I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp) (chart_mem_atlas H x) hqs).1
    (BoundarylessManifold.isInteriorPoint' (I := I) q)
  have hwq : (chartAt H x).extend I q = w := (extChartAt I x).right_inv hw
  rw [hwq] at hint
  exact mem_interior_iff_mem_nhds.1 hint

/-- The target of the chart at `y` is a neighbourhood of `φ y`, in a manifold without boundary. -/
theorem extChartAt_target_mem_nhds_of_boundaryless [BoundarylessManifold I M] (y : M) :
    (extChartAt I y).target ∈ 𝓝 (extChartAt I y y) :=
  (isOpen_extChartAt_target_of_boundaryless y).mem_nhds (mem_extChartAt_target y)

end Lightlike.Causal
