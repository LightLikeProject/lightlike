import Lightlike.Spacetime.Causal.TimeReversal
import Lightlike.Spacetime.CausalLadder.PerturbTimelike

/-!
# The chronological past is open

In a manifold without boundary the chronological future is open (`T-GE2-P7`, proved from
`exists_nhds_reach`; `isOpen_chronFuture_of_reach` repeats the short argument inside the library, since
the task file is not imported by it). The chronological past for `T` is the chronological future for the
reversed orientation (`chronFuture_reverse`), so it is open too.

Supporting lemmas for the causal structure; no catalogue entry.
-/

open Set Bundle Manifold Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **The chronological future is open** (the statement of `T-GE2-P7`, in the library). -/
theorem isOpen_chronFuture_of_reach (x : M) : IsOpen (chronFuture T x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨γ, a, b, hab, hγ, rfl, rfl⟩
  obtain ⟨U, hU, hreach⟩ := exists_nhds_reach T hab hγ
  filter_upwards [hU] with z hz
  obtain ⟨G, e, hae, hG, hG1, hG2⟩ := hreach z hz
  exact ⟨G, a, e, hae, hG, hG1, hG2⟩

/-- **The chronological past is open.** -/
theorem isOpen_chronPast (x : M) : IsOpen (chronPast T x) := by
  rw [← chronFuture_reverse]
  exact isOpen_chronFuture_of_reach T.reverse x

end Lightlike.Causal
