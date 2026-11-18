import Lightlike.Spacetime.CausalLadder.ChartLine
import Lightlike.Spacetime.CausalLadder.StrongCausality

/-!
# Global hyperbolicity implies causal simplicity (manifold without boundary)

Strong causality gives causality (`causal_of_stronglyCausal`). The causal future `J⁺(x)` is closed:
if `y` lies in its closure, there is a point `z` in the causal future of every point near `y`
(`exists_future_point`, a straight line in a chart), so the points of `J⁺(x)` near `y` lie in the
causal diamond `J⁺(x) ∩ J⁻(z)`, which is compact by global hyperbolicity, hence closed; so `y` lies
in it. The causal past is closed in the same way, using a point in the causal past of every point
near `y`.

The straight-line step uses that the manifold has no boundary (`BoundarylessManifold I M`), so that
the chart image is a neighbourhood of the image of the point and a short segment in the time direction
stays in the manifold. Hawking–Ellis take space-time to be a manifold without boundary.

Supporting lemma for the causal ladder.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Global hyperbolicity implies causal simplicity**, for a manifold without boundary. -/
theorem isCausallySimple_of_isGloballyHyperbolic_boundaryless [BoundarylessManifold I M] [T2Space M]
    (h : IsGloballyHyperbolic T) : IsCausallySimple T := by
  refine ⟨causal_of_stronglyCausal T h.1, fun x => ⟨?_, ?_⟩⟩
  · refine closure_subset_iff_isClosed.1 fun y hy => ?_
    obtain ⟨z, hz⟩ := exists_future_point T y
    have hD : IsClosed (causalFuture T x ∩ causalPast T z) := (h.2 x z).isClosed
    have hyD : y ∈ closure (causalFuture T x ∩ causalPast T z) := by
      rw [mem_closure_iff_nhds]
      intro t ht
      obtain ⟨y', ⟨hy't, hy'z⟩, hy'x⟩ := mem_closure_iff_nhds.1 hy (t ∩ {y' | z ∈ causalFuture T y'})
        (inter_mem ht hz)
      exact ⟨y', hy't, hy'x, hy'z⟩
    rw [hD.closure_eq] at hyD
    exact hyD.1
  · refine closure_subset_iff_isClosed.1 fun y hy => ?_
    obtain ⟨z, hz⟩ := exists_past_point T y
    have hD : IsClosed (causalFuture T z ∩ causalPast T x) := (h.2 z x).isClosed
    have hyD : y ∈ closure (causalFuture T z ∩ causalPast T x) := by
      rw [mem_closure_iff_nhds]
      intro t ht
      obtain ⟨y', ⟨hy't, hy'z⟩, hy'x⟩ := mem_closure_iff_nhds.1 hy (t ∩ {y' | y' ∈ causalFuture T z})
        (inter_mem ht hz)
      exact ⟨y', hy't, hy'z, hy'x⟩
    rw [hD.closure_eq] at hyD
    exact hyD.2

end Lightlike.Causal
