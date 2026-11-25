import Lightlike.Rows.G1_012.AchronalBoundary
import Lightlike.Spacetime.CausalLadder.GlobHypSimple
import Lightlike.Spacetime.CausalLadder.NearFuture

/-!
# The causal future of a compact set is closed in a globally hyperbolic spacetime (G1-012)

A globally hyperbolic spacetime is causally simple (`isCausallySimple_of_isGloballyHyperbolic_boundaryless`),
so `J⁺(x)` and `J⁻(x)` are closed. For a compact set `S`: if `y ∉ J⁺(S)` then each `s ∈ S` has a
point `w ≪ s` with `y ∉ J⁺(w)` (otherwise `I⁻(s) ⊆ J⁻(y)`, and `s` is in the closure of `I⁻(s)`, so
`s ∈ J⁻(y)`); the open sets `I⁺(w)` cover `S`, finitely many suffice, and `J⁺(S)` lies in the
closed set `⋃ᵢ J⁺(wᵢ)`, which does not contain `y`.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Every point is a limit of points of its chronological past.** -/
theorem mem_closure_chronPast [BoundarylessManifold I M] (x : M) : x ∈ closure (chronPast T x) := by
  rw [mem_closure_iff_nhds]
  intro V hV
  obtain ⟨q, hqV, hq⟩ := exists_mem_chronFuture_near T.neg x hV
  exact ⟨q, hqV, (chronFuture_neg_iff T).1 hq⟩

/-- **Past reflection in a causally simple spacetime**: if `y ∈ J⁺(w)` for every `w ≪ x`, then
`y ∈ J⁺(x)`. -/
theorem mem_causalFuture_of_forall_chronPast [BoundarylessManifold I M]
    (hclosed : ∀ y : M, IsClosed (causalPast T y)) {x y : M}
    (h : ∀ w ∈ chronPast T x, y ∈ causalFuture T w) : y ∈ causalFuture T x := by
  have hsub : chronPast T x ⊆ causalPast T y := fun w hw => h w hw
  have := closure_minimal hsub (hclosed y) (mem_closure_chronPast T x)
  exact this

/-- **The causal future of a compact set is closed in a globally hyperbolic spacetime.** -/
theorem isClosed_causalFutureSet [BoundarylessManifold I M] [T2Space M]
    (hGH : IsGloballyHyperbolic T) {S : Set M} (hS : IsCompact S) :
    IsClosed (causalFutureSet T S) := by
  have hcs := isCausallySimple_of_isGloballyHyperbolic_boundaryless T hGH
  refine closure_subset_iff_isClosed.1 fun y hy => ?_
  by_contra hyS
  have key : ∀ s ∈ S, ∃ w, w ∈ chronPast T s ∧ y ∉ causalFuture T w := by
    intro s hs
    by_contra hcon
    push_neg at hcon
    exact hyS (mem_iUnion₂.2 ⟨s, hs, mem_causalFuture_of_forall_chronPast T
      (fun y' => (hcs.2 y').2) hcon⟩)
  choose! w hwp hwy using key
  have hcover : S ⊆ ⋃ s ∈ S, chronFuture T (w s) := fun s hs =>
    mem_iUnion₂.2 ⟨s, hs, hwp s hs⟩
  obtain ⟨b, hbS, hbfin, hbcov⟩ := hS.elim_finite_subcover_image
    (fun s _ => isOpen_chronFuture_of_reach T (w s)) hcover
  have hF : IsClosed (⋃ s ∈ b, causalFuture T (w s)) :=
    hbfin.isClosed_biUnion fun s _ => (hcs.2 (w s)).1
  have hsubF : causalFutureSet T S ⊆ ⋃ s ∈ b, causalFuture T (w s) := by
    intro z hz
    obtain ⟨s', hs', hzs'⟩ := mem_iUnion₂.1 hz
    obtain ⟨s, hsb, hs's⟩ := mem_iUnion₂.1 (hbcov hs')
    exact mem_iUnion₂.2 ⟨s, hsb, chron_subset_causal T (w s)
      (chronFuture_causalFuture_trans_of_isOpen T (isOpen_chronFuture_of_reach T) hs's hzs')⟩
  have hyF := closure_minimal hsubF hF hy
  obtain ⟨s, hsb, hys⟩ := mem_iUnion₂.1 hyF
  exact hwy s (hbS hsb) hys

end Lightlike.Causal
