import Lightlike.Rows.G1_067.EventHorizon

/-!
# The boundary of the causal future of a set is achronal and closed (G1-012)

Step 3 of Penrose's argument (Hawking–Ellis 1973, Prop. 6.3.1, the achronal boundary): for any set `S`, the topological
boundary `∂J⁺(S)` is achronal (`isAchronal_frontier_causalFutureSet`) and closed (`isClosed_frontier_causalFutureSet`).
This is the future analogue of `Causal.isAchronal_frontier_causalPastSet` (G1-067). That `∂J⁺(S)` is a topological
hypersurface (locally a graph) is **not** proved here.
-/

open Set Bundle Manifold
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

omit [BoundarylessManifold I M] in
/-- A point is in `J⁺(S)` iff some point of `S` is in its causal past. -/
theorem mem_causalFutureSet {S : Set M} {p : M} :
    p ∈ causalFutureSet T S ↔ ∃ s ∈ S, p ∈ causalFuture T s := by
  simp [causalFutureSet]

/-- `I⁺(S)` is open and contained in `J⁺(S)`, so it lies in the interior of `J⁺(S)`. -/
theorem chronFutureSet_subset_interior (S : Set M) :
    chronFutureSet T S ⊆ interior (causalFutureSet T S) := by
  refine interior_maximal ?_ (isOpen_biUnion fun x _ => isOpen_chronFuture_of_reach T x)
  intro p hp
  obtain ⟨s, hs, hps⟩ := mem_iUnion₂.1 hp
  exact (mem_causalFutureSet T).2 ⟨s, hs, chron_subset_causal T s hps⟩

/-- **The boundary of the causal future of a set is achronal** (future form of the achronal boundary property;
the proof is by the second push-up lemma). -/
theorem isAchronal_frontier_causalFutureSet (S : Set M) :
    IsAchronal T (frontier (causalFutureSet T S)) := by
  intro p hp q hq hpq
  obtain ⟨r, hr1, hr2⟩ := mem_closure_iff.1 hp.1 _ (isOpen_chronPast T q) hpq
  obtain ⟨s, hs, hrs⟩ := (mem_causalFutureSet T).1 hr2
  have hqs : q ∈ chronFuture T s :=
    causalFuture_chronFuture_trans_of_isOpen T (isOpen_chronFuture_of_reach T.neg) hrs hr1
  exact hq.2 (chronFutureSet_subset_interior T S (mem_iUnion₂.2 ⟨s, hs, hqs⟩))

omit [BoundarylessManifold I M] in
/-- The boundary of the causal future of a set is closed. -/
theorem isClosed_frontier_causalFutureSet (S : Set M) : IsClosed (frontier (causalFutureSet T S)) :=
  isClosed_frontier

end Lightlike.Causal
