import Lightlike.Spacetime.Causal.CauchySeparation
import Lightlike.Spacetime.Causal.OpenPast
import Lightlike.Spacetime.CausalLadder.LocalLift

/-!
# The event horizon as the boundary of the causal past of future null infinity

The area theorem (Hawking 1971) is a statement about the event horizon of a black hole. In the
weak form of Hawking–Ellis (`hawking-ellis-1973`; no section number is claimed here) the black hole region is `M \ J⁻(𝓘⁺)` and the event horizon is
its boundary `∂J⁻(𝓘⁺)`, where `𝓘⁺` is future null infinity. Future null infinity lives in a conformal
completion, not in the physical spacetime. Here the completion is taken as given: an ambient
time-oriented Lorentzian manifold `M` (without boundary), a set `Scri ⊆ M` playing the part of `𝓘⁺`
(any set; no property of it is assumed), and an open set `U ⊆ M`, the physical spacetime. The causal
past is computed in the ambient manifold, where the curves reaching `𝓘⁺` live.

## Main definitions

* `Causal.causalPastSet T S`: `J⁻(S) = ⋃ x ∈ S, J⁻(x)`.
* `Causal.blackHoleRegion T Scri U`: `U \ J⁻(Scri)`.
* `Causal.eventHorizon T Scri U`: `U ∩ ∂J⁻(Scri)`.

## Main results

* `Causal.compl_causalPastSet_future`: the black hole region is closed under the causal future:
  nothing returns from it.
* `Causal.chronPastSet_subset_interior`: `I⁻(S)` lies in the interior of `J⁻(S)`.
* `Causal.isAchronal_frontier_causalPastSet`, `Causal.eventHorizon_isAchronal`: the boundary of the
  causal past of any set, hence the event horizon, is achronal.

The existence of `𝓘⁺` (asymptotic flatness) is not part of this file; a model horizon may replace it.

## References

* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973) (`hawking-ellis-1973`), chapters on causal structure and on black holes; statements
  here are checked by the Lean proofs, not against a numbered proposition.
-/

open Set Bundle Manifold
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- The **causal past of a set**, `J⁻(S) = ⋃ x ∈ S, J⁻(x)`. -/
def causalPastSet (S : Set M) : Set M := ⋃ x ∈ S, causalPast T x

/-- The **black hole region** `U \ J⁻(𝓘⁺)` of the physical region `U`, for a set `Scri` standing for
future null infinity in an ambient manifold. -/
def blackHoleRegion (Scri U : Set M) : Set M := U \ causalPastSet T Scri

/-- The **event horizon** `U ∩ ∂J⁻(𝓘⁺)`: the boundary in the ambient manifold of the causal past of
`Scri`, inside the physical region `U`. -/
def eventHorizon (Scri U : Set M) : Set M := U ∩ frontier (causalPastSet T Scri)

/-- A point is in `J⁻(S)` iff some point of `S` is in its causal future. -/
theorem mem_causalPastSet {S : Set M} {p : M} :
    p ∈ causalPastSet T S ↔ ∃ s ∈ S, s ∈ causalFuture T p := by
  simp [causalPastSet, causalPast]

/-- `J⁻` is monotone in the set. -/
theorem causalPastSet_mono {S S' : Set M} (h : S ⊆ S') : causalPastSet T S ⊆ causalPastSet T S' := by
  intro p hp
  obtain ⟨s, hs, hps⟩ := (mem_causalPastSet T).1 hp
  exact (mem_causalPastSet T).2 ⟨s, h hs, hps⟩

/-- `J⁻(S)` is closed under the causal past. -/
theorem causalPastSet_causalPast {S : Set M} {p q : M} (hp : p ∈ causalPastSet T S)
    (hqp : q ∈ causalPast T p) : q ∈ causalPastSet T S := by
  obtain ⟨s, hs, hps⟩ := (mem_causalPastSet T).1 hp
  exact (mem_causalPastSet T).2 ⟨s, hs, causal_trans T hqp hps⟩

/-- **Nothing returns from the black hole region**: if `p ∉ J⁻(𝓘⁺)` then no point of the causal
future of `p` is in `J⁻(𝓘⁺)`. -/
theorem compl_causalPastSet_future {S : Set M} {p q : M} (hp : p ∉ causalPastSet T S)
    (hpq : q ∈ causalFuture T p) : q ∉ causalPastSet T S :=
  fun hq => hp (causalPastSet_causalPast T hq hpq)

/-- The black hole region is closed under the causal future, inside a causally convex `U`; in
particular for `U = univ`. -/
theorem blackHoleRegion_future {S U : Set M} {p q : M} (hp : p ∈ blackHoleRegion T S U)
    (hq : q ∈ U) (hpq : q ∈ causalFuture T p) : q ∈ blackHoleRegion T S U :=
  ⟨hq, compl_causalPastSet_future T hp.2 hpq⟩

/-- With no future infinity the whole physical region is a black hole region and there is no
horizon. -/
theorem blackHoleRegion_empty (U : Set M) : blackHoleRegion T (∅ : Set M) U = U := by
  simp [blackHoleRegion, causalPastSet]

/-- With no future infinity there is no event horizon. -/
theorem eventHorizon_empty (U : Set M) : eventHorizon T (∅ : Set M) U = ∅ := by
  simp [eventHorizon, causalPastSet]

/-- If every point of the physical region is in `Scri`, there is no black hole region. -/
theorem blackHoleRegion_eq_empty_of_subset {S U : Set M} (h : U ⊆ S) :
    blackHoleRegion T S U = ∅ := by
  refine eq_empty_of_forall_notMem fun p hp => hp.2 ((mem_causalPastSet T).2 ⟨p, h hp.1, ?_⟩)
  exact self_mem_causalFuture T p

/-- The event horizon lies in the closure of the black hole region of the ambient manifold. -/
theorem eventHorizon_subset_closure (S : Set M) {U : Set M} :
    eventHorizon T S U ⊆ U ∩ closure (blackHoleRegion T S univ) := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  have h2 : p ∈ closure (causalPastSet T S) ∩ closure (causalPastSet T S)ᶜ := by
    rw [← frontier_eq_closure_inter_closure]; exact hp.2
  have h3 := h2.2
  rwa [compl_eq_univ_sdiff] at h3

section Boundaryless

variable [BoundarylessManifold I M]

/-- `I⁻(S)` is open and contained in `J⁻(S)`, so it lies in the interior of `J⁻(S)`. -/
theorem chronPastSet_subset_interior (S : Set M) :
    chronPastSet T S ⊆ interior (causalPastSet T S) := by
  refine interior_maximal ?_ (isOpen_biUnion fun x _ => isOpen_chronPast T x)
  intro p hp
  obtain ⟨s, hs, hps⟩ := mem_iUnion₂.1 hp
  exact (mem_causalPastSet T).2 ⟨s, hs, chron_subset_causal T p hps⟩

/-- **The boundary of the causal past of a set is achronal** (a standard fact of
causality theory; the proof is by the push-up lemma). -/
theorem isAchronal_frontier_causalPastSet (S : Set M) :
    IsAchronal T (frontier (causalPastSet T S)) := by
  intro p hp q hq hpq
  obtain ⟨r, hr1, hr2⟩ := mem_closure_iff.1 hq.1 _ (isOpen_chronFuture_of_reach T p) hpq
  obtain ⟨s, hs, hrs⟩ := (mem_causalPastSet T).1 hr2
  have hps : s ∈ chronFuture T p :=
    chronFuture_causalFuture_trans_of_isOpen T (isOpen_chronFuture_of_reach T) hr1 hrs
  have hpI : p ∈ chronPastSet T S := mem_iUnion₂.2 ⟨s, hs, hps⟩
  exact hp.2 (chronPastSet_subset_interior T S hpI)

/-- **The event horizon is achronal.** -/
theorem eventHorizon_isAchronal (S U : Set M) : IsAchronal T (eventHorizon T S U) :=
  fun p hp q hq => isAchronal_frontier_causalPastSet T S p hp.2 q hq.2

end Boundaryless

end Lightlike.Causal
