module

public import Lightlike.PonzanoRegge.TriangulationIndependence.Values

/-!
# Triangulation independence, conditional on Pachner's theorem

Pachner's theorem (two triangulations of one closed PL manifold are connected by the four
Pachner moves) needs PL topology that Mathlib lacks, so it enters here as an explicit hypothesis on
an abstract relation `Same` ("the two complexes triangulate the same manifold").

* `CommonForward K K'`: both complexes reach one complex `K''` by 2-3 and 1-4 moves.
* `CommonForward.moveConnected`: a common forward descendant is a move-connection.
* `CommonForward.ampValues_subset`: the regularised values of both complexes lie in those of `K''`.
* `PachnerHyp`: the hypothesis "same manifold implies move-connected"; `PachnerForwardHyp` is the
  form that the forward-simulation argument needs.
* `triangulation_independence_of_pachner`: under `PachnerForwardHyp`, any two complexes with
  `Same` have a common complex realising every regularised value of both.

What is not claimed: that two move-connected complexes have equal sets of values. The inverse moves
(3-2, 4-1) need cut-off inequalities on the new edges, so only the forward direction simulates a
general state; see `Values.lean`.

The unconditional version, with `PachnerForwardHyp` proven (Adiprasito–Pak, arXiv:2404.05930), is
the milestone PL7c; here it stays a hypothesis.
-/

@[expose] public section

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- Two complexes have a **common forward descendant**: both reach one complex by 2-3 and 1-4
moves. -/
def CommonForward (K K' : Complex3 V) : Prop :=
  ∃ K'' : Complex3 V, ForwardMoves K K'' ∧ ForwardMoves K' K''

/-- A common forward descendant is a move-connection. -/
theorem CommonForward.moveConnected {K K' : Complex3 V} (h : CommonForward K K') :
    MoveConnected K K' := by
  obtain ⟨K'', h1, h2⟩ := h
  exact (moveConnected_equivalence.trans h1.moveConnected h2.moveConnected.symm :)

/-- Common forward descendants are symmetric. -/
theorem CommonForward.symm {K K' : Complex3 V} (h : CommonForward K K') : CommonForward K' K := by
  obtain ⟨K'', h1, h2⟩ := h
  exact ⟨K'', h2, h1⟩

/-- Every complex is its own common forward descendant. -/
theorem CommonForward.refl (K : Complex3 V) : CommonForward K K := ⟨K, .refl, .refl⟩

/-- **The regularised values of both complexes occur on a common complex.** -/
theorem CommonForward.ampValues_subset {K K' : Complex3 V} (h : CommonForward K K') :
    ∃ K'' : Complex3 V, ampValues K ⊆ ampValues K'' ∧ ampValues K' ⊆ ampValues K'' := by
  obtain ⟨K'', h1, h2⟩ := h
  exact ⟨K'', ampValues_mono_forward h1, ampValues_mono_forward h2⟩

/-- **Pachner's theorem as a hypothesis**: complexes related by `Same` (triangulating one closed
manifold) are connected by Pachner moves. -/
def PachnerHyp (Same : Complex3 V → Complex3 V → Prop) : Prop :=
  ∀ K K', Same K K' → MoveConnected K K'

/-- The strengthened form that forward simulation uses: `Same` complexes have a common forward
descendant. It implies `PachnerHyp` (`PachnerForwardHyp.pachnerHyp`). -/
def PachnerForwardHyp (Same : Complex3 V → Complex3 V → Prop) : Prop :=
  ∀ K K', Same K K' → CommonForward K K'

/-- The forward form of Pachner's hypothesis gives the plain one. -/
theorem PachnerForwardHyp.pachnerHyp {Same : Complex3 V → Complex3 V → Prop}
    (h : PachnerForwardHyp Same) : PachnerHyp Same :=
  fun K K' hs => (h K K' hs).moveConnected

/-- **Triangulation independence of the regularised amplitude, given Pachner's theorem.** If
`Same K K'` and Pachner's theorem holds in its forward form, then every gauge-fixed amplitude of `K`
and every one of `K'` is a gauge-fixed amplitude, at some maximal tree and cut-off, of one common
complex `K''`. The cut-off is a regulator, so this is the form in which independence holds before
the cut-off is removed. The hypothesis is removed by the milestone PL7c. -/
theorem triangulation_independence_of_pachner {Same : Complex3 V → Complex3 V → Prop}
    (hP : PachnerForwardHyp Same) {K K' : Complex3 V} (hs : Same K K') :
    ∃ K'' : Complex3 V, ampValues K ⊆ ampValues K'' ∧ ampValues K' ⊆ ampValues K'' :=
  (hP K K' hs).ampValues_subset

end Lightlike.PR
