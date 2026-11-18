import Lightlike.Spacetime.Causal.OpenPast
import Lightlike.Spacetime.Causal.CauchyCover
import Lightlike.Spacetime.Causal.Extension
import Lightlike.Spacetime.Causal.Relations

/-!
# A Cauchy surface is closed

Let `S` be a Cauchy surface. A point `q` of the closure of `S` not in `S` lies on an inextendible
timelike curve `G`, which meets `S` at a point `r` before or after `q`. If `r` is after `q` then `q`
is in the chronological past of `r`, an open set, which therefore contains a point of `S`; if `r`
is before `q` then `q` is in the chronological future of `r`, which is open (`isOpen_chronFuture_of_reach`),
so again it contains a point of `S`. Two points of `S` joined by a timelike curve contradict
achronality (`IsCauchySurface.isAchronal_of_boundaryless`).

The openness of the chronological past is `isOpen_chronPast` (time reversal of
`isOpen_chronFuture_of_reach`); the first lemma takes it as a hypothesis.

## References

* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973), Chapter 6.

The comparison of the statements with the book at its location is pending.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [SecondCountableTopology M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **A Cauchy surface is closed**, given that chronological pasts are open. -/
theorem IsCauchySurface.isClosed_of_isOpen_chronPast {S : Set M} (h : IsCauchySurface T S)
    (hPast : ∀ x : M, IsOpen (chronPast T x)) : IsClosed S := by
  have hA : IsAchronal T S := h.isAchronal_of_boundaryless T
  refine closure_subset_iff_isClosed.1 fun q hq => ?_
  by_contra hqS
  obtain ⟨G, s, t₀, hG, ht₀, hGq⟩ := exists_inextendible_through T q
  obtain ⟨t, ⟨hts, htS⟩, -⟩ := h G s hG
  have hsub : ∀ u v, u ∈ s → v ∈ s → u < v → G v ∈ chronFuture T (G u) := fun u v hu hv huv =>
    ⟨G, u, v, huv, hG.1.restrict T (fun r hr => hG.1.1.ordConnected.out hu hv hr) huv, rfl, rfl⟩
  rcases lt_trichotomy t t₀ with hlt | heq | hgt
  · -- `q ∈ I⁺(G t)`, open
    have hq' : q ∈ chronFuture T (G t) := hGq ▸ hsub t t₀ hts ht₀ hlt
    obtain ⟨s', hs'F, hs'S⟩ := mem_closure_iff.1 hq _ (isOpen_chronFuture_of_reach T (G t)) hq'
    exact hA _ htS _ hs'S hs'F
  · exact hqS (by rw [← hGq, ← heq]; exact htS)
  · -- `q ∈ I⁻(G t)`, open
    have hq' : q ∈ chronPast T (G t) := hGq ▸ hsub t₀ t ht₀ hts hgt
    obtain ⟨s', hs'P, hs'S⟩ := mem_closure_iff.1 hq _ (hPast (G t)) hq'
    exact hA _ hs'S _ htS hs'P

/-- **A Cauchy surface is closed** (on a Hausdorff, second countable manifold without boundary):
the chronological past is open by time reversal of `isOpen_chronFuture_of_reach`. -/
theorem IsCauchySurface.isClosed {S : Set M} (h : IsCauchySurface T S) : IsClosed S :=
  h.isClosed_of_isOpen_chronPast T (isOpen_chronPast T)

end Causal

end Lightlike
