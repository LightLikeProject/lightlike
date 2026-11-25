import Mathlib

/-!
# The topological end of Penrose's argument (G1-012)

In the proof of Penrose's singularity theorem (Senovilla–Garfinkle 2015, proof of Theorem 2; Hawking–Ellis
1973, section 8.2), null completeness makes the achronal boundary `∂J⁺(S)` of a closed trapped surface
compact, the flow of a timelike vector field projects it injectively and continuously into the Cauchy
surface `Σ`, the projection is open by invariance of domain, and so its image is a compact, open, non-empty
subset of the connected `Σ`: `Σ` would be compact.

`compactSpace_of_open_range`, `not_open_range_of_noncompact`: this last step, for any connected
Hausdorff space.
-/

namespace Lightlike.Penrose

/-- **The last step of Penrose's argument.** If a connected Hausdorff space `Σ` receives a continuous map
from a non-empty compact space `K` with open range, then `Σ` is compact. -/
theorem compactSpace_of_open_range {S K : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    [TopologicalSpace K] [CompactSpace K] [Nonempty K] (f : K → S) (hf : Continuous f)
    (hopen : IsOpen (Set.range f)) : CompactSpace S := by
  have hclosed : IsClosed (Set.range f) := (isCompact_range hf).isClosed
  have hclopen : IsClopen (Set.range f) := ⟨hclosed, hopen⟩
  have hne : (Set.range f).Nonempty := Set.range_nonempty f
  have huniv : Set.range f = Set.univ := hclopen.eq_univ hne
  exact ⟨by rw [← huniv]; exact isCompact_range hf⟩

/-- Contrapositive form: a non-compact connected Hausdorff space is not the open continuous image of a
compact non-empty space. -/
theorem not_open_range_of_noncompact {S K : Type*} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] [NoncompactSpace S] [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (f : K → S) (hf : Continuous f) : ¬ IsOpen (Set.range f) := fun h => by
  have := compactSpace_of_open_range f hf h
  exact not_compactSpace_iff.mpr ‹NoncompactSpace S› this

end Lightlike.Penrose
