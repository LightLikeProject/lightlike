import Lightlike.PL.SliceGeom
import Lightlike.PL.CommonSub
import Lightlike.PL.Realisation

/-!
# The chain complex of a slicing is a subdivision

The chain complex of the cells of a slicing of a geometric complex `K` by affine functionals is a
geometric subdivision of `K`, and each of its simplices lies in the closed part of one cell, where
each of the functionals has a fixed sign.

## Main results

* `SComplex.exists_sliceHull_of_mem_chainComplex`: a simplex of the chain complex lies in the
  closed part of a cell.
* `SComplex.isSubdivision_slice`: the chain complex of a slicing subdivides `K`.
-/

open Finset
open scoped Classical

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- Every non-empty simplex of the chain complex of a slicing has its hull inside the closed part
of a cell. -/
lemma exists_sliceHull_of_mem_chainComplex (K : SComplex E) (hK : IsGeom K)
    (H : ι → E →ᵃ[ℝ] ℝ) {s : Finset E} (hs : s ∈ (sliceStructure K hK H).chainComplex)
    (hne : s.Nonempty) :
    ∃ c ∈ cells K (fun i => ⇑(H i)), convexHull ℝ (s : Set E) ⊆ sliceHull H c := by
  obtain ⟨C, hC, rfl⟩ := (sliceStructure K hK H).mem_chainComplex.1 hs
  have hCne : C.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨p, hp, -⟩ := Finset.mem_image.1 hx
    exact ⟨p, hp⟩
  obtain ⟨m, hmC, hm⟩ := exists_greatest_of_isChain hC.2 hCne
  exact ⟨m, hC.1 hmC, (sliceStructure K hK H).convexHull_image_pt_subset hC.1 (hC.1 hmC) hm⟩

/-- A cell of a slicing lies in the closed simplex of a simplex of `K`. -/
lemma sliceHull_subset_convexHull (H : ι → E →ᵃ[ℝ] ℝ) (c : CellIdx E ι) :
    sliceHull H c ⊆ convexHull ℝ (c.1 : Set E) := fun _ hx => hx.1

/-- **The chain complex of a slicing subdivides the complex.** -/
theorem isSubdivision_slice (K : SComplex E) (hK : IsGeom K) (h₀ : ∅ ∈ K)
    (H : ι → E →ᵃ[ℝ] ℝ) :
    IsSubdivision (sliceStructure K hK H).chainComplex K where
  geom' := isGeom_slice_chainComplex K hK H
  geom := hK
  space_eq := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hxs⟩ := mem_space.1 hx
      rcases s.eq_empty_or_nonempty with rfl | hne
      · simp at hxs
      obtain ⟨c, hc, hsc⟩ := exists_sliceHull_of_mem_chainComplex K hK H hs hne
      exact mem_space.2 ⟨c.1, (mem_cells.1 hc).1, hsc hxs |>.1⟩
    · intro hx
      obtain ⟨s, hs, hxs⟩ := mem_space.1 hx
      obtain ⟨t, htK, -, hxt⟩ := exists_face_openHull hs hxs
      have hmem : (t, fun i => SignType.sign (H i x)) ∈ cells K (fun i => ⇑(H i)) :=
        mem_cells.2 ⟨htK, x, hxt, fun i => rfl⟩
      obtain ⟨C, hC, -, hxC⟩ := exists_chain_of_mem_sliceCell K hK H hmem ⟨hxt, fun i => rfl⟩
      exact mem_space.2 ⟨_, (sliceStructure K hK H).mem_chainComplex.2 ⟨C, hC, rfl⟩, hxC⟩
  le s hs := by
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, h₀, by simp⟩
    · obtain ⟨c, hc, hsc⟩ := exists_sliceHull_of_mem_chainComplex K hK H hs hne
      exact ⟨c.1, (mem_cells.1 hc).1, hsc.trans (sliceHull_subset_convexHull H c)⟩

end SComplex
end Lightlike.PL
