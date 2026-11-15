import Lightlike.PL.SliceGeom

/-!
# The derived boundary of a cell, realised geometrically

For a cell `C` of a `CellStructure`, the cells strictly below `C` form the **derived boundary**
`orderComplex (cells.filter (· < C))`. Sending each cell to its chosen point realises it as the
geometric complex `chainsBelow C`, whose underlying set is the closed part of `C` without its open
part, provided every point there lies in a smaller cell and rays leave cells through smaller
cells.

## Main results

* `CellStructure.chainsBelow`: the geometric realisation of the derived boundary of a cell.
* `CellStructure.isGeom_chainsBelow`: it is a geometric complex.
* `CellStructure.space_chainsBelow`: its underlying set is the closed part of `C` minus the open
  part.
* `SComplex.space_chainsBelow_slice`: the same for the cells of a slicing, with no hypothesis.
-/

open Finset
open scoped Classical

namespace Lightlike.PL

namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A subcomplex of a geometric complex is geometric. -/
lemma IsGeom.of_subcomplex {K L : SComplex E} (hK : IsGeom K) (h : ∀ s ∈ L, s ∈ K) : IsGeom L where
  indep s hs := hK.indep s (h s hs)
  inter s hs t ht := hK.inter s (h s hs) t (h t ht)

end SComplex

namespace CellStructure

variable {E α : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder α] (S : CellStructure E α)

/-- The **derived boundary of the cell `C`, realised**: the chains of cells strictly below `C`,
with each cell replaced by its chosen point. -/
noncomputable def chainsBelow (C : α) : SComplex E :=
  (SComplex.orderComplex (S.cells.filter (· < C))).image S.pt

lemma mem_chainsBelow {C : α} {s : Finset E} :
    s ∈ S.chainsBelow C ↔
      ∃ D, D ⊆ S.cells.filter (· < C) ∧ IsChain (· ≤ ·) (↑D : Set α) ∧ D.image S.pt = s := by
  unfold chainsBelow
  rw [SComplex.mem_image]
  constructor
  · rintro ⟨D, hD, rfl⟩
    rw [SComplex.mem_orderComplex] at hD
    exact ⟨D, hD.1, fun a ha b hb _ => hD.2 a ha b hb, rfl⟩
  · rintro ⟨D, hD, hch, rfl⟩
    refine ⟨D, SComplex.mem_orderComplex.2 ⟨hD, fun a ha b hb => ?_⟩, rfl⟩
    rcases eq_or_ne a b with rfl | hab
    · exact Or.inl le_rfl
    · exact hch ha hb hab

/-- The derived boundary of a cell has the empty face. -/
lemma empty_mem_chainsBelow (C : α) : (∅ : Finset E) ∈ S.chainsBelow C :=
  S.mem_chainsBelow.2 ⟨∅, by simp, by simp, by simp⟩

/-- The realised derived boundary is a subcomplex of the chain complex. -/
lemma chainsBelow_sub {C : α} {s : Finset E} (hs : s ∈ S.chainsBelow C) : s ∈ S.chainComplex := by
  obtain ⟨D, hD, hch, rfl⟩ := S.mem_chainsBelow.1 hs
  exact S.mem_chainComplex.2 ⟨D, ⟨hD.trans (filter_subset _ _), hch⟩, rfl⟩

/-- **The realised derived boundary is a geometric complex.** -/
theorem isGeom_chainsBelow (C : α) : SComplex.IsGeom (S.chainsBelow C) :=
  S.isGeom_chainComplex.of_subcomplex fun _ hs => S.chainsBelow_sub hs

/-- The underlying set of the realised derived boundary lies in the closed part of `C` and misses
its open part. -/
theorem space_chainsBelow_subset {C : α} (hC : C ∈ S.cells) :
    (S.chainsBelow C).space ⊆ S.hull C \ S.cell C := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := SComplex.mem_space.1 hx
  obtain ⟨D, hD, hch, rfl⟩ := S.mem_chainsBelow.1 hs
  rcases D.eq_empty_or_nonempty with rfl | hne
  · simp at hxs
  have hDc : D ⊆ S.cells := hD.trans (filter_subset _ _)
  obtain ⟨m, hmD, hm⟩ := exists_greatest_of_isChain hch hne
  have hmC : m < C := (mem_filter.1 (hD hmD)).2
  have hmcells : m ∈ S.cells := hDc hmD
  have hy := S.convexHull_image_pt_subset hDc hmcells hm hxs
  refine ⟨S.hull_mono C hC m hmcells hmC.le hy, fun hxc => ?_⟩
  exact S.notMem_span C hC m hmcells hmC x hxc (subset_affineSpan ℝ _ hy)

/-- **The underlying set of the realised derived boundary** is the closed part of `C` without its
open part, given that every point there lies in a smaller cell and that rays leave cells through
smaller cells. -/
theorem space_chainsBelow {C : α} (hC : C ∈ S.cells)
    (hcov : ∀ x ∈ S.hull C, x ∉ S.cell C → ∃ b ∈ S.cells, b < C ∧ x ∈ S.cell b)
    (hexit : ∀ a ∈ S.cells, ∀ x ∈ S.cell a, x ≠ S.pt a →
      ∃ t : ℝ, 1 ≤ t ∧ ∃ b ∈ S.cells, b < a ∧ S.pt a + t • (x - S.pt a) ∈ S.cell b) :
    (S.chainsBelow C).space = S.hull C \ S.cell C := by
  refine Set.Subset.antisymm (S.space_chainsBelow_subset hC) fun x ⟨hxh, hxc⟩ => ?_
  obtain ⟨b, hb, hbC, hxb⟩ := hcov x hxh hxc
  obtain ⟨D, hD, hDle, hxD⟩ := S.exists_chain_of_mem_cell hexit _ b hb rfl x hxb
  refine SComplex.mem_space.2 ⟨D.image S.pt, S.mem_chainsBelow.2 ⟨D, ?_, hD.2, rfl⟩, hxD⟩
  intro p hp
  exact mem_filter.2 ⟨hD.1 hp, lt_of_le_of_lt (hDle p hp) hbC⟩

end CellStructure

namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The realised derived boundary of a cell of a slicing**: its underlying set is the closed
part of the cell without its open part. -/
theorem space_chainsBelow_slice (K : SComplex E) (hK : IsGeom K) (H : ι → E →ᵃ[ℝ] ℝ)
    {C : CellIdx E ι} (hC : C ∈ (sliceStructure K hK H).cells) :
    ((sliceStructure K hK H).chainsBelow C).space = sliceHull H C \ cellSet (fun i => ⇑(H i)) C := by
  refine (sliceStructure K hK H).space_chainsBelow hC ?_ (sliceStructure_exit K hK H)
  intro x hx hxc
  obtain ⟨c', hc'C, hc'K, hxc'⟩ := exists_cell_of_mem_sliceHull H (mem_cells.1 hC).1 hx
  have hc' : c' ∈ cells K (fun i => ⇑(H i)) := mem_cells.2 ⟨hc'K, x, hxc'⟩
  refine ⟨c', hc', lt_of_le_of_ne hc'C fun he => hxc (he ▸ hxc'), hxc'⟩

end SComplex
end Lightlike.PL
