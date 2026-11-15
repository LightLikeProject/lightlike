import Lightlike.PL.Slicing
import Lightlike.PL.Carrier

/-!
# Cells cut out of a geometric complex by affine functionals

Given a geometric complex `K` and finitely many real functions `H i` on the ambient space (the
affine functionals that slice it), a **cell** is a pair `(σ, s)` of a face `σ` of `K` and a sign
pattern `s`, standing for the part of the open simplex of `σ` on which each `H i` has the sign
`s i`. The cells that are nonempty, ordered by "lies in the closure of", form a poset whose order
complex is the slicing of `K` by `H` (Lickorish, proof of Theorem 4.5). This file defines the poset
and its order complex; for no functionals it is the first derived subdivision.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E] {ι : Type*}

/-- Index of a cell: a face together with a sign pattern. -/
def CellIdx (E : Type*) (ι : Type*) := Finset E × (ι → SignType)

noncomputable instance : DecidableEq (CellIdx E ι) := Classical.decEq _

/-- The closure order on cell indices: `(σ', s') ≤ (σ, s)` when `σ' ⊆ σ` and every sign of `s'` is
zero or agrees with the sign of `s`. -/
instance : PartialOrder (CellIdx E ι) where
  le a b := a.1 ⊆ b.1 ∧ ∀ i, a.2 i = 0 ∨ a.2 i = b.2 i
  le_refl a := ⟨subset_rfl, fun i => .inr rfl⟩
  le_trans a b c h₁ h₂ := ⟨h₁.1.trans h₂.1, fun i => by
    rcases h₁.2 i with h | h
    · exact .inl h
    · rcases h₂.2 i with h' | h'
      · exact .inl (h.trans h')
      · exact .inr (h.trans h')⟩
  le_antisymm a b h₁ h₂ := by
    refine Prod.ext (Finset.Subset.antisymm h₁.1 h₂.1) (funext fun i => ?_)
    rcases h₁.2 i with h | h <;> rcases h₂.2 i with h' | h'
    · exact h.trans h'.symm
    · exact h'.symm
    · exact h
    · exact h

omit [AddCommGroup E] [Module ℝ E] [DecidableEq E] in
lemma cellIdx_le {a b : CellIdx E ι} :
    a ≤ b ↔ a.1 ⊆ b.1 ∧ ∀ i, a.2 i = 0 ∨ a.2 i = b.2 i := Iff.rfl

/-- The set of points of the cell `(σ, s)`: the open simplex of `σ` on which each `H i` has the sign
`s i`. -/
def cellSet (H : ι → E → ℝ) (c : CellIdx E ι) : Set E :=
  openHull c.1 ∩ {x | ∀ i, SignType.sign (H i x) = c.2 i}

/-- The cell indices of `K` and `H` whose cell is nonempty: the elements of the poset `P(K, H)`. -/
noncomputable def cells [Fintype ι] [DecidableEq ι] (K : SComplex E) (H : ι → E → ℝ) :
    Finset (CellIdx E ι) := by
  classical
  exact (K.faces ×ˢ (Finset.univ : Finset (ι → SignType))).filter fun c => (cellSet H c).Nonempty

lemma mem_cells [Fintype ι] [DecidableEq ι] {K : SComplex E} {H : ι → E → ℝ} {c : CellIdx E ι} :
    c ∈ cells K H ↔ c.1 ∈ K ∧ (cellSet H c).Nonempty := by
  classical
  unfold cells
  refine Finset.mem_filter.trans ?_
  refine and_congr_left fun _ => ?_
  exact (Finset.mem_product (s := K.faces) (t := (Finset.univ : Finset (ι → SignType)))
    (p := c)).trans (by simp [mem_faces])

/-- The **slicing** of `K` by `H`: the order complex of the poset of nonempty cells. -/
noncomputable def sliceComplex [Fintype ι] [DecidableEq ι] (K : SComplex E) (H : ι → E → ℝ) :
    SComplex (CellIdx E ι) := orderComplex (cells K H)

/-! ## No functionals: the derived subdivision -/

omit [DecidableEq E] in
/-- The open simplex of a nonempty finite set is nonempty (it contains the centroid). -/
lemma openHull_nonempty {σ : Finset E} (h : σ.Nonempty) : (openHull σ).Nonempty := by
  refine ⟨∑ y ∈ σ, (1 / (#σ : ℝ)) • y, fun _ => 1 / (#σ : ℝ), fun y _ => ?_, ?_, rfl⟩
  · have : (0 : ℝ) < #σ := by exact_mod_cast h.card_pos
    positivity
  · have : (#σ : ℝ) ≠ 0 := by exact_mod_cast h.card_pos.ne'
    simp [this]

/-- With no functionals the cell indices are the faces. -/
def cellEmb (ι : Type*) [IsEmpty ι] : Finset E ↪ CellIdx E ι where
  toFun σ := (σ, isEmptyElim)
  inj' a b h := congrArg Prod.fst h

lemma cellEmb_le [IsEmpty ι] (a b : Finset E) : cellEmb ι a ≤ cellEmb ι b ↔ a ≤ b :=
  ⟨fun h => h.1, fun h => ⟨h, fun i => isEmptyElim i⟩⟩

/-- With no functionals, the nonempty cells are the nonempty faces. -/
lemma cells_isEmpty [Fintype ι] [DecidableEq ι] [IsEmpty ι] (K : SComplex E) (H : ι → E → ℝ) :
    cells K H = (K.faces.erase ∅).map (cellEmb ι) := by
  ext c
  have hs : c.2 = isEmptyElim := funext fun i => isEmptyElim i
  obtain ⟨σ, s⟩ := c
  change s = _ at hs
  subst hs
  refine mem_cells.trans (Iff.trans ?_ Finset.mem_map.symm)
  constructor
  · rintro ⟨hσ, hne⟩
    refine ⟨σ, Finset.mem_erase.2 ⟨?_, mem_faces.2 hσ⟩, rfl⟩
    rintro rfl
    obtain ⟨x, hx, -⟩ := hne
    simp at hx
  · rintro ⟨τ, hτ', he⟩
    obtain ⟨hτ, hτK⟩ := Finset.mem_erase.1 hτ'
    rw [mem_faces] at hτK
    have : τ = σ := congrArg Prod.fst he
    subst this
    refine ⟨hτK, ?_⟩
    obtain ⟨x, hx⟩ := openHull_nonempty (nonempty_iff_ne_empty.2 hτ)
    exact ⟨x, hx, fun i => isEmptyElim i⟩

/-- **With no functionals the slicing is the derived subdivision**, up to renaming the vertices. -/
theorem sliceComplex_isEmpty [Fintype ι] [DecidableEq ι] [IsEmpty ι] (K : SComplex E)
    (H : ι → E → ℝ) : sliceComplex K H = (sd K).map (cellEmb ι) := by
  rw [sliceComplex, cells_isEmpty, orderComplex_map _ (cellEmb_le)]
  rfl

/-- With no functionals the slicing of `K` is stellar equivalent to `K`. -/
theorem stellarEquivIn_slice_isEmpty [Fintype ι] [DecidableEq ι] [IsEmpty ι] (K : SComplex E)
    (h0 : ∅ ∈ K) (H : ι → E → ℝ) :
    StellarEquivIn (K.map (Function.Embedding.inl : E ↪ E ⊕ CellIdx E ι))
      ((sliceComplex K H).map (Function.Embedding.inr : CellIdx E ι ↪ E ⊕ CellIdx E ι)) := by
  have h := (stellarEquivIn_sd K h0).map (Function.Embedding.sumMap (Function.Embedding.refl E)
    (cellEmb ι))
  rw [map_map, map_map, sliceComplex_isEmpty, map_map] at *
  convert h using 2 <;> (try ext) <;> rfl

end SComplex
end Lightlike.PL
