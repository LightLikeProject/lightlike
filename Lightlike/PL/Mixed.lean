import Lightlike.PL.Convex

/-!
# The mixed poset of cells

When a functional `h` is adjoined to a family `H`, the cells of the extended family refine those
of `H`. The cells can be split one at a time, lower ones first. The intermediate stages live in one
poset `Mixed E ι` whose elements are old cells (not yet split) or new cells (already split), with
a new cell below an old one when its restriction to the old signs is.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} {ι : Type*}

/-- An element of the mixed poset: a cell of the old family or one of the extended family. -/
inductive Mixed (E : Type*) (ι : Type*)
  | old : CellIdx E ι → Mixed E ι
  | new : CellIdx E (ι ⊕ Unit) → Mixed E ι

noncomputable instance : DecidableEq (Mixed E ι) := Classical.decEq _

/-- Forget the sign of the new functional. -/
def CellIdx.restr (b : CellIdx E (ι ⊕ Unit)) : CellIdx E ι := (b.1, fun i => b.2 (Sum.inl i))

lemma CellIdx.restr_mono {a b : CellIdx E (ι ⊕ Unit)} (h : a ≤ b) : a.restr ≤ b.restr :=
  ⟨h.1, fun i => h.2 (Sum.inl i)⟩

/-- The order of the mixed poset: old cells and new cells each carry their closure order, and a new
cell lies below an old cell when its restriction does. An old cell is never below a new one. -/
def Mixed.Le : Mixed E ι → Mixed E ι → Prop
  | .old a, .old b => a ≤ b
  | .new a, .new b => a ≤ b
  | .new a, .old b => a.restr ≤ b
  | .old _, .new _ => False

instance : PartialOrder (Mixed E ι) where
  le := Mixed.Le
  le_refl x := by
    cases x with
    | old a => exact le_refl a
    | new a => exact le_refl a
  le_trans x y z h₁ h₂ := by
    cases x with
    | old a =>
      cases y with
      | old b =>
        cases z with
        | old c => exact le_trans (α := CellIdx E ι) h₁ h₂
        | new c => exact h₂.elim
      | new b => exact h₁.elim
    | new a =>
      cases y with
      | old b =>
        cases z with
        | old c => exact le_trans (α := CellIdx E ι) h₁ h₂
        | new c => exact h₂.elim
      | new b =>
        cases z with
        | old c => exact le_trans (α := CellIdx E ι) (CellIdx.restr_mono (a := a) (b := b) h₁) h₂
        | new c => exact le_trans (α := CellIdx E (ι ⊕ Unit)) h₁ h₂
  le_antisymm x y h₁ h₂ := by
    cases x with
    | old a =>
      cases y with
      | old b => exact congrArg Mixed.old (le_antisymm (α := CellIdx E ι) h₁ h₂)
      | new b => exact h₁.elim
    | new a =>
      cases y with
      | old b => exact h₂.elim
      | new b => exact congrArg Mixed.new (le_antisymm (α := CellIdx E (ι ⊕ Unit)) h₁ h₂)

lemma Mixed.old_le_old {a b : CellIdx E ι} : Mixed.old a ≤ Mixed.old b ↔ a ≤ b := Iff.rfl

lemma Mixed.new_le_new {a b : CellIdx E (ι ⊕ Unit)} : Mixed.new a ≤ Mixed.new b ↔ a ≤ b := Iff.rfl

lemma Mixed.new_le_old {a : CellIdx E (ι ⊕ Unit)} {b : CellIdx E ι} :
    Mixed.new a ≤ Mixed.old b ↔ a.restr ≤ b := Iff.rfl

lemma Mixed.not_old_le_new {a : CellIdx E ι} {b : CellIdx E (ι ⊕ Unit)} :
    ¬ Mixed.old a ≤ Mixed.new b := fun h => h

/-- Old cells as elements of the mixed poset. -/
def Mixed.oldEmb : CellIdx E ι ↪ Mixed E ι where
  toFun := Mixed.old
  inj' _ _ h := Mixed.old.inj h

/-- New cells as elements of the mixed poset. -/
def Mixed.newEmb : CellIdx E (ι ⊕ Unit) ↪ Mixed E ι where
  toFun := Mixed.new
  inj' _ _ h := Mixed.new.inj h

lemma Mixed.oldEmb_le (a b : CellIdx E ι) : Mixed.oldEmb a ≤ Mixed.oldEmb b ↔ a ≤ b := Iff.rfl

lemma Mixed.newEmb_le (a b : CellIdx E (ι ⊕ Unit)) : Mixed.newEmb a ≤ Mixed.newEmb b ↔ a ≤ b :=
  Iff.rfl

section Stages

variable [AddCommGroup E] [Module ℝ E] [DecidableEq E] [Fintype ι] [DecidableEq ι]

open Classical in
/-- The cells of the mixed poset after the old cells in `D` have been split: the unsplit old cells
outside `D`, and the new cells over `D`. -/
noncomputable def mixedCells (K : SComplex E) (H : ι → E →ᵃ[ℝ] ℝ) (h : E →ᵃ[ℝ] ℝ)
    (D : Finset (CellIdx E ι)) : Finset (Mixed E ι) :=
  ((cells K (fun i => ⇑(H i))).filter (· ∉ D)).map Mixed.oldEmb ∪
    ((cells K (extH H h)).filter (fun b => b.restr ∈ D)).map Mixed.newEmb

omit [DecidableEq E] in
/-- Before any cell is split the mixed poset is the poset of old cells. -/
lemma mixedCells_empty (K : SComplex E) (H : ι → E →ᵃ[ℝ] ℝ) (h : E →ᵃ[ℝ] ℝ) :
    mixedCells K H h ∅ = (cells K (fun i => ⇑(H i))).map Mixed.oldEmb := by
  classical
  simp [mixedCells]

omit [AddCommGroup E] [Module ℝ E] [DecidableEq E] [Fintype ι] [DecidableEq ι] in
/-- A cell index of the extended family is the extension of its restriction. -/
lemma CellIdx.eq_mk_restr (b : CellIdx E (ι ⊕ Unit)) :
    b = mkCell b.restr.1 (extSign b.restr.2 (b.2 (Sum.inr ()))) := by
  refine Prod.ext rfl (funext fun i => ?_)
  rcases i with i | ⟨⟩ <;> rfl

/-- After all cells are split the mixed poset is the poset of cells of the extended family. -/
lemma mixedCells_univ (K : SComplex E) (H : ι → E →ᵃ[ℝ] ℝ) (h : E →ᵃ[ℝ] ℝ) :
    mixedCells K H h (cells K (fun i => ⇑(H i))) = (cells K (extH H h)).map Mixed.newEmb := by
  classical
  ext x
  simp only [mixedCells, Finset.mem_union, Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro (⟨a, ⟨ha, hn⟩, rfl⟩ | ⟨b, ⟨hb, -⟩, rfl⟩)
    · exact absurd ha hn
    · exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    refine .inr ⟨b, ⟨hb, ?_⟩, rfl⟩
    have := CellIdx.eq_mk_restr b
    rw [this] at hb
    exact restrict_mem_cells hb

omit [DecidableEq E] in
/-- At the first stage the order complex of the mixed poset is the slicing by `H`. -/
lemma orderComplex_mixedCells_empty (K : SComplex E) (H : ι → E →ᵃ[ℝ] ℝ) (h : E →ᵃ[ℝ] ℝ) :
    orderComplex (mixedCells K H h ∅) = (sliceComplex K (fun i => ⇑(H i))).map Mixed.oldEmb := by
  rw [mixedCells_empty, sliceComplex, orderComplex_map _ Mixed.oldEmb_le]

/-- At the last stage the order complex of the mixed poset is the slicing by the extended family. -/
lemma orderComplex_mixedCells_univ (K : SComplex E) (H : ι → E →ᵃ[ℝ] ℝ) (h : E →ᵃ[ℝ] ℝ) :
    orderComplex (mixedCells K H h (cells K (fun i => ⇑(H i)))) =
      (sliceComplex K (extH H h)).map Mixed.newEmb := by
  rw [mixedCells_univ, sliceComplex, orderComplex_map _ Mixed.newEmb_le]

end Stages

end SComplex
end Lightlike.PL
