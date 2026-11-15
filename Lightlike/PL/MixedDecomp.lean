import Lightlike.PL.MixedStep
import Lightlike.PL.OrderSplit

/-!
# The stages of the mixed poset around a split cell

For a cell `A` not yet split, the stage before splitting is the rest of the poset together with the
join of the order complex of the lower neighbours and the old `A` with that of the upper
neighbours; the stage after splitting has the new cells over `A` in place of the old `A`.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {K : SComplex E} {H : ι → E →ᵃ[ℝ] ℝ} {h : E →ᵃ[ℝ] ℝ} {D : Finset (CellIdx E ι)}

open Classical in
/-- The elements of the stage other than the old cell `A`. -/
noncomputable def mixedRest (K : SComplex E) (H : ι → E →ᵃ[ℝ] ℝ) (h : E →ᵃ[ℝ] ℝ)
    (D : Finset (CellIdx E ι)) (A : CellIdx E ι) : Finset (Mixed E ι) :=
  (mixedCells K H h D).erase (Mixed.old A)

open Classical in
/-- The elements of the stage below the old cell `A`. -/
noncomputable def mixedLower (K : SComplex E) (H : ι → E →ᵃ[ℝ] ℝ) (h : E →ᵃ[ℝ] ℝ)
    (D : Finset (CellIdx E ι)) (A : CellIdx E ι) : Finset (Mixed E ι) :=
  (mixedCells K H h D).filter (· < Mixed.old A)

open Classical in
/-- The elements of the stage above the old cell `A`. -/
noncomputable def mixedUpper (K : SComplex E) (H : ι → E →ᵃ[ℝ] ℝ) (h : E →ᵃ[ℝ] ℝ)
    (D : Finset (CellIdx E ι)) (A : CellIdx E ι) : Finset (Mixed E ι) :=
  (mixedCells K H h D).filter (Mixed.old A < ·)

open Classical in
/-- The new cells over `A`. -/
noncomputable def mixedNew (K : SComplex E) (H : ι → E →ᵃ[ℝ] ℝ) (h : E →ᵃ[ℝ] ℝ)
    (A : CellIdx E ι) : Finset (Mixed E ι) :=
  ((cells K (extH H h)).filter (fun b => b.restr = A)).map Mixed.newEmb

lemma mem_mixedRest {A : CellIdx E ι} {x : Mixed E ι} :
    x ∈ mixedRest K H h D A ↔ x ∈ mixedCells K H h D ∧ x ≠ Mixed.old A := by
  classical
  simp [mixedRest, and_comm]

lemma mem_mixedLower {A : CellIdx E ι} {x : Mixed E ι} :
    x ∈ mixedLower K H h D A ↔ x ∈ mixedCells K H h D ∧ x < Mixed.old A := by
  classical
  simp [mixedLower]

lemma mem_mixedUpper {A : CellIdx E ι} {x : Mixed E ι} :
    x ∈ mixedUpper K H h D A ↔ x ∈ mixedCells K H h D ∧ Mixed.old A < x := by
  classical
  simp [mixedUpper]

lemma new_mem_mixedNew {A : CellIdx E ι} {b : CellIdx E (ι ⊕ Unit)} :
    Mixed.new b ∈ mixedNew K H h A ↔ b ∈ cells K (extH H h) ∧ b.restr = A := by
  classical
  simp only [mixedNew, Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro ⟨c, hc, he⟩
    exact (Mixed.new.inj he) ▸ hc
  · intro hb
    exact ⟨b, hb, rfl⟩

lemma old_notMem_mixedNew {A : CellIdx E ι} {x : CellIdx E ι} :
    Mixed.old x ∉ mixedNew K H h A := by
  classical
  simp only [mixedNew, Finset.mem_map, Finset.mem_filter, not_exists, not_and]
  intro c _ he
  cases he

/-- **The stage after splitting `A`**: the rest of the stage and the new cells over `A`. -/
lemma mixedCells_insert (A : CellIdx E ι) :
    mixedCells K H h (insert A D) = mixedRest K H h D A ∪ mixedNew K H h A := by
  classical
  ext x
  rw [Finset.mem_union, mem_mixedRest]
  rcases x with x | b
  · rw [old_mem_mixedCells, old_mem_mixedCells]
    simp only [old_notMem_mixedNew, or_false, mem_insert, not_or, ne_eq, Mixed.old.injEq]
    tauto
  · rw [new_mem_mixedCells, new_mem_mixedCells, new_mem_mixedNew]
    simp only [mem_insert, ne_eq, reduceCtorEq, not_false_eq_true, and_true]
    constructor
    · rintro ⟨hb, hr | hr⟩
      · exact .inr ⟨hb, hr⟩
      · exact .inl ⟨hb, hr⟩
    · rintro (⟨hb, hr⟩ | ⟨hb, hr⟩)
      · exact ⟨hb, .inr hr⟩
      · exact ⟨hb, .inl hr⟩

/-- **The stage before splitting `A`**: the rest of the stage and the old cell `A`. -/
lemma mixedCells_eq_rest_union {A : CellIdx E ι} (hA : A ∈ cells K (fun i => ⇑(H i)))
    (hAD : A ∉ D) :
    mixedCells K H h D = mixedRest K H h D A ∪ {Mixed.old A} := by
  classical
  ext x
  rw [Finset.mem_union, mem_mixedRest, Finset.mem_singleton]
  constructor
  · intro hx
    by_cases hxA : x = Mixed.old A
    · exact .inr hxA
    · exact .inl ⟨hx, hxA⟩
  · rintro (⟨hx, -⟩ | rfl)
    · exact hx
    · exact old_mem_mixedCells.2 ⟨hA, hAD⟩

/-- **The stage before splitting `A`, as a rest glued to a join.** The rest of the stage, together
with the order complex of the cells below `A` (and `A`) joined to the order complex of the cells
above `A`. -/
theorem orderComplex_mixedCells_decomp {A : CellIdx E ι} (hA : A ∈ cells K (fun i => ⇑(H i)))
    (hAD : A ∉ D) :
    orderComplex (mixedCells K H h D) =
      (orderComplex (mixedRest K H h D A)).union
        ((orderComplex (mixedLower K H h D A ∪ {Mixed.old A})).join
          (orderComplex (mixedUpper K H h D A))) := by
  classical
  rw [mixedCells_eq_rest_union hA hAD]
  refine orderComplex_union_block ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_mixedLower] at hx
    exact mem_mixedRest.2 ⟨hx.1, hx.2.ne⟩
  · intro x hx
    rw [mem_mixedUpper] at hx
    exact mem_mixedRest.2 ⟨hx.1, hx.2.ne'⟩
  · intro l hl u hu
    exact ((mem_mixedLower.1 hl).2.trans (mem_mixedUpper.1 hu).2).le
  · intro w hw u hu
    rw [Finset.mem_singleton] at hw
    subst hw
    exact (mem_mixedUpper.1 hu).2.le
  · intro n hn w hw hnw
    rw [Finset.mem_singleton] at hw
    subst hw
    obtain ⟨hn1, hn2⟩ := mem_mixedRest.1 hn
    rcases hnw with hnw | hnw
    · exact .inl (mem_mixedLower.2 ⟨hn1, lt_of_le_of_ne hnw hn2⟩)
    · exact .inr (mem_mixedUpper.2 ⟨hn1, lt_of_le_of_ne hnw (Ne.symm hn2)⟩)

/-- The restriction of a cell of the extended family is a cell of the original family. -/
lemma CellIdx.restr_mem_cells [DecidableEq E] {b : CellIdx E (ι ⊕ Unit)} (hb : b ∈ cells K (extH H h)) :
    b.restr ∈ cells K (fun i => ⇑(H i)) := by
  have := CellIdx.eq_mk_restr b
  rw [this] at hb
  exact restrict_mem_cells hb

/-- **The stage after splitting `A`, as the same rest glued to a different join.** The old cell `A`
is replaced by the new cells over it. -/
theorem orderComplex_mixedCells_insert_decomp {A : CellIdx E ι}
    (hAD : A ∉ D) (hD : ∀ x ∈ cells K (fun i => ⇑(H i)), ∀ y ∈ D, x ≤ y → x ∈ D) :
    orderComplex (mixedCells K H h (insert A D)) =
      (orderComplex (mixedRest K H h D A)).union
        ((orderComplex (mixedLower K H h D A ∪ mixedNew K H h A)).join
          (orderComplex (mixedUpper K H h D A))) := by
  classical
  rw [mixedCells_insert]
  refine orderComplex_union_block ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_mixedLower] at hx
    exact mem_mixedRest.2 ⟨hx.1, hx.2.ne⟩
  · intro x hx
    rw [mem_mixedUpper] at hx
    exact mem_mixedRest.2 ⟨hx.1, hx.2.ne'⟩
  · intro l hl u hu
    exact ((mem_mixedLower.1 hl).2.trans (mem_mixedUpper.1 hu).2).le
  · intro w hw u hu
    obtain ⟨hu1, hu2⟩ := mem_mixedUpper.1 hu
    rcases w with w | b
    · exact absurd hw old_notMem_mixedNew
    · obtain ⟨-, hb⟩ := new_mem_mixedNew.1 hw
      obtain ⟨z, rfl⟩ : ∃ z, u = Mixed.old z := by
        rcases u with z | c
        · exact ⟨z, rfl⟩
        · exact absurd hu2.le Mixed.not_old_le_new
      rw [Mixed.new_le_old, hb]
      exact Mixed.old_le_old.1 hu2.le
  · intro n hn w hw hnw
    obtain ⟨hn1, hn2⟩ := mem_mixedRest.1 hn
    rcases w with w | b
    · exact absurd hw old_notMem_mixedNew
    · obtain ⟨-, hb⟩ := new_mem_mixedNew.1 hw
      rcases n with z | c
      · rcases hnw with hnw | hnw
        · exact absurd hnw Mixed.not_old_le_new
        · rw [Mixed.new_le_old, hb] at hnw
          refine .inr (mem_mixedUpper.2 ⟨hn1, lt_of_le_of_ne (Mixed.old_le_old.2 hnw) (Ne.symm hn2)⟩)
      · obtain ⟨hcK, hcD⟩ := new_mem_mixedCells.1 hn1
        rcases hnw with hnw | hnw
        · refine .inl (mem_mixedLower.2 ⟨hn1, ?_⟩)
          have h1 : c.restr ≤ A := hb ▸ CellIdx.restr_mono hnw
          have h2 : c.restr ≠ A := fun e => hAD (e ▸ hcD)
          exact lt_of_le_of_ne (Mixed.new_le_old.2 h1) (by intro e; cases e)
        · exfalso
          have h1 : A ≤ c.restr := hb ▸ CellIdx.restr_mono hnw
          have hAc : A ∈ cells K (fun i => ⇑(H i)) :=
            hb ▸ CellIdx.restr_mem_cells (new_mem_mixedNew.1 hw).1
          exact absurd (hD A hAc _ hcD h1) hAD

end SComplex
end Lightlike.PL
