import Lightlike.PL.Mixed

/-!
# One stage of the mixed poset: an uncut cell

Splitting a cell `A` on which the new functional `h` has constant sign `e` changes nothing but
a name: the old cell `A` becomes the new cell `A` with sign `e`, and the order relations to the
other elements of the stage are unchanged. This file proves that the next stage is the image of
the current one under the permutation that swaps these two elements.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

variable {K : SComplex E} {H : ι → E →ᵃ[ℝ] ℝ} {h : E →ᵃ[ℝ] ℝ} {D : Finset (CellIdx E ι)}

omit [DecidableEq E] in
/-- An old cell is in a stage when it is a cell outside the set of split cells. -/
lemma old_mem_mixedCells {x : CellIdx E ι} :
    Mixed.old x ∈ mixedCells K H h D ↔ x ∈ cells K (fun i => ⇑(H i)) ∧ x ∉ D := by
  classical
  simp only [mixedCells, Finset.mem_union, Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro (⟨a, ha, he⟩ | ⟨b, -, he⟩)
    · exact (Mixed.old.inj he) ▸ ha
    · cases he
  · rintro ha
    exact .inl ⟨x, ha, rfl⟩

omit [DecidableEq E] in
/-- A new cell is in a stage when it is a cell of the extended family over a split cell. -/
lemma new_mem_mixedCells {b : CellIdx E (ι ⊕ Unit)} :
    Mixed.new b ∈ mixedCells K H h D ↔ b ∈ cells K (extH H h) ∧ b.restr ∈ D := by
  classical
  simp only [mixedCells, Finset.mem_union, Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro (⟨a, -, he⟩ | ⟨c, hc, he⟩)
    · cases he
    · exact (Mixed.new.inj he) ▸ hc
  · rintro hb
    exact .inr ⟨b, hb, rfl⟩

/-- If `h` has constant sign `e` on `A`, a new cell over a cell below `A` has `h`-sign zero or `e`. -/
lemma sign_new_of_le_const {y : CellIdx E (ι ⊕ Unit)} {A' : CellIdx E ι} {e : SignType}
    (hy : y ∈ cells K (extH H h)) (hle : y.restr ≤ A')
    (hp : (cellSet (fun i => ⇑(H i)) A').Nonempty)
    (hconst : ∀ q ∈ cellSet (fun i => ⇑(H i)) A', SignType.sign (h q) = e) :
    y.2 (Sum.inr ()) = 0 ∨ y.2 (Sum.inr ()) = e := by
  obtain ⟨-, x, hx⟩ := mem_cells.1 hy
  have hx2 : x ∈ cellSet (extH H h) (mkCell y.restr.1 (extSign y.restr.2 (y.2 (Sum.inr ())))) := by
    rw [← CellIdx.eq_mk_restr y]; exact hx
  obtain ⟨hx3, hx4⟩ := mem_cellSet_ext.1 hx2
  obtain ⟨p, hp'⟩ := hp
  rw [← hx4]
  exact sign_face_of_const hle hx3 hp' hconst

/-- **Splitting an uncut cell only renames it.** If `A` is a cell outside the split set `D`, all
cells below `A` are in `D`, `D` is closed downwards and `h` has constant sign `e` on `A`, then the
stage after splitting `A` is the image of the current stage under the swap of the old cell `A` with
the new cell `A` of sign `e`. -/
theorem orderComplex_mixedCells_insert_of_const {A : CellIdx E ι} {e : SignType}
    (hA : A ∈ cells K (fun i => ⇑(H i))) (hAD : A ∉ D)
    (hD : ∀ x ∈ cells K (fun i => ⇑(H i)), ∀ y ∈ D, x ≤ y → x ∈ D)
    (hmin : ∀ x ∈ cells K (fun i => ⇑(H i)), x < A → x ∈ D)
    (hconst : ∀ q ∈ cellSet (fun i => ⇑(H i)) A, SignType.sign (h q) = e) :
    orderComplex (mixedCells K H h (insert A D)) =
      (orderComplex (mixedCells K H h D)).map
        (Equiv.swap (Mixed.old A) (Mixed.new (mkCell A.1 (extSign A.2 e)))).toEmbedding := by
  classical
  set Ae : CellIdx E (ι ⊕ Unit) := mkCell A.1 (extSign A.2 e) with hAe
  obtain ⟨hAK, hAne⟩ := mem_cells.1 hA
  have hAecells : Ae ∈ cells K (extH H h) :=
    (ext_cell_mem_iff_const (K := K) (H := H) (h := h) hAK hAne hconst e).2 rfl
  have hres : Ae.restr = A := rfl
  have hkey : ∀ b ∈ cells K (extH H h), b.restr = A → b = Ae := by
    intro b hb hr
    have h1 := CellIdx.eq_mk_restr b
    rw [hr] at h1
    rw [h1] at hb
    have := (ext_cell_mem_iff_const (K := K) (H := H) (h := h) hAK hAne hconst _).1 hb
    rw [h1, this]
  have hAeD : Mixed.new Ae ∉ mixedCells K H h D := fun hm =>
    hAD (hres ▸ (new_mem_mixedCells.1 hm).2)
  have hmem : ∀ y, y ∈ mixedCells K H h (insert A D) ↔
      Equiv.swap (Mixed.old A) (Mixed.new Ae) y ∈ mixedCells K H h D := by
    rintro (x | b)
    · by_cases hx : x = A
      · subst hx
        rw [Equiv.swap_apply_left, old_mem_mixedCells, new_mem_mixedCells, hres]
        simp [hAD]
      · rw [Equiv.swap_apply_of_ne_of_ne (by simpa using hx) (by simp), old_mem_mixedCells,
          old_mem_mixedCells]
        simp [hx]
    · by_cases hb : b = Ae
      · subst hb
        rw [Equiv.swap_apply_right, old_mem_mixedCells, new_mem_mixedCells, hres]
        simp [hA, hAD, hAecells]
      · rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hb), new_mem_mixedCells,
          new_mem_mixedCells]
        constructor
        · rintro ⟨hc, hr⟩
          rcases mem_insert.1 hr with hr | hr
          · exact absurd (hkey b hc hr) hb
          · exact ⟨hc, hr⟩
        · rintro ⟨hc, hr⟩
          exact ⟨hc, mem_insert_of_mem hr⟩
  have hset : mixedCells K H h (insert A D) =
      (mixedCells K H h D).map (Equiv.swap (Mixed.old A) (Mixed.new Ae)).toEmbedding := by
    ext y
    rw [Finset.mem_map_equiv, Equiv.symm_swap]
    exact hmem y
  rw [hset]
  refine orderComplex_map_on _ fun a ha b hb => ?_
  simp only [Equiv.coe_toEmbedding]
  have hnotAe : ∀ a ∈ mixedCells K H h D, a ≠ Mixed.new Ae := fun a ha h' => hAeD (h' ▸ ha)
  have hρ : ∀ a ∈ mixedCells K H h D, a ≠ Mixed.old A →
      Equiv.swap (Mixed.old A) (Mixed.new Ae) a = a := fun a ha hne =>
    Equiv.swap_apply_of_ne_of_ne hne (hnotAe a ha)
  by_cases ha' : a = Mixed.old A
  · subst ha'
    rw [Equiv.swap_apply_left]
    by_cases hb' : b = Mixed.old A
    · subst hb'
      rw [Equiv.swap_apply_left]
      exact ⟨fun _ => le_refl _, fun _ => le_refl _⟩
    · rw [hρ b hb hb']
      rcases b with y | z
      · exact Iff.rfl
      · have hz := new_mem_mixedCells.1 hb
        constructor
        · intro hle
          exfalso
          have : A ≤ z.restr := hres ▸ CellIdx.restr_mono (Mixed.new_le_new.1 hle)
          exact hAD (hD A hA _ hz.2 this)
        · intro hle
          exact (Mixed.not_old_le_new hle).elim
  · rw [hρ a ha ha']
    by_cases hb' : b = Mixed.old A
    · subst hb'
      rw [Equiv.swap_apply_left]
      rcases a with x | y
      · have hx := old_mem_mixedCells.1 ha
        constructor
        · intro hle
          exact (Mixed.not_old_le_new hle).elim
        · intro hle
          exfalso
          have hlt : x < A := lt_of_le_of_ne (Mixed.old_le_old.1 hle)
            (fun h' => ha' (h' ▸ rfl))
          exact hx.2 (hmin x hx.1 hlt)
      · have hy := new_mem_mixedCells.1 ha
        constructor
        · intro hle
          exact Mixed.new_le_old.2 (CellIdx.restr_mono (Mixed.new_le_new.1 hle))
        · intro hle
          have hle' : y.restr ≤ A := Mixed.new_le_old.1 hle
          refine Mixed.new_le_new.2 ⟨hle'.1, ?_⟩
          rintro (i | ⟨⟩)
          · exact hle'.2 i
          · exact sign_new_of_le_const hy.1 hle' hAne hconst
    · rw [hρ b hb hb']

end SComplex
end Lightlike.PL
