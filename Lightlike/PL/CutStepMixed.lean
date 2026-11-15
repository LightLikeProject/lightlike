import Lightlike.PL.MixedDecomp
import Lightlike.PL.OrderCone

/-!
# Splitting a cut cell in the mixed poset

If the new functional `h` takes both signs on a cell `A` whose lower neighbours are already split,
the three new cells over `A` (positive, zero, negative) replace the old cell. This is the cut swap
of `OrderCone.lean`: the cone over the (already split) boundary of `A` is exchanged, by three ball
swaps, for the two cones over the boundaries of the positive and the negative new cell. The
boundaries of the new cells must be PL spheres; that is the hypothesis carried by the theorem.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
  {K : SComplex E} {H : ι → E →ᵃ[ℝ] ℝ} {h : E →ᵃ[ℝ] ℝ} {D : Finset (CellIdx E ι)}

/-- The new cell over `A` on which `h` has sign `e`, as an element of the mixed poset. -/
def newOver (A : CellIdx E ι) (e : SignType) : Mixed E ι :=
  Mixed.new (mkCell A.1 (extSign A.2 e))

omit [AddCommGroup E] [Module ℝ E] [DecidableEq E] [Fintype ι] [DecidableEq ι] in
/-- The sign is determined by the new cell over `A`. -/
lemma newOver_inj {A : CellIdx E ι} {e e' : SignType} (h : newOver A e = newOver A e') : e = e' := by
  have := congrArg (fun x : CellIdx E (ι ⊕ Unit) => x.2 (Sum.inr ())) (Mixed.new.inj h)
  simpa [extSign] using this

omit [AddCommGroup E] [Module ℝ E] [DecidableEq E] [Fintype ι] [DecidableEq ι] in
/-- A new cell below an old cell lies below the new cell over it with sign `e` exactly when its own
sign is zero or `e`. -/
lemma new_le_newOver {b : CellIdx E (ι ⊕ Unit)} {A : CellIdx E ι} (hb : b.restr ≤ A)
    (e : SignType) :
    Mixed.new b ≤ newOver A e ↔ b.2 (Sum.inr ()) = 0 ∨ b.2 (Sum.inr ()) = e := by
  rw [newOver, Mixed.new_le_new, cellIdx_le]
  constructor
  · rintro ⟨-, hs⟩
    simpa [extSign] using hs (Sum.inr ())
  · intro hs
    refine ⟨hb.1, ?_⟩
    rintro (i | ⟨⟩)
    · exact hb.2 i
    · simpa [extSign] using hs

/-- When `h` takes all three signs on the cell `A`, the new cells over `A` are exactly the three
cells `newOver A 1`, `newOver A 0` and `newOver A (-1)`. -/
lemma mixedNew_eq_of_cut {A : CellIdx E ι} (hAK : A.1 ∈ K)
    (hp : ∃ x ∈ cellSet (fun i => ⇑(H i)) A, 0 < h x)
    (hz : ∃ x ∈ cellSet (fun i => ⇑(H i)) A, h x = 0)
    (hn : ∃ x ∈ cellSet (fun i => ⇑(H i)) A, h x < 0) :
    mixedNew K H h A = {newOver A 1, newOver A 0, newOver A (-1)} := by
  classical
  ext x
  rcases x with y | b
  · simp only [old_notMem_mixedNew, mem_insert, mem_singleton, false_iff]
    simp [newOver]
  · rw [new_mem_mixedNew]
    simp only [mem_insert, mem_singleton, newOver, Mixed.new.injEq]
    constructor
    · rintro ⟨-, hr⟩
      have h1 := CellIdx.eq_mk_restr b
      rw [hr] at h1
      rcases SignType.trichotomy (b.2 (Sum.inr ())) with he | he | he
      · exact .inr (.inr (h1.trans (by rw [he])))
      · exact .inr (.inl (h1.trans (by rw [he])))
      · exact .inl (h1.trans (by rw [he]))
    · intro hb
      have hc : ∀ e, mkCell A.1 (extSign A.2 e) ∈ cells K (extH H h) := fun e =>
        ext_cell_mem_of_cut (σ := A.1) (s := A.2) hAK hp hz hn e
      rcases hb with rfl | rfl | rfl
      · exact ⟨hc 1, rfl⟩
      · exact ⟨hc 0, rfl⟩
      · exact ⟨hc (-1), rfl⟩

omit [DecidableEq E] in
/-- The elements of the stage below the old cell `A` are new cells over cells strictly below `A`. -/
lemma mem_mixedLower_new {A : CellIdx E ι} (hAD : A ∉ D)
    (hmin : ∀ x ∈ cells K (fun i => ⇑(H i)), x < A → x ∈ D) {x : Mixed E ι}
    (hx : x ∈ mixedLower K H h D A) :
    ∃ b, x = Mixed.new b ∧ b ∈ cells K (extH H h) ∧ b.restr ∈ D ∧ b.restr < A := by
  obtain ⟨h1, h2⟩ := mem_mixedLower.1 hx
  rcases x with y | b
  · obtain ⟨hy, hyD⟩ := old_mem_mixedCells.1 h1
    exact absurd (hmin y hy (Mixed.old_le_old.1 h2.le |>.lt_of_ne fun e => by
      rw [e] at h2; exact lt_irrefl _ h2)) hyD
  · obtain ⟨hb, hbD⟩ := new_mem_mixedCells.1 h1
    refine ⟨b, rfl, hb, hbD, lt_of_le_of_ne (Mixed.new_le_old.1 h2.le) fun e => hAD (e ▸ hbD)⟩

omit [AddCommGroup E] [Module ℝ E] [DecidableEq E] [Fintype ι] [DecidableEq ι] in
/-- A new cell whose restriction is not `A` is none of the new cells over `A`. -/
lemma new_ne_newOver {b : CellIdx E (ι ⊕ Unit)} {A : CellIdx E ι} (hb : b.restr ≠ A) (e : SignType) :
    Mixed.new b ≠ newOver A e := fun h => hb (by rw [Mixed.new.inj h]; rfl)

omit [AddCommGroup E] [Module ℝ E] [DecidableEq E] [Fintype ι] [DecidableEq ι] in
/-- A new cell is never an old cell. -/
lemma newOver_ne_old {A B : CellIdx E ι} (e : SignType) : newOver A e ≠ Mixed.old B :=
  fun h => by cases h

omit [AddCommGroup E] [Module ℝ E] [DecidableEq E] [Fintype ι] [DecidableEq ι] in
/-- The cell `newOver A 0` lies strictly below `newOver A e` for `e ≠ 0`. -/
lemma newOver_zero_lt {A : CellIdx E ι} {e : SignType} (he : e ≠ 0) :
    newOver A 0 < newOver A e := by
  refine lt_of_le_of_ne ?_ fun h => he (newOver_inj h).symm
  exact (new_le_newOver (b := mkCell A.1 (extSign A.2 0)) le_rfl e).2 (.inl rfl)

section Cut

variable {A : CellIdx E ι} (hA : A ∈ cells K (fun i => ⇑(H i))) (hAD : A ∉ D)
  (hp : ∃ x ∈ cellSet (fun i => ⇑(H i)) A, 0 < h x)
  (hz : ∃ x ∈ cellSet (fun i => ⇑(H i)) A, h x = 0)
  (hn : ∃ x ∈ cellSet (fun i => ⇑(H i)) A, h x < 0)

include hA hp hz hn in
/-- Each new cell over a cut cell `A` is in the stage after splitting `A`. -/
lemma newOver_mem_stage (e : SignType) :
    newOver A e ∈ mixedCells K H h (insert A D) :=
  new_mem_mixedCells.2 ⟨ext_cell_mem_of_cut (mem_cells.1 hA).1 hp hz hn e, mem_insert_self A D⟩

include hAD in
omit [DecidableEq E] in
/-- No new cell over `A` is in the stage before splitting `A`. -/
lemma newOver_notMem_stage (e : SignType) : newOver A e ∉ mixedCells K H h D :=
  fun hm => hAD (new_mem_mixedCells.1 hm).2

include hA hp hz hn in
open Classical in
/-- The elements of the stage after splitting `A` that lie below the new positive (or negative)
cell: the zero cell and the lower elements below it. -/
lemma stage_filter_eq {e : SignType} (he : e ≠ 0) :
    (mixedCells K H h (insert A D)).filter (· < newOver A e) =
      insert (newOver A 0) ((mixedLower K H h D A).filter (· < newOver A e)) := by
  ext x
  simp only [mem_filter, mem_insert]
  constructor
  · rintro ⟨hx, hlt⟩
    rcases x with y | b
    · exact absurd hlt.le Mixed.not_old_le_new
    · obtain ⟨hb, hbD⟩ := new_mem_mixedCells.1 hx
      have hbA : b.restr ≤ A := CellIdx.restr_mono (Mixed.new_le_new.1 hlt.le)
      rcases mem_insert.1 hbD with hr | hr
      · have hs := (new_le_newOver hr.le e).1 hlt.le
        have h1 := CellIdx.eq_mk_restr b
        rw [hr] at h1
        rcases hs with hs | hs
        · exact .inl (by rw [newOver, ← hs, ← h1])
        · exact absurd (by rw [newOver, ← hs, ← h1]) (ne_of_lt hlt)
      · exact .inr ⟨mem_mixedLower.2 ⟨new_mem_mixedCells.2 ⟨hb, hr⟩, lt_of_le_of_ne
          (Mixed.new_le_old.2 hbA) fun h' => absurd h' (by simp)⟩, hlt⟩
  · rintro (rfl | ⟨hxL, hlt⟩)
    · exact ⟨newOver_mem_stage hA hp hz hn 0, newOver_zero_lt he⟩
    · obtain ⟨hx1, hx2⟩ := mem_mixedLower.1 hxL
      refine ⟨?_, hlt⟩
      rw [mixedCells_insert]
      exact mem_union_left _ (mem_mixedRest.2 ⟨hx1, hx2.ne⟩)

end Cut

omit [AddCommGroup E] [Module ℝ E] [DecidableEq E] [Fintype ι] [DecidableEq ι] in
/-- A new cell over a cell strictly below `A` lies strictly below the new cell over `A` with sign `e`
exactly when its own sign is zero or `e`. -/
lemma lower_lt_iff {b : CellIdx E (ι ⊕ Unit)} {A : CellIdx E ι} (hr : b.restr < A) (e : SignType) :
    Mixed.new b < newOver A e ↔ b.2 (Sum.inr ()) = 0 ∨ b.2 (Sum.inr ()) = e :=
  ⟨fun h => (new_le_newOver hr.le e).1 h.le, fun h =>
    lt_of_le_of_ne ((new_le_newOver hr.le e).2 h) (new_ne_newOver hr.ne e)⟩

open Classical in
/-- **A cut cell is split by the cut swap.** Let `h` take all three signs on the cell `A`, whose
lower neighbours are already split. If the boundaries of the new positive cell and the new negative
cell (the elements of the stage after splitting that lie below them) are PL spheres, the stage
before splitting `A` is stellar equivalent to the stage after. -/
theorem stellarEquivIn_mixed_cut [Infinite (Mixed E ι)] {n : ℕ} {A : CellIdx E ι}
    (hA : A ∈ cells K (fun i => ⇑(H i))) (hAD : A ∉ D)
    (hD : ∀ x ∈ cells K (fun i => ⇑(H i)), ∀ y ∈ D, x ≤ y → x ∈ D)
    (hmin : ∀ x ∈ cells K (fun i => ⇑(H i)), x < A → x ∈ D)
    (hp : ∃ x ∈ cellSet (fun i => ⇑(H i)) A, 0 < h x)
    (hz : ∃ x ∈ cellSet (fun i => ⇑(H i)) A, h x = 0)
    (hn : ∃ x ∈ cellSet (fun i => ⇑(H i)) A, h x < 0)
    (hSp : IsSB false (n + 1)
      (orderComplex ((mixedCells K H h (insert A D)).filter (· < newOver A 1))))
    (hSm : IsSB false (n + 1)
      (orderComplex ((mixedCells K H h (insert A D)).filter (· < newOver A (-1))))) :
    StellarEquivIn (orderComplex (mixedCells K H h D))
      (orderComplex (mixedCells K H h (insert A D))) := by
  have hnew := mixedNew_eq_of_cut (K := K) (H := H) (h := h) (mem_cells.1 hA).1 hp hz hn
  rw [stage_filter_eq hA hp hz hn (by decide)] at hSp
  rw [stage_filter_eq hA hp hz hn (by decide)] at hSm
  rw [orderComplex_mixedCells_decomp hA hAD, orderComplex_mixedCells_insert_decomp hAD hD]
  have e1 : mixedLower K H h D A ∪ {Mixed.old A} = insert (Mixed.old A) (mixedLower K H h D A) := by
    ext x; simp only [mem_union, mem_insert, mem_singleton]; tauto
  have e2 : mixedLower K H h D A ∪ mixedNew K H h A = insert (newOver A 1) (insert (newOver A (-1))
      (insert (newOver A 0) (mixedLower K H h D A))) := by
    rw [hnew]; ext x; simp only [mem_union, mem_insert, mem_singleton]; tauto
  rw [e1, e2]
  have hLD : ∀ x ∈ mixedLower K H h D A, x ∈ mixedCells K H h D := fun x hx =>
    (mem_mixedLower.1 hx).1
  have hUD : ∀ x ∈ mixedUpper K H h D A, x ∈ mixedCells K H h D := fun x hx =>
    (mem_mixedUpper.1 hx).1
  have hRD : ∀ x ∈ mixedRest K H h D A, x ∈ mixedCells K H h D := fun x hx =>
    (mem_mixedRest.1 hx).1
  have hLn : ∀ x ∈ mixedLower K H h D A, ∃ b, x = Mixed.new b ∧ b.restr < A := fun x hx => by
    obtain ⟨b, rfl, -, -, hr⟩ := mem_mixedLower_new hAD hmin hx
    exact ⟨b, rfl, hr⟩
  refine stellarEquivIn_order_cut (n := n) (a := Mixed.old A) (u := newOver A 1)
    (v := newOver A (-1)) (z := newOver A 0) (fun l hl => (mem_mixedLower.1 hl).2.le) ?_
    (newOver_zero_lt (by decide)) (newOver_zero_lt (by decide)) ?_ ?_ ?_ ?_ ?_ hSp hSm
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun h => newOver_notMem_stage hAD 0 (hLD _ h)
  · intro h
    have := (cellIdx_le.1 (Mixed.new_le_new.1 h)).2 (Sum.inr ())
    simp [extSign] at this
  · intro h
    have := (cellIdx_le.1 (Mixed.new_le_new.1 h)).2 (Sum.inr ())
    simp [extSign] at this
  · intro x hx
    obtain ⟨b, rfl, hr⟩ := hLn x hx
    rcases SignType.trichotomy (b.2 (Sum.inr ())) with he | he | he
    · exact .inr ((lower_lt_iff hr _).2 (.inr he))
    · exact .inl ((lower_lt_iff hr _).2 (.inl he))
    · exact .inl ((lower_lt_iff hr _).2 (.inr he))
  · intro x hx h1 h2
    obtain ⟨b, rfl, hr⟩ := hLn x hx
    rw [lower_lt_iff hr] at h1 h2 ⊢
    rcases h1 with h1 | h1
    · exact .inl h1
    · rcases h2 with h2 | h2
      · exact .inl h2
      · exact absurd (h1.symm.trans h2) (by decide)
  · intro x hx h
    obtain ⟨b, rfl, hr⟩ := hLn x hx
    have h' := (cellIdx_le.1 (Mixed.new_le_new.1 h.le))
    have hAb : A ≤ b.restr := ⟨h'.1, fun i => h'.2 (Sum.inl i)⟩
    exact lt_irrefl _ (lt_of_lt_of_le hr hAb)
  · intro h
    rcases mem_insert.1 h with h | h
    · exact newOver_ne_old 0 h.symm
    · exact lt_irrefl _ (mem_mixedLower.1 h).2
  · intro h
    rcases mem_insert.1 h with h | h
    · exact absurd (newOver_inj h) (by decide)
    · exact newOver_notMem_stage hAD 1 (hLD _ h)
  · intro h
    rcases mem_insert.1 h with h | h
    · exact absurd (newOver_inj h) (by decide)
    · exact newOver_notMem_stage hAD (-1) (hLD _ h)
  · refine Finset.disjoint_left.2 fun x hx hxU => ?_
    rcases mem_insert.1 hx with rfl | hx
    · exact newOver_notMem_stage hAD 0 (hUD _ hxU)
    · exact lt_asymm (mem_mixedLower.1 hx).2 (mem_mixedUpper.1 hxU).2
  · exact fun h => lt_irrefl _ (mem_mixedUpper.1 h).2
  · exact fun h => newOver_notMem_stage hAD 1 (hUD _ h)
  · exact fun h => newOver_notMem_stage hAD (-1) (hUD _ h)
  · exact fun h => newOver_notMem_stage hAD 0 (hRD _ h)
  · exact fun h => (mem_mixedRest.1 h).2 rfl
  · exact fun h => newOver_notMem_stage hAD 1 (hRD _ h)
  · exact fun h => newOver_notMem_stage hAD (-1) (hRD _ h)

end SComplex
end Lightlike.PL
