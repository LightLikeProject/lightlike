module

public import Lightlike.PonzanoRegge.GaugeFixed

/-!
# The inverse Pachner moves 3-2 and 4-1 on an arbitrary complex

`IsMove23`/`move23` and `IsMove14`/`move14` describe the 2-3 and 1-4 moves. Until now their
inverses were covered only for a complex already written as `move23 K h` or `move14 K h`. This file
recognises them on an arbitrary complex.

* `IsMove32 K A B C D E`: the edge `DE` lies in exactly the three tetrahedra `ABDE`, `BCDE`,
  `CADE`, and no tetrahedron contains the triangle `ABC`. `move32` replaces those three tetrahedra
  by `ABCD` and `ABCE`.
* `IsMove41 K A B C D E`: the vertex `E` lies in exactly the four tetrahedra `ABCE`, `ABDE`,
  `ACDE`, `BCDE`, and `ABCD` is not a tetrahedron. `move41` replaces the four by `ABCD`.
* The moves are mutually inverse, with matching preconditions: `isMove23_move32`,
  `move23_move32`, `isMove32_move23`, `move32_move23`, and the same four for 1-4 and 4-1.
* `amplitudeGF_move32`, `amplitudeGF_move41`: the gauge-fixed amplitude is unchanged by the
  inverse moves, under the cutoff conditions of the forward moves; `gfStep_move32`,
  `gfStep_move41` place them in the chains of `amplitudeGF_eqvGen`.

For the 4-1 move the removed vertex `E` must be joined to the rest of the gauge set by the single
gauge edge `DE` (any of `A, B, C, D` can play the role of `D`). If `E` carries several gauge edges,
removing it changes the gauge set in a way these theorems do not cover; for a maximal tree this is
the question of independence of the tree.
-/

@[expose] public section

open Finset

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- Two complexes with the same tetrahedra are equal. -/
@[ext] lemma Complex3.ext {K K' : Complex3 V} (h : K.tets = K'.tets) : K = K' := by
  cases K; cases K'; subst h; rfl

/-! ## The 3-2 move -/

/-- Preconditions of a 3-2 move on `K`: the edge `DE` lies in exactly the three tetrahedra
`ABDE`, `BCDE`, `CADE`, and no tetrahedron of `K` contains the triangle `ABC`. -/
structure IsMove32 (K : Complex3 V) (A B C D E : V) : Prop where
  hAB : A ≠ B
  hAC : A ≠ C
  hAD : A ≠ D
  hAE : A ≠ E
  hBC : B ≠ C
  hBD : B ≠ D
  hBE : B ≠ E
  hCD : C ≠ D
  hCE : C ≠ E
  hDE : D ≠ E
  mem₁ : {A, B, D, E} ∈ K.tets
  mem₂ : {B, C, D, E} ∈ K.tets
  mem₃ : {C, A, D, E} ∈ K.tets
  star : ∀ t ∈ K.tets, {D, E} ⊆ t → t = {A, B, D, E} ∨ t = {B, C, D, E} ∨ t = {C, A, D, E}
  fresh : ∀ t ∈ K.tets, ¬ {A, B, C} ⊆ t

/-- **The 3-2 Pachner move**: replace `ABDE`, `BCDE`, `CADE` by `ABCD`, `ABCE`. -/
def move32 (K : Complex3 V) {A B C D E : V} (h : IsMove32 K A B C D E) : Complex3 V where
  tets := {{A, B, C, D}, {A, B, C, E}} ∪
    ((K.tets.erase {A, B, D, E}).erase {B, C, D, E}).erase {C, A, D, E}
  card_eq t ht := by
    rcases mem_union.mp ht with ht | ht
    · simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact card_four h.hAB h.hAC h.hAD h.hBC h.hBD h.hCD
      · exact card_four h.hAB h.hAC h.hAE h.hBC h.hBE h.hCE
    · exact K.card_eq t (mem_of_mem_erase (mem_of_mem_erase (mem_of_mem_erase ht)))

/-- After a 3-2 move, the 2-3 move along `DE` applies. -/
theorem isMove23_move32 {K : Complex3 V} {A B C D E : V} (h : IsMove32 K A B C D E) :
    IsMove23 (move32 K h) A B C D E where
  hAB := h.hAB
  hAC := h.hAC
  hAD := h.hAD
  hAE := h.hAE
  hBC := h.hBC
  hBD := h.hBD
  hBE := h.hBE
  hCD := h.hCD
  hCE := h.hCE
  hDE := h.hDE
  mem₁ := by simp [move32]
  mem₂ := by simp [move32]
  face t ht hsub := by
    simp only [move32, mem_union, mem_insert, mem_singleton, mem_erase] at ht
    rcases ht with (rfl | rfl) | ⟨-, -, -, ht⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hsub (h.fresh t ht)
  fresh t ht hsub := by
    have hD : D ∈ t := hsub (by simp)
    have hE : E ∈ t := hsub (by simp)
    simp only [move32, mem_union, mem_insert, mem_singleton, mem_erase] at ht
    rcases ht with (rfl | rfl) | ⟨h3, h2, h1, ht⟩
    · simp [h.hAE.symm, h.hBE.symm, h.hCE.symm, h.hDE.symm] at hE
    · simp [h.hAD.symm, h.hBD.symm, h.hCD.symm, h.hDE] at hD
    · rcases h.star t ht hsub with rfl | rfl | rfl
      exacts [h1 rfl, h2 rfl, h3 rfl]

/-- **The 2-3 move undoes the 3-2 move.** -/
theorem move23_move32 {K : Complex3 V} {A B C D E : V} (h : IsMove32 K A B C D E) :
    move23 (move32 K h) (isMove23_move32 h) = K := by
  have hABCD : ({A, B, C, D} : Finset V) ∉ K.tets := fun hm => h.fresh _ hm (by small_subset)
  have hABCE : ({A, B, C, E} : Finset V) ∉ K.tets := fun hm => h.fresh _ hm (by small_subset)
  ext t
  simp only [move23, move32, mem_union, mem_insert, mem_singleton, mem_erase]
  constructor
  · rintro ((rfl | rfl | rfl) | ⟨hne2, hne1, (rfl | rfl) | ⟨-, -, -, ht⟩⟩)
    · exact h.mem₁
    · exact h.mem₂
    · exact h.mem₃
    · exact absurd rfl hne1
    · exact absurd rfl hne2
    · exact ht
  · intro ht
    by_cases h1 : t = {A, B, D, E}
    · exact Or.inl (Or.inl h1)
    by_cases h2 : t = {B, C, D, E}
    · exact Or.inl (Or.inr (Or.inl h2))
    by_cases h3 : t = {C, A, D, E}
    · exact Or.inl (Or.inr (Or.inr h3))
    refine Or.inr ⟨?_, ?_, Or.inr ⟨h3, h2, h1, ht⟩⟩
    · rintro rfl
      exact hABCE ht
    · rintro rfl
      exact hABCD ht

/-- After a 2-3 move, the 3-2 move along `DE` applies. -/
theorem isMove32_move23 {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) :
    IsMove32 (move23 K h) A B C D E where
  hAB := h.hAB
  hAC := h.hAC
  hAD := h.hAD
  hAE := h.hAE
  hBC := h.hBC
  hBD := h.hBD
  hBE := h.hBE
  hCD := h.hCD
  hCE := h.hCE
  hDE := h.hDE
  mem₁ := by simp [move23]
  mem₂ := by simp [move23]
  mem₃ := by simp [move23]
  star t ht hsub := by
    simp only [move23, mem_union, mem_insert, mem_singleton, mem_erase] at ht
    rcases ht with (rfl | rfl | rfl) | ⟨-, -, ht⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact absurd hsub (h.fresh t ht)
  fresh t ht hsub := by
    have hA : A ∈ t := hsub (by simp)
    have hB : B ∈ t := hsub (by simp)
    have hC : C ∈ t := hsub (by simp)
    simp only [move23, mem_union, mem_insert, mem_singleton, mem_erase] at ht
    rcases ht with (rfl | rfl | rfl) | ⟨hne2, hne1, ht⟩
    · simp [h.hAC.symm, h.hBC.symm, h.hCD, h.hCE] at hC
    · simp [h.hAB, h.hAC, h.hAD, h.hAE] at hA
    · simp [h.hAB.symm, h.hBC, h.hBD, h.hBE] at hB
    · rcases h.face t ht hsub with rfl | rfl
      exacts [hne1 rfl, hne2 rfl]

/-- **The 3-2 move undoes the 2-3 move.** -/
theorem move32_move23 {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) :
    move32 (move23 K h) (isMove32_move23 h) = K := by
  have hABDE : ({A, B, D, E} : Finset V) ∉ K.tets := fun hm => h.fresh _ hm (by small_subset)
  have hBCDE : ({B, C, D, E} : Finset V) ∉ K.tets := fun hm => h.fresh _ hm (by small_subset)
  have hCADE : ({C, A, D, E} : Finset V) ∉ K.tets := fun hm => h.fresh _ hm (by small_subset)
  ext t
  simp only [move23, move32, mem_union, mem_insert, mem_singleton, mem_erase]
  constructor
  · rintro ((rfl | rfl) | ⟨h3, h2, h1, (rfl | rfl | rfl) | ⟨-, -, ht⟩⟩)
    · exact h.mem₁
    · exact h.mem₂
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact ht
  · intro ht
    by_cases h1 : t = {A, B, C, D}
    · exact Or.inl (Or.inl h1)
    by_cases h2 : t = {A, B, C, E}
    · exact Or.inl (Or.inr h2)
    refine Or.inr ⟨?_, ?_, ?_, Or.inr ⟨h2, h1, ht⟩⟩
    · rintro rfl
      exact hCADE ht
    · rintro rfl
      exact hBCDE ht
    · rintro rfl
      exact hABDE ht

/-- The edges after a 3-2 move: all old edges except `DE`. -/
theorem edges_move32 {K : Complex3 V} {A B C D E : V} (h : IsMove32 K A B C D E) :
    (move32 K h).edges = K.edges.erase {D, E} := by
  have h1 := edges_move23 (move32 K h) (isMove23_move32 h)
  rw [move23_move32] at h1
  have hDE : ({D, E} : Finset V) ∉ (move32 K h).edges := fun hm => by
    obtain ⟨t, ht, hst, -⟩ := Complex3.mem_edges.mp hm
    exact (isMove23_move32 h).fresh t ht hst
  rw [h1, erase_insert hDE]

/-- **The gauge-fixed amplitude is unchanged by a 3-2 move**, for any gauge set `T` of old edges
other than `DE`, if the cutoff of the removed edge satisfies `cut AD + cut AE ≤ cut DE`. -/
theorem amplitudeGF_move32 (K : Complex3 V) {A B C D E : V} (h : IsMove32 K A B C D E)
    (T : Finset (Finset V)) (hT : T ⊆ K.edges) (hDE : ({D, E} : Finset V) ∉ T)
    (cut : Finset V → ℕ) (hcut : cut {A, D} + cut {A, E} ≤ cut {D, E}) :
    amplitudeGF (move32 K h) T cut = amplitudeGF K T cut := by
  have hT' : T ⊆ (move32 K h).edges := by
    rw [edges_move32]
    intro e he
    exact mem_erase.mpr ⟨fun h' => hDE (h' ▸ he), hT he⟩
  have := amplitudeGF_move23 (move32 K h) (isMove23_move32 h) T hT' cut hcut
  rw [move23_move32] at this
  exact this.symm

/-- A 3-2 move is a step of the chains in `amplitudeGF_eqvGen` (read backwards). -/
theorem gfStep_move32 {K : Complex3 V} {A B C D E : V} (h : IsMove32 K A B C D E)
    {T : Finset (Finset V)} (hT : T ⊆ K.edges) (hDE : ({D, E} : Finset V) ∉ T)
    {cut : Finset V → ℕ} (hcut : cut {A, D} + cut {A, E} ≤ cut {D, E}) :
    GFStep (move32 K h, T, cut) (K, T, cut) := by
  have hT' : T ⊆ (move32 K h).edges := by
    rw [edges_move32]
    intro e he
    exact mem_erase.mpr ⟨fun h' => hDE (h' ▸ he), hT he⟩
  have := GFStep.move23 (isMove23_move32 h) hT' hcut
  rwa [move23_move32] at this

/-! ## The 4-1 move -/

/-- Preconditions of a 4-1 move on `K`: the vertex `E` lies in exactly the four tetrahedra
`ABCE`, `ABDE`, `ACDE`, `BCDE`, and `ABCD` is not a tetrahedron of `K`. -/
structure IsMove41 (K : Complex3 V) (A B C D E : V) : Prop where
  hAB : A ≠ B
  hAC : A ≠ C
  hAD : A ≠ D
  hAE : A ≠ E
  hBC : B ≠ C
  hBD : B ≠ D
  hBE : B ≠ E
  hCD : C ≠ D
  hCE : C ≠ E
  hDE : D ≠ E
  mem₁ : {A, B, C, E} ∈ K.tets
  mem₂ : {A, B, D, E} ∈ K.tets
  mem₃ : {A, C, D, E} ∈ K.tets
  mem₄ : {B, C, D, E} ∈ K.tets
  star : ∀ t ∈ K.tets, E ∈ t →
    t = {A, B, C, E} ∨ t = {A, B, D, E} ∨ t = {A, C, D, E} ∨ t = {B, C, D, E}
  fresh : {A, B, C, D} ∉ K.tets

/-- **The 4-1 Pachner move**: replace `ABCE`, `ABDE`, `ACDE`, `BCDE` by `ABCD`. -/
def move41 (K : Complex3 V) {A B C D E : V} (h : IsMove41 K A B C D E) : Complex3 V where
  tets := insert {A, B, C, D}
    ((((K.tets.erase {A, B, C, E}).erase {A, B, D, E}).erase {A, C, D, E}).erase {B, C, D, E})
  card_eq t ht := by
    rcases mem_insert.mp ht with rfl | ht
    · exact card_four h.hAB h.hAC h.hAD h.hBC h.hBD h.hCD
    · exact K.card_eq t
        (mem_of_mem_erase (mem_of_mem_erase (mem_of_mem_erase (mem_of_mem_erase ht))))

/-- After a 4-1 move, the 1-4 move with new vertex `E` applies. -/
theorem isMove14_move41 {K : Complex3 V} {A B C D E : V} (h : IsMove41 K A B C D E) :
    IsMove14 (move41 K h) A B C D E where
  hAB := h.hAB
  hAC := h.hAC
  hAD := h.hAD
  hAE := h.hAE
  hBC := h.hBC
  hBD := h.hBD
  hBE := h.hBE
  hCD := h.hCD
  hCE := h.hCE
  hDE := h.hDE
  mem := by simp [move41]
  fresh t ht hE := by
    simp only [move41, mem_insert, mem_erase] at ht
    rcases ht with rfl | ⟨h4, h3, h2, h1, ht⟩
    · simp [h.hAE.symm, h.hBE.symm, h.hCE.symm, h.hDE.symm] at hE
    · rcases h.star t ht hE with rfl | rfl | rfl | rfl
      exacts [h1 rfl, h2 rfl, h3 rfl, h4 rfl]

/-- **The 1-4 move undoes the 4-1 move.** -/
theorem move14_move41 {K : Complex3 V} {A B C D E : V} (h : IsMove41 K A B C D E) :
    move14 (move41 K h) (isMove14_move41 h) = K := by
  ext t
  simp only [move14, move41, mem_union, mem_insert, mem_singleton, mem_erase]
  constructor
  · rintro ((rfl | rfl | rfl | rfl) | ⟨hne, rfl | ⟨-, -, -, -, ht⟩⟩)
    · exact h.mem₁
    · exact h.mem₂
    · exact h.mem₃
    · exact h.mem₄
    · exact absurd rfl hne
    · exact ht
  · intro ht
    by_cases h1 : t = {A, B, C, E}
    · exact Or.inl (Or.inl h1)
    by_cases h2 : t = {A, B, D, E}
    · exact Or.inl (Or.inr (Or.inl h2))
    by_cases h3 : t = {A, C, D, E}
    · exact Or.inl (Or.inr (Or.inr (Or.inl h3)))
    by_cases h4 : t = {B, C, D, E}
    · exact Or.inl (Or.inr (Or.inr (Or.inr h4)))
    refine Or.inr ⟨?_, Or.inr ⟨h4, h3, h2, h1, ht⟩⟩
    rintro rfl
    exact h.fresh ht

/-- After a 1-4 move, the 4-1 move removing `E` applies. -/
theorem isMove41_move14 {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) :
    IsMove41 (move14 K h) A B C D E where
  hAB := h.hAB
  hAC := h.hAC
  hAD := h.hAD
  hAE := h.hAE
  hBC := h.hBC
  hBD := h.hBD
  hBE := h.hBE
  hCD := h.hCD
  hCE := h.hCE
  hDE := h.hDE
  mem₁ := by simp [move14]
  mem₂ := by simp [move14]
  mem₃ := by simp [move14]
  mem₄ := by simp [move14]
  star t ht hE := by
    simp only [move14, mem_union, mem_insert, mem_singleton, mem_erase] at ht
    rcases ht with (rfl | rfl | rfl | rfl) | ⟨-, ht⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact absurd hE (h.fresh t ht)
  fresh hm := by
    have hE : E ∉ ({A, B, C, D} : Finset V) := by
      simp [h.hAE.symm, h.hBE.symm, h.hCE.symm, h.hDE.symm]
    simp only [move14, mem_union, mem_insert, mem_singleton, mem_erase] at hm
    rcases hm with (h1 | h1 | h1 | h1) | ⟨hne, -⟩
    · exact hE (h1 ▸ by simp)
    · exact hE (h1 ▸ by simp)
    · exact hE (h1 ▸ by simp)
    · exact hE (h1 ▸ by simp)
    · exact hne rfl

/-- **The 4-1 move undoes the 1-4 move.** -/
theorem move41_move14 {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) :
    move41 (move14 K h) (isMove41_move14 h) = K := by
  have hnot : ∀ X Y Z : V, ({X, Y, Z, E} : Finset V) ∉ K.tets := fun X Y Z hm =>
    h.fresh _ hm (by simp)
  ext t
  simp only [move14, move41, mem_union, mem_insert, mem_singleton, mem_erase]
  constructor
  · rintro (rfl | ⟨h4, h3, h2, h1, (rfl | rfl | rfl | rfl) | ⟨-, ht⟩⟩)
    · exact h.mem
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h4
    · exact ht
  · intro ht
    by_cases h0 : t = {A, B, C, D}
    · exact Or.inl h0
    refine Or.inr ⟨?_, ?_, ?_, ?_, Or.inr ⟨h0, ht⟩⟩ <;>
    · rintro rfl
      exact hnot _ _ _ ht

/-- The edges after a 4-1 move: the old edges are those of the new complex together with the four
edges through `E`. -/
theorem edges_move41 {K : Complex3 V} {A B C D E : V} (h : IsMove41 K A B C D E) :
    K.edges = (move41 K h).edges ∪ {{A, E}, {B, E}, {C, E}, {D, E}} := by
  conv_lhs => rw [← move14_move41 h]
  exact edges_move14 _ (isMove14_move41 h)

/-- **The gauge-fixed amplitude is unchanged by a 4-1 move**, when `E` is attached to the gauge
set only by the gauge edge `DE`: the amplitude of `K` with gauge set `T ∪ {DE}` equals that of the
smaller complex with gauge set `T`, under the cutoff conditions of the 1-4 move. -/
theorem amplitudeGF_move41 (K : Complex3 V) {A B C D E : V} (h : IsMove41 K A B C D E)
    (T : Finset (Finset V)) (hT : T ⊆ K.edges) (hTE : ∀ e ∈ T, E ∉ e) (cut : Finset V → ℕ)
    (hA : cut {A, D} ≤ cut {A, E}) (hB : cut {B, D} ≤ cut {B, E})
    (hC : cut {C, D} ≤ cut {C, E}) :
    amplitudeGF (move41 K h) T cut = amplitudeGF K (insert {D, E} T) cut := by
  have hT' : T ⊆ (move41 K h).edges := by
    intro e he
    have he' := hT he
    rw [edges_move41 h, mem_union] at he'
    refine he'.resolve_right fun hm => hTE e he ?_
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simp
  have := amplitudeGF_move14 (move41 K h) (isMove14_move41 h) T hT' cut hA hB hC
  rw [move14_move41] at this
  exact this.symm

/-- A 4-1 move is a step of the chains in `amplitudeGF_eqvGen` (read backwards). -/
theorem gfStep_move41 {K : Complex3 V} {A B C D E : V} (h : IsMove41 K A B C D E)
    {T : Finset (Finset V)} (hT : T ⊆ K.edges) (hTE : ∀ e ∈ T, E ∉ e) {cut : Finset V → ℕ}
    (hA : cut {A, D} ≤ cut {A, E}) (hB : cut {B, D} ≤ cut {B, E})
    (hC : cut {C, D} ≤ cut {C, E}) :
    GFStep (move41 K h, T, cut) (K, insert {D, E} T, cut) := by
  have hT' : T ⊆ (move41 K h).edges := by
    intro e he
    have he' := hT he
    rw [edges_move41 h, mem_union] at he'
    refine he'.resolve_right fun hm => hTE e he ?_
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simp
  have := GFStep.move14 (isMove14_move41 h) hT' hA hB hC
  rwa [move14_move41] at this

end Lightlike.PR
