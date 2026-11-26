import Lightlike.PonzanoRegge.TriangulationIndependence.Rename

/-!
# Preparing the link of a vertex for the rename: stacking many tetrahedra at once

The rename of a vertex `v` by forward moves (`commonForward_rename_of_split`) needs the link of `v`
to split into two tree-shellable disks. The reduction that makes the link of `v` such a link starts
by stacking every tetrahedron through `v` with its own fresh vertex.

* `stackAll K S g`: every tetrahedron `t ∈ S` of `K` replaced by the four cones from the fresh
  vertex `g t` on the faces of `t`; `forwardMoves_stackAll`: it is reached by 1-4 moves.
-/

open Finset Lightlike.PL

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- A four-element set lists its elements. -/
lemma exists_four {t : Finset V} (ht : #t = 4) :
    ∃ A B C D : V, A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧ t = {A, B, C, D} := by
  obtain ⟨A, t', hA, rfl, ht'⟩ := card_eq_succ.1 ht
  obtain ⟨B, C, D, hBC, hBD, hCD, rfl⟩ := card_eq_three.1 ht'
  simp only [mem_insert, mem_singleton, not_or] at hA
  exact ⟨A, B, C, D, hA.1, hA.2.1, hA.2.2, hBC, hBD, hCD, rfl⟩

/-- The cones from `e` on the four faces of `t`. -/
def stackPieces (t : Finset V) (e : V) : Finset (Finset V) := t.image fun x => insert e (t.erase x)

/-- **All the tetrahedra of `S` stacked**: every `t ∈ S` replaced by the four cones from `g t` on
its faces. -/
def stackAll (K : Complex3 V) (S : Finset (Finset V)) (g : Finset V → V) : Complex3 V where
  tets := ((K.tets \ S) ∪ S.biUnion fun t => stackPieces t (g t)).filter (#· = 4)
  card_eq _ h := (mem_filter.1 h).2

/-- The conditions for stacking `S` with the labels `g`: `S` consists of tetrahedra of `K`, and the
labels are fresh and distinct. -/
structure StackData (K : Complex3 V) (S : Finset (Finset V)) (g : Finset V → V) : Prop where
  sub : S ⊆ K.tets
  fresh : ∀ t ∈ S, g t ∉ K.verts
  inj : ∀ s ∈ S, ∀ t ∈ S, g s = g t → s = t

lemma StackData.mono {K : Complex3 V} {S S' : Finset (Finset V)} {g : Finset V → V}
    (h : StackData K S g) (hS : S' ⊆ S) : StackData K S' g :=
  ⟨hS.trans h.sub, fun t ht => h.fresh t (hS ht), fun s hs t ht => h.inj s (hS hs) t (hS ht)⟩

lemma mem_stackPieces {t : Finset V} {e : V} {s : Finset V} :
    s ∈ stackPieces t e ↔ ∃ x ∈ t, insert e (t.erase x) = s := by
  simp [stackPieces]

lemma card_stackPiece {K : Complex3 V} {t : Finset V} (ht : t ∈ K.tets) {e : V}
    (he : e ∉ K.verts) {x : V} (hx : x ∈ t) : #(insert e (t.erase x)) = 4 := by
  have het : e ∉ t := fun h => he (mem_biUnion.2 ⟨t, ht, h⟩)
  rw [card_insert_of_notMem (fun h => het (mem_of_mem_erase h)), card_erase_of_mem hx,
    K.card_eq t ht]

/-- Membership in `stackAll`. -/
lemma StackData.mem_stackAll {K : Complex3 V} {S : Finset (Finset V)} {g : Finset V → V}
    (h : StackData K S g) {s : Finset V} :
    s ∈ (stackAll K S g).tets ↔ (s ∈ K.tets ∧ s ∉ S) ∨ ∃ t ∈ S, ∃ x ∈ t, insert (g t) (t.erase x) = s := by
  simp only [stackAll, mem_filter, mem_union, mem_sdiff, mem_biUnion, mem_stackPieces]
  constructor
  · rintro ⟨h1 | h1, -⟩
    · exact .inl h1
    · exact .inr h1
  · rintro (h1 | ⟨t, ht, x, hx, rfl⟩)
    · exact ⟨.inl h1, K.card_eq s h1.1⟩
    · exact ⟨.inr ⟨t, ht, x, hx, rfl⟩, card_stackPiece (h.sub ht) (h.fresh t ht) hx⟩

lemma complex3_eq' {K L : Complex3 V} (h : ∀ t, t ∈ K.tets ↔ t ∈ L.tets) : K = L := by
  cases K; cases L; congr; ext t; exact h t

/-- **Stacking a set of tetrahedra is a chain of 1-4 moves.** -/
theorem forwardMoves_stackAll {K : Complex3 V} {S : Finset (Finset V)} {g : Finset V → V}
    (h : StackData K S g) : ForwardMoves K (stackAll K S g) := by
  induction S using Finset.induction_on with
  | empty =>
    have : stackAll K ∅ g = K := complex3_eq' fun s => by
      rw [(h.mono (empty_subset _)).mem_stackAll]
      simp
    rw [this]
    exact .refl
  | @insert t S htS ih =>
    have hS := h.mono (subset_insert t S)
    have ht : t ∈ K.tets := h.sub (mem_insert_self t S)
    obtain ⟨A, B, C, D, hAB, hAC, hAD, hBC, hBD, hCD, rfl⟩ := exists_four (K.card_eq t ht)
    have hE := h.fresh _ (mem_insert_self _ S)
    set E := g {A, B, C, D} with hEdef
    have hEt : ∀ x ∈ ({A, B, C, D} : Finset V), E ≠ x := fun x hx e =>
      hE (e ▸ mem_biUnion.2 ⟨_, ht, hx⟩)
    have h14 : IsMove14 (stackAll K S g) A B C D E := by
      refine ⟨hAB, hAC, hAD, Ne.symm (hEt A (by simp)), hBC, hBD, Ne.symm (hEt B (by simp)), hCD,
        Ne.symm (hEt C (by simp)), Ne.symm (hEt D (by simp)), ?_, ?_⟩
      · rw [hS.mem_stackAll]; exact .inl ⟨ht, htS⟩
      · intro s hs hEs
        rw [hS.mem_stackAll] at hs
        rcases hs with ⟨hs, -⟩ | ⟨u, hu, x, hx, rfl⟩
        · exact hE (mem_biUnion.2 ⟨s, hs, hEs⟩)
        · rcases mem_insert.1 hEs with e | e
          · exact htS (h.inj _ (mem_insert_self _ S) u (mem_insert_of_mem hu) e ▸ hu)
          · exact hE (mem_biUnion.2 ⟨u, h.sub (mem_insert_of_mem hu), mem_of_mem_erase e⟩)
    suffices e : move14 (stackAll K S g) h14 = stackAll K (insert {A, B, C, D} S) g by
      rw [← e]; exact (ih hS).tail (.m14 h14)
    refine complex3_eq' fun s => ?_
    rw [h.mem_stackAll]
    simp only [move14, mem_union, mem_insert, mem_singleton, mem_erase, hS.mem_stackAll]
    have eA : insert E (({A, B, C, D} : Finset V).erase A) = {B, C, D, E} := by
      ext y; simp only [mem_insert, mem_erase, mem_singleton]; grind
    have eB : insert E (({A, B, C, D} : Finset V).erase B) = {A, C, D, E} := by
      ext y; simp only [mem_insert, mem_erase, mem_singleton]; grind
    have eC : insert E (({A, B, C, D} : Finset V).erase C) = {A, B, D, E} := by
      ext y; simp only [mem_insert, mem_erase, mem_singleton]; grind
    have eD : insert E (({A, B, C, D} : Finset V).erase D) = {A, B, C, E} := by
      ext y; simp only [mem_insert, mem_erase, mem_singleton]; grind
    have hne : ∀ u ∈ S, ∀ x ∈ u, insert (g u) (u.erase x) ≠ {A, B, C, D} := fun u hu x hx e => by
      have : g u ∈ ({A, B, C, D} : Finset V) := e ▸ mem_insert_self _ _
      exact h.fresh u (mem_insert_of_mem hu) (mem_biUnion.2 ⟨_, ht, this⟩)
    constructor
    · rintro ((rfl | rfl | rfl | rfl) | ⟨hsT, ⟨hs, hsS⟩ | ⟨u, hu, x, hx, rfl⟩⟩)
      · exact .inr ⟨_, .inl rfl, D, by simp, eD⟩
      · exact .inr ⟨_, .inl rfl, C, by simp, eC⟩
      · exact .inr ⟨_, .inl rfl, B, by simp, eB⟩
      · exact .inr ⟨_, .inl rfl, A, by simp, eA⟩
      · exact .inl ⟨hs, not_or.2 ⟨hsT, hsS⟩⟩
      · exact .inr ⟨u, .inr hu, x, hx, rfl⟩
    · rintro (⟨hs, hsS⟩ | ⟨u, hu, x, hx, rfl⟩)
      · rw [not_or] at hsS
        exact .inr ⟨hsS.1, .inl ⟨hs, hsS.2⟩⟩
      · rcases hu with rfl | hu
        · simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact .inl (.inr (.inr (.inr eA)))
          · exact .inl (.inr (.inr (.inl eB)))
          · exact .inl (.inr (.inl eC))
          · exact .inl (.inl eD)
        · exact .inr ⟨hne u hu x hx, .inr ⟨u, hu, x, hx, rfl⟩⟩

end Lightlike.PR
