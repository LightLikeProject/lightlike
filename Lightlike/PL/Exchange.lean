import Lightlike.PL.Links

/-!
# Stellar exchanges

Let `A` be a face of `K` whose link is a join `∂B * L`, where `B` is a nonempty simplex that is not
a face of `K` (Lickorish 1999, Definition 5.1). The **stellar exchange** `κ(A, B)` removes
`A * ∂B * L` and inserts `∂A * B * L`. For `L = {∅}` it is the bistellar move `κ(A, B)`; for a new
vertex `B = {a}` (so that `∂B = {∅}`) it is the stellar subdivision `(A, a)`. Exchanges are the
moves of the proof of Pachner's theorem (`Lightlike/PL/Pachner.lean`).

## Main results

* `exch_eq_bistellar`, `exch_eq_starAt`: bistellar moves and stellar subdivisions are exchanges.
* `isExch_exch`, `exch_exch`: `κ(B, A)` is defined after `κ(A, B)` and undoes it.
* `eq_of_link_eq`: a complex is determined by its faces without `B` and the link of `B`.
* `link_exch`: the link of `X` after an exchange at `X ∪ C` is the exchange at `C` of the link.
* `link_join_right`: the link of a face of the second factor of a join.
* `exch_join`: exchanges commute with joining a complex on other vertices.
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V : Type*} [DecidableEq V]

/-! ## Joins -/

/-- The join is associative. -/
lemma join_assoc (K L M : SComplex V) : (K.join L).join M = K.join (L.join M) := by
  refine ext_mem fun s => ?_
  simp only [mem_join]
  constructor
  · rintro ⟨_, ⟨t, ht, u, hu, rfl⟩, w, hw, rfl⟩
    exact ⟨t, ht, u ∪ w, ⟨u, hu, w, hw, rfl⟩, (union_assoc _ _ _).symm⟩
  · rintro ⟨t, ht, _, ⟨u, hu, w, hw, rfl⟩, rfl⟩
    exact ⟨t ∪ u, ⟨t, ht, u, hu, rfl⟩, w, hw, union_assoc _ _ _⟩

/-- **The link of a face of the second factor of a join**: for disjoint vertex sets and `σ ∈ L`,
`lk(σ, K * L) = K * lk(σ, L)`. -/
theorem link_join_right {K L : SComplex V} {σ : Finset V} (hKL : Disjoint K.verts L.verts)
    (hσ : σ ⊆ L.verts) : (K.join L).link σ = K.join (L.link σ) := by
  have hσK : Disjoint σ K.verts := disjoint_of_subset_left hσ hKL.symm
  have htσ : ∀ {t : Finset V}, t ∈ K → Disjoint t σ := fun ht =>
    disjoint_of_subset_left (subset_verts ht) hσK.symm
  refine ext_mem fun u => ?_
  rw [mem_link', mem_join, mem_join]
  constructor
  · rintro ⟨hd, t, ht, w, hw, he⟩
    have hσw : σ ⊆ w := fun x hx => by
      have : x ∈ t ∪ w := he.symm ▸ mem_union_left u hx
      rcases mem_union.1 this with h | h
      · exact absurd hx (disjoint_left.1 (htσ ht) h)
      · exact h
    refine ⟨t, ht, w \ σ, mem_link'.2 ⟨disjoint_sdiff, by rwa [union_sdiff_of_subset hσw]⟩, ?_⟩
    ext x
    have hx : x ∈ t ∪ w ↔ x ∈ σ ∪ u := by rw [he]
    simp only [mem_union, mem_sdiff] at hx ⊢
    have hxt : x ∈ t → x ∉ σ := fun h => disjoint_left.1 (htσ ht) h
    have hxu : x ∈ u → x ∉ σ := fun h h' => disjoint_left.1 hd h' h
    tauto
  · rintro ⟨t, ht, w, hw, rfl⟩
    obtain ⟨hσw, hσwL⟩ := mem_link'.1 hw
    refine ⟨disjoint_union_right.2 ⟨(htσ ht).symm, hσw⟩, t, ht, σ ∪ w, hσwL, ?_⟩
    rw [← union_assoc, union_comm t σ, union_assoc]

/-! ## Stellar exchanges -/

/-- Preconditions of the **stellar exchange** `κ(A, B)` of `K` with complementary link `L`: `A`
and `B` are nonempty and disjoint, `L` has a face and no vertex in `A ∪ B`, the link of `A` is
`∂B * L`, and `B` is not a face of `K`. -/
structure IsExch (K : SComplex V) (A B : Finset V) (L : SComplex V) : Prop where
  /-- The face being exchanged is nonempty. -/
  nonempty_left : A.Nonempty
  /-- The new face is nonempty. -/
  nonempty_right : B.Nonempty
  /-- The two faces are disjoint. -/
  disjoint : Disjoint A B
  /-- `L` has no vertex in `A`. -/
  disjoint_left_verts : Disjoint A L.verts
  /-- `L` has no vertex in `B`. -/
  disjoint_right_verts : Disjoint B L.verts
  /-- `L` has a face. -/
  empty_mem : ∅ ∈ L
  /-- The link of `A` is `∂B * L`. -/
  link_eq : K.link A = (boundary B).join L
  /-- `B` is not yet a face. -/
  notMem : B ∉ K

namespace IsExch

variable {K L : SComplex V} {A B : Finset V}

lemma empty_mem_boundary (h : IsExch K A B L) : ∅ ∈ boundary B :=
  mem_boundary.2 (Finset.ssubset_iff_subset_ne.2 ⟨empty_subset _, h.nonempty_right.ne_empty.symm⟩)

/-- Under the exchange conditions `A` is a face. -/
lemma mem (h : IsExch K A B L) : A ∈ K := by
  have : ∅ ∈ K.link A := by
    rw [h.link_eq]
    exact mem_join.2 ⟨∅, h.empty_mem_boundary, ∅, h.empty_mem, union_empty _⟩
  simpa using (mem_link.1 this).2.2

/-- No face of `K` contains `B`. -/
lemma not_subset (h : IsExch K A B L) {s : Finset V} (hs : s ∈ K) : ¬ B ⊆ s :=
  fun hB => h.notMem (down_mem hs hB)

/-- The faces of `K` containing `A` are the sets `A ∪ t ∪ u` with `t ⊂ B`, `u ∈ L`. -/
lemma subset_iff (h : IsExch K A B L) {s : Finset V} :
    s ∈ K ∧ A ⊆ s ↔ ∃ t ⊂ B, ∃ u ∈ L, A ∪ t ∪ u = s := by
  constructor
  · rintro ⟨hs, hA⟩
    have hl : s \ A ∈ K.link A :=
      mem_link'.2 ⟨disjoint_sdiff, by rwa [union_sdiff_of_subset hA]⟩
    rw [h.link_eq, mem_join] at hl
    obtain ⟨t, ht, u, hu, he⟩ := hl
    exact ⟨t, mem_boundary.1 ht, u, hu, by rw [union_assoc, he, union_sdiff_of_subset hA]⟩
  · rintro ⟨t, ht, u, hu, rfl⟩
    have hl : t ∪ u ∈ K.link A := by
      rw [h.link_eq]
      exact mem_join.2 ⟨t, mem_boundary.2 ht, u, hu, rfl⟩
    rw [union_assoc]
    exact ⟨(mem_link'.1 hl).2, subset_union_left⟩

end IsExch

/-- The **stellar exchange** `κ(A, B)`: remove the faces containing `A` (the star
`A * ∂B * L`) and add the faces `t ∪ B ∪ u` with `t ⊂ A`, `u ∈ L` (the star `∂A * B * L`). -/
def exch (K : SComplex V) (A B : Finset V) (L : SComplex V) (h : IsExch K A B L) :
    SComplex V where
  faces := K.faces.filter (fun s => ¬ A ⊆ s) ∪
    ((boundary A).faces ×ˢ L.faces).image fun p => p.1 ∪ B ∪ p.2
  down s hs r hr := by
    simp only [mem_union, mem_filter, mem_image, mem_product, Prod.exists, mem_faces,
      mem_boundary] at hs ⊢
    rcases hs with ⟨hs, hA⟩ | ⟨t, u, ⟨ht, hu⟩, rfl⟩
    · exact .inl ⟨down_mem hs hr, fun h' => hA (h'.trans hr)⟩
    · have hrsub : ∀ x ∈ r, x ∈ t ∨ x ∈ B ∨ x ∈ u := fun x hx => by
        have := hr hx
        simp only [mem_union] at this
        tauto
      by_cases hB : B ⊆ r
      · right
        refine ⟨r ∩ t, r ∩ u, ⟨inter_subset_right.trans_ssubset ht,
          down_mem hu inter_subset_right⟩, ?_⟩
        ext x
        simp only [mem_union, mem_inter]
        constructor
        · rintro ((⟨h₁, -⟩ | h₁) | ⟨h₁, -⟩)
          · exact h₁
          · exact hB h₁
          · exact h₁
        · intro hx
          rcases hrsub x hx with h' | h' | h'
          · exact .inl (.inl ⟨hx, h'⟩)
          · exact .inl (.inr h')
          · exact .inr ⟨hx, h'⟩
      · left
        have hw : (r ∩ B) ∪ (r ∩ u) ∈ K.link A := by
          rw [h.link_eq]
          refine mem_join.2 ⟨r ∩ B, mem_boundary.2 (Finset.ssubset_iff_subset_ne.2
            ⟨inter_subset_right, fun e => hB (e ▸ inter_subset_left)⟩), r ∩ u,
            down_mem hu inter_subset_right, rfl⟩
        have hAw := (mem_link'.1 hw).2
        obtain ⟨x, hxA, hxt⟩ := not_subset.1 ht.not_subset
        refine ⟨down_mem hAw fun y hy => ?_, fun h' => ?_⟩
        · rcases hrsub y hy with h'' | h'' | h''
          · exact mem_union_left _ (ht.subset h'')
          · exact mem_union_right _ (mem_union_left _ (mem_inter.2 ⟨hy, h''⟩))
          · exact mem_union_right _ (mem_union_right _ (mem_inter.2 ⟨hy, h''⟩))
        · rcases hrsub x (h' hxA) with h'' | h'' | h''
          · exact hxt h''
          · exact disjoint_left.1 h.disjoint hxA h''
          · exact disjoint_left.1 h.disjoint_left_verts hxA (subset_verts hu h'')

lemma exch_faces {K L : SComplex V} {A B : Finset V} (h : IsExch K A B L) :
    (exch K A B L h).faces = K.faces.filter (fun s => ¬ A ⊆ s) ∪
      ((boundary A).faces ×ˢ L.faces).image (fun p => p.1 ∪ B ∪ p.2) := rfl

lemma mem_exch {K L : SComplex V} {A B : Finset V} {h : IsExch K A B L} {s : Finset V} :
    s ∈ exch K A B L h ↔ (s ∈ K ∧ ¬ A ⊆ s) ∨ ∃ t ⊂ A, ∃ u ∈ L, t ∪ B ∪ u = s := by
  rw [← mem_faces, exch_faces]
  simp only [mem_union, mem_filter, mem_image, mem_product, Prod.exists, mem_faces, mem_boundary]
  constructor
  · rintro (h | ⟨t, u, ⟨ht, hu⟩, rfl⟩)
    · exact .inl h
    · exact .inr ⟨t, ht, u, hu, rfl⟩
  · rintro (h | ⟨t, ht, u, hu, rfl⟩)
    · exact .inl h
    · exact .inr ⟨t, u, ⟨ht, hu⟩, rfl⟩

/-- A face of the exchange without `B` is a face of `K` without `A`. -/
lemma mem_exch_of_not_subset {K L : SComplex V} {A B : Finset V} {h : IsExch K A B L}
    {s : Finset V} (hB : ¬ B ⊆ s) : s ∈ exch K A B L h ↔ s ∈ K ∧ ¬ A ⊆ s := by
  rw [mem_exch]
  refine ⟨fun h' => h'.elim id ?_, .inl⟩
  rintro ⟨t, -, u, -, rfl⟩
  exact absurd (subset_union_right.trans subset_union_left) hB

/-- **Bistellar moves are exchanges** with `L = {∅}`. -/
lemma IsBistellar.isExch {K : SComplex V} {A B : Finset V} (h : IsBistellar K A B) :
    IsExch K A B (simplex ∅) where
  nonempty_left := h.nonempty_left
  nonempty_right := h.nonempty_right
  disjoint := h.disjoint
  disjoint_left_verts := by rw [verts_simplex]; exact disjoint_empty_right _
  disjoint_right_verts := by rw [verts_simplex]; exact disjoint_empty_right _
  empty_mem := mem_simplex.2 (empty_subset _)
  link_eq := by rw [join_simplex_empty]; exact h.link_eq
  notMem := h.notMem

/-- The bistellar move `κ(A, B)` is the exchange `κ(A, B)` with complementary link `{∅}`. -/
lemma bistellar_eq_exch {K : SComplex V} {A B : Finset V} (h : IsBistellar K A B) :
    K.bistellar A B h = exch K A B (simplex ∅) h.isExch := by
  refine ext_mem fun s => ?_
  rw [mem_bistellar, mem_exch]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, ∅, mem_simplex.2 (empty_subset _), union_empty _⟩
  · rintro ⟨t, ht, u, hu, rfl⟩
    rw [mem_simplex, subset_empty] at hu
    exact ⟨t, ht, by rw [hu, union_empty]⟩

/-- An exchange with `L = {∅}` is a bistellar move. -/
lemma IsExch.isBistellar {K : SComplex V} {A B : Finset V} (h : IsExch K A B (simplex ∅)) :
    IsBistellar K A B where
  nonempty_left := h.nonempty_left
  nonempty_right := h.nonempty_right
  disjoint := h.disjoint
  link_eq := by rw [h.link_eq, join_simplex_empty]
  notMem := h.notMem

/-- **Stellar subdivisions are exchanges** with a new vertex `B = {a}` and `L = lk(A, K)`. -/
lemma isExch_starAt {K : SComplex V} {A : Finset V} {a : V} (hA : A ∈ K) (hne : A.Nonempty)
    (ha : a ∉ K.verts) : IsExch K A {a} (K.link A) where
  nonempty_left := hne
  nonempty_right := singleton_nonempty a
  disjoint := disjoint_singleton_right.2 (notMem_of_notMem_verts ha hA)
  disjoint_left_verts := disjoint_verts_link K A
  disjoint_right_verts := disjoint_singleton_left.2 fun h => ha (verts_link_subset K A h)
  empty_mem := mem_link'.2 ⟨disjoint_empty_right _, by rwa [union_empty]⟩
  link_eq := by rw [boundary_singleton, simplex_empty_join]
  notMem := fun h => ha (mem_verts.2 h)

/-- The stellar subdivision `(A, a)` is the exchange `κ(A, {a})` with complementary link
`lk(A, K)`. -/
lemma exch_eq_starAt {K : SComplex V} {A : Finset V} {a : V} (hA : A ∈ K) (hne : A.Nonempty)
    (ha : a ∉ K.verts) : exch K A {a} (K.link A) (isExch_starAt hA hne ha) = K.starAt A a := by
  refine ext_mem fun s => ?_
  rw [mem_exch, mem_starAt']
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨t, ht, u, hu, rfl⟩
    exact ⟨t ∪ u, mem_join.2 ⟨t, mem_boundary.2 ht, u, hu, rfl⟩, by
      rw [insert_eq, ← union_assoc, union_comm {a} t, union_assoc]⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨t, ht, u, hu, rfl⟩ := mem_join.1 hw
    exact ⟨t, mem_boundary.1 ht, u, hu, by rw [insert_eq, ← union_assoc, union_comm {a} t]⟩

/-- The link of `B` after the exchange is `∂A * L`. -/
theorem link_exch_right {K L : SComplex V} {A B : Finset V} (h : IsExch K A B L) :
    (exch K A B L h).link B = (boundary A).join L := by
  refine ext_mem fun u => ?_
  rw [mem_link', mem_exch, mem_join]
  constructor
  · rintro ⟨hd, ⟨hu, -⟩ | ⟨t, ht, w, hw, he⟩⟩
    · exact absurd subset_union_left (h.not_subset hu)
    · refine ⟨t, mem_boundary.2 ht, w, hw, ?_⟩
      -- remove `B` from both sides
      have e1 : (B ∪ u) \ B = u := by rw [union_sdiff_left, sdiff_eq_self_of_disjoint hd.symm]
      have hdt : Disjoint t B := disjoint_of_subset_left ht.subset h.disjoint
      have hdw : Disjoint w B := disjoint_of_subset_left (subset_verts hw) h.disjoint_right_verts.symm
      rw [← e1, ← he, union_sdiff_distrib, union_sdiff_distrib, sdiff_self, bot_eq_empty,
        union_empty, sdiff_eq_self_of_disjoint hdt, sdiff_eq_self_of_disjoint hdw]
  · rintro ⟨t, ht, w, hw, rfl⟩
    have hdt : Disjoint B t := disjoint_of_subset_right (mem_boundary.1 ht).subset h.disjoint.symm
    have hdw : Disjoint B w := disjoint_of_subset_right (subset_verts hw) h.disjoint_right_verts
    refine ⟨disjoint_union_right.2 ⟨hdt, hdw⟩, .inr ⟨t, mem_boundary.1 ht, w, hw, ?_⟩⟩
    rw [union_comm t B, union_assoc]

/-- **The inverse exchange is defined**: after `κ(A, B)`, the exchange `κ(B, A)` applies. -/
theorem isExch_exch {K L : SComplex V} {A B : Finset V} (h : IsExch K A B L) :
    IsExch (exch K A B L h) B A L where
  nonempty_left := h.nonempty_right
  nonempty_right := h.nonempty_left
  disjoint := h.disjoint.symm
  disjoint_left_verts := h.disjoint_right_verts
  disjoint_right_verts := h.disjoint_left_verts
  empty_mem := h.empty_mem
  link_eq := link_exch_right h
  notMem := by
    rw [mem_exch]
    rintro (⟨-, h'⟩ | ⟨t, -, u, -, he⟩)
    · exact h' subset_rfl
    · obtain ⟨b, hb⟩ := h.nonempty_right
      exact disjoint_left.1 h.disjoint (he ▸ mem_union_left _ (mem_union_right t hb)) hb

/-- **`κ(B, A)` undoes `κ(A, B)`.** -/
theorem exch_exch {K L : SComplex V} {A B : Finset V} (h : IsExch K A B L) :
    exch (exch K A B L h) B A L (isExch_exch h) = K := by
  refine ext_mem fun s => ?_
  rw [mem_exch]
  constructor
  · rintro (⟨hs, hB⟩ | ⟨t, ht, u, hu, rfl⟩)
    · exact ((mem_exch_of_not_subset hB).1 hs).1
    · exact (h.subset_iff.2 ⟨t, ht, u, hu, by rw [union_comm t A]⟩).1
  · intro hs
    by_cases hA : A ⊆ s
    · obtain ⟨t, ht, u, hu, rfl⟩ := h.subset_iff.1 ⟨hs, hA⟩
      exact .inr ⟨t, ht, u, hu, by rw [union_comm t A]⟩
    · exact .inl ⟨(mem_exch_of_not_subset (h.not_subset hs)).2 ⟨hs, hA⟩, h.not_subset hs⟩

/-- **A complex is determined by its faces without `B` and the link of `B`.** -/
theorem eq_of_link_eq {M N : SComplex V} {B : Finset V}
    (h₁ : ∀ s, ¬ B ⊆ s → (s ∈ M ↔ s ∈ N)) (h₂ : M.link B = N.link B) : M = N := by
  refine ext_mem fun s => ?_
  by_cases hB : B ⊆ s
  · have hM : s ∈ M ↔ s \ B ∈ M.link B := by
      rw [mem_link', union_sdiff_of_subset hB]
      exact ⟨fun h => ⟨disjoint_sdiff, h⟩, fun h => h.2⟩
    have hN : s ∈ N ↔ s \ B ∈ N.link B := by
      rw [mem_link', union_sdiff_of_subset hB]
      exact ⟨fun h => ⟨disjoint_sdiff, h⟩, fun h => h.2⟩
    rw [hM, hN, h₂]
  · exact h₁ s hB

/-! ## Links and joins of exchanges -/

/-- The exchange conditions pass to links. -/
lemma IsExch.link {K L : SComplex V} {X C D : Finset V} (h : IsExch K (X ∪ C) D L)
    (hXC : Disjoint X C) (hC : C.Nonempty) : IsExch (K.link X) C D L where
  nonempty_left := hC
  nonempty_right := h.nonempty_right
  disjoint := disjoint_of_subset_left subset_union_right h.disjoint
  disjoint_left_verts := disjoint_of_subset_left subset_union_right h.disjoint_left_verts
  disjoint_right_verts := h.disjoint_right_verts
  empty_mem := h.empty_mem
  link_eq := by rw [link_link K hXC, h.link_eq]
  notMem := fun hD => h.notMem (down_mem (mem_link'.1 hD).2 subset_union_right)

/-- **The link of `X` after an exchange at `X ∪ C`** is the exchange at `C` of the link of `X`
(for `X` disjoint from `C`, `D` and `L`). -/
theorem link_exch {K L : SComplex V} {X C D : Finset V} (h : IsExch K (X ∪ C) D L)
    (hXC : Disjoint X C) (hC : C.Nonempty) (hXD : Disjoint X D) (hXL : Disjoint X L.verts) :
    (exch K (X ∪ C) D L h).link X = exch (K.link X) C D L (h.link hXC hC) := by
  refine ext_mem fun u => ?_
  rw [mem_link', mem_exch, mem_exch, mem_link']
  constructor
  · rintro ⟨hd, ⟨hu, hXCu⟩ | ⟨t, ht, w, hw, he⟩⟩
    · refine .inl ⟨⟨hd, hu⟩, fun h' => hXCu (union_subset_union_right h')⟩
    · right
      -- `X` lies in `t`
      have hXt : X ⊆ t := fun x hx => by
        have : x ∈ t ∪ D ∪ w := he ▸ mem_union_left u hx
        rcases mem_union.1 this with h' | h'
        · rcases mem_union.1 h' with h'' | h''
          · exact h''
          · exact absurd h'' (disjoint_left.1 hXD hx)
        · exact absurd (subset_verts hw h') (disjoint_left.1 hXL hx)
      refine ⟨t \ X, ?_, w, hw, ?_⟩
      · refine Finset.ssubset_iff_subset_ne.2 ⟨fun x hx => ?_, fun e => ht.ne ?_⟩
        · rw [mem_sdiff] at hx
          rcases mem_union.1 (ht.subset hx.1) with h' | h'
          · exact absurd h' hx.2
          · exact h'
        · rw [← e, union_sdiff_of_subset hXt]
      · ext x
        have hx := congrArg (x ∈ ·) he
        simp only [mem_union, mem_sdiff, eq_iff_iff] at hx ⊢
        have hxu : x ∈ u → x ∉ X := fun h' h'' => disjoint_left.1 hd h'' h'
        have hxD : x ∈ D → x ∉ X := fun h' h'' => disjoint_left.1 hXD h'' h'
        have hxw : x ∈ w → x ∉ X := fun h' h'' => disjoint_left.1 hXL h'' (subset_verts hw h')
        tauto
  · rintro (⟨⟨hd, hu⟩, hCu⟩ | ⟨t, ht, w, hw, rfl⟩)
    · refine ⟨hd, .inl ⟨hu, fun h' => hCu fun x hx => ?_⟩⟩
      rcases mem_union.1 (h' (mem_union_right X hx)) with h'' | h''
      · exact absurd hx (disjoint_left.1 hXC h'')
      · exact h''
    · refine ⟨?_, .inr ⟨X ∪ t, ?_, w, hw, by rw [union_assoc X, union_assoc X, union_assoc]⟩⟩
      · refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨disjoint_of_subset_right
          ht.subset hXC, hXD⟩, hXL.mono_right (subset_verts hw)⟩
      · refine Finset.ssubset_iff_subset_ne.2 ⟨union_subset_union_right ht.subset, fun e => ht.ne ?_⟩
        have e' := congrArg (· \ X) e
        simp only [union_sdiff_left] at e'
        rwa [sdiff_eq_self_of_disjoint (disjoint_of_subset_left ht.subset hXC.symm),
          sdiff_eq_self_of_disjoint hXC.symm] at e'

/-- The join is commutative and associative: `P * (Q * R) = Q * (P * R)`. -/
lemma join_left_comm (P Q R : SComplex V) : P.join (Q.join R) = Q.join (P.join R) := by
  rw [← join_assoc, join_comm P Q, join_assoc]

/-- The exchange conditions pass to joins with a complex on other vertices. -/
lemma IsExch.join_left {P L L'' : SComplex V} {C D : Finset V} (h : IsExch L C D L'')
    (hP : ∅ ∈ P) (hPL : Disjoint P.verts L.verts) (hPD : Disjoint P.verts D) :
    IsExch (P.join L) C D (P.join L'') where
  nonempty_left := h.nonempty_left
  nonempty_right := h.nonempty_right
  disjoint := h.disjoint
  disjoint_left_verts := by
    refine disjoint_of_subset_right (verts_join_subset P L'') (disjoint_union_right.2 ⟨?_,
      h.disjoint_left_verts⟩)
    exact disjoint_of_subset_left (subset_verts h.mem) hPL.symm
  disjoint_right_verts := disjoint_of_subset_right (verts_join_subset P L'')
    (disjoint_union_right.2 ⟨hPD.symm, h.disjoint_right_verts⟩)
  empty_mem := mem_join.2 ⟨∅, hP, ∅, h.empty_mem, union_empty _⟩
  link_eq := by
    rw [link_join_right hPL (subset_verts h.mem), h.link_eq, join_left_comm]
  notMem := by
    rw [mem_join]
    rintro ⟨p, hp, l, hl, he⟩
    have hp0 : p = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      exact disjoint_left.1 hPD (subset_verts hp hx) (he ▸ mem_union_left l hx)
    rw [hp0, empty_union] at he
    exact h.notMem (he ▸ hl)

/-- **Exchanges commute with joins**: `κ(C, D)` on `P * L` is `P * κ(C, D) L`. -/
theorem exch_join {P L L'' : SComplex V} {C D : Finset V} (h : IsExch L C D L'')
    (hP : ∅ ∈ P) (hPL : Disjoint P.verts L.verts) (hPD : Disjoint P.verts D) :
    exch (P.join L) C D (P.join L'') (h.join_left hP hPL hPD) = P.join (exch L C D L'' h) := by
  have hCP : Disjoint C P.verts := disjoint_of_subset_left (subset_verts h.mem) hPL.symm
  refine ext_mem fun s => ?_
  rw [mem_exch, mem_join (K := P) (L := exch L C D L'' h)]
  constructor
  · rintro (⟨hs, hCs⟩ | ⟨t, ht, u, hu, rfl⟩)
    · obtain ⟨p, hp, l, hl, rfl⟩ := mem_join.1 hs
      exact ⟨p, hp, l, mem_exch.2 (.inl ⟨hl, fun h' => hCs (h'.trans subset_union_right)⟩), rfl⟩
    · obtain ⟨p, hp, w, hw, rfl⟩ := mem_join.1 hu
      refine ⟨p, hp, t ∪ D ∪ w, mem_exch.2 (.inr ⟨t, ht, w, hw, rfl⟩), ?_⟩
      ext x
      simp only [mem_union]
      tauto
  · rintro ⟨p, hp, w, hw, rfl⟩
    rcases mem_exch.1 hw with ⟨hl, hCl⟩ | ⟨t, ht, u, hu, rfl⟩
    · refine .inl ⟨mem_join.2 ⟨p, hp, w, hl, rfl⟩, fun h' => hCl fun x hx => ?_⟩
      rcases mem_union.1 (h' hx) with h'' | h''
      · exact absurd (subset_verts hp h'') (disjoint_left.1 hCP hx)
      · exact h''
    · refine .inr ⟨t, ht, p ∪ u, mem_join.2 ⟨p, hp, u, hu, rfl⟩, ?_⟩
      ext x
      simp only [mem_union]
      tauto

end SComplex

end Lightlike.PL
