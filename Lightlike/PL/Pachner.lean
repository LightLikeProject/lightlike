import Lightlike.PL.Exchange

/-!
# Pachner's theorem

**Pachner's theorem, stellar version**: closed combinatorial manifolds are stellar equivalent if
and only if they are related by bistellar moves. "Combinatorial manifold" is the stellar notion of
`Lightlike/PL/Manifold.lean` (every vertex link stellar equivalent to the boundary of a simplex;
Lickorish 1999, Definition 3.1). Lickorish's Theorem 5.9 (Newman, Pachner 1991) is the same
statement with "PL homeomorphic" in place of "stellar equivalent" and with the piecewise-linear
notion of combinatorial manifold (Definition 2.2). The two readings agree by Newman's theorem
(Lickorish §4), milestone PL4, which is not yet formalized; the version with PL homeomorphisms needs
it.

No renamings of the vertices (simplicial isomorphisms) are needed besides the moves: they are not
generators of stellar or bistellar equivalence here. A renaming of a closed combinatorial manifold
by a permutation, and more generally any isomorphism of complexes on `V`, is itself a composite of
bistellar moves (`IsClosedCombManifold.bistellarEquiv_map`, `bistellarEquiv_of_iso`).

Bistellar moves are stellar equivalences (`StellarEquiv.bistellar`). For the converse it suffices
to show that every stellar subdivision of a closed combinatorial manifold is a composite of
bistellar moves. A subdivision is the stellar exchange `κ(A, {a})` with complementary link
`lk(A, K)`, a PL sphere. Following Lickorish, all exchanges `κ(A, B)` whose link `∂B * S * L'`
is a join of a *standard sphere* `S = ∂C₁ * ⋯ * ∂C_k` with a PL sphere `L'` are shown to be
composites of bistellar moves, by induction on the dimension of `L'` and the number of stellar
moves relating `L'` to the boundary of a simplex.

The base case, where `L'` is absent (`lk(A, K) = ∂B * ∂C₁ * ⋯ * ∂C_k`), is treated without
shellings: if `C₁ = C' ∪ {c}`, the exchange `κ(A, B)` is the exchange `κ(A ∪ C', B)` (link
`∂B * ∂C₂ * ⋯`) followed by `κ(A, B ∪ {c})` (link `∂(B ∪ c) * ∂C' * ∂C₂ * ⋯`), and both are of
the same kind with smaller links (`exch_std_split`).

## Main results (this file)

* `BistellarEquivIn`, `BistellarEquiv`: bistellar equivalence (bistellar moves only), inside the
  vertex type and with an unlimited supply of new vertices; `BistellarEquiv.stellarEquiv`.
* `bistellarEquivIn_exch_std`: an exchange whose link is `∂B` joined with a standard sphere is a
  composite of bistellar moves.
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V : Type*} [DecidableEq V]

/-! ## Bistellar equivalence -/

/-- An elementary **bistellar step**: a bistellar move. -/
inductive BistellarStep : SComplex V → SComplex V → Prop
  /-- A bistellar move `κ(A, B)`. -/
  | bistellar {K : SComplex V} {A B : Finset V} (h : IsBistellar K A B) :
      BistellarStep K (K.bistellar A B h)

/-- `K` and `L` are **bistellar equivalent inside `V`**: related by a chain of bistellar moves
and their inverses, with vertices in `V`. -/
def BistellarEquivIn (K L : SComplex V) : Prop := Relation.EqvGen BistellarStep K L

/-- `K` and `L` are **bistellar equivalent**: their lifts to `V ⊕ ℕ` are bistellar equivalent
inside `V ⊕ ℕ` (an unlimited supply of new vertices). -/
def BistellarEquiv (K L : SComplex V) : Prop := BistellarEquivIn K.lift L.lift

namespace BistellarEquivIn

@[refl] lemma refl (K : SComplex V) : BistellarEquivIn K K := Relation.EqvGen.refl K

@[symm] lemma symm {K L : SComplex V} (h : BistellarEquivIn K L) : BistellarEquivIn L K :=
  Relation.EqvGen.symm _ _ h

@[trans] lemma trans {K L M : SComplex V} (h₁ : BistellarEquivIn K L)
    (h₂ : BistellarEquivIn L M) : BistellarEquivIn K M := Relation.EqvGen.trans _ _ _ h₁ h₂

/-- A bistellar move is a bistellar equivalence. -/
lemma bistellar {K : SComplex V} {A B : Finset V} (h : IsBistellar K A B) :
    BistellarEquivIn K (K.bistellar A B h) := Relation.EqvGen.rel _ _ (.bistellar h)

/-- An exchange with `L = {∅}` is a bistellar equivalence. -/
lemma exch_simplex_empty {K : SComplex V} {A B : Finset V} (h : IsExch K A B (simplex ∅)) :
    BistellarEquivIn K (exch K A B (simplex ∅) h) := by
  have := bistellar h.isBistellar
  rwa [bistellar_eq_exch] at this

/-- **Bistellar equivalence implies stellar equivalence** (inside an infinite type). -/
theorem stellarEquivIn [Infinite V] {K L : SComplex V} (h : BistellarEquivIn K L) :
    StellarEquivIn K L := by
  induction h with
  | rel K L h =>
    cases h with
    | bistellar h => exact StellarEquivIn.bistellar' h
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end BistellarEquivIn

/-- **Bistellar equivalence implies stellar equivalence.** -/
theorem BistellarEquiv.stellarEquiv {K L : SComplex V} (h : BistellarEquiv K L) :
    StellarEquiv K L :=
  BistellarEquivIn.stellarEquivIn h

/-! ## Exchanges with equal data -/

/-- Exchanges with equal data are equal (the proof argument does not matter). -/
lemma exch_congr {K K' L L' : SComplex V} {A B : Finset V} (hK : K = K') (hL : L = L')
    (h : IsExch K A B L) (h' : IsExch K' A B L') : exch K A B L h = exch K' A B L' h' := by
  subst hK hL
  rfl

/-! ## Standard spheres -/

/-- The **standard sphere** `∂C₁ * ⋯ * ∂C_k` of a list of vertex sets (`{∅}` for the empty
list). -/
def stdJoin : List (Finset V) → SComplex V
  | [] => simplex ∅
  | C :: Cs => (boundary C).join (stdJoin Cs)

/-- The vertices of all members of a list. -/
def suppList : List (Finset V) → Finset V
  | [] => ∅
  | C :: Cs => C ∪ suppList Cs

/-- The members are nonempty and pairwise disjoint. -/
def IsStdList : List (Finset V) → Prop
  | [] => True
  | C :: Cs => C.Nonempty ∧ Disjoint C (suppList Cs) ∧ IsStdList Cs

/-- The total number of vertices of the members. -/
def sizeList : List (Finset V) → ℕ
  | [] => 0
  | C :: Cs => #C + sizeList Cs

lemma empty_mem_stdJoin : ∀ {Cs : List (Finset V)}, IsStdList Cs → ∅ ∈ stdJoin Cs
  | [], _ => mem_simplex.2 (empty_subset _)
  | _ :: _, ⟨hC, _, hCs⟩ => mem_join.2 ⟨∅, mem_boundary.2 (Finset.ssubset_iff_subset_ne.2
      ⟨empty_subset _, hC.ne_empty.symm⟩), ∅, empty_mem_stdJoin hCs, union_empty _⟩

lemma verts_boundary_subset (C : Finset V) : (boundary C).verts ⊆ C := fun x hx =>
  (mem_boundary.1 (mem_verts.1 hx)).subset (mem_singleton_self x)

lemma verts_stdJoin_subset : ∀ Cs : List (Finset V), (stdJoin Cs).verts ⊆ suppList Cs
  | [] => by simp [stdJoin, suppList, verts_simplex]
  | C :: Cs => (verts_join_subset _ _).trans
      (union_subset_union (verts_boundary_subset C) (verts_stdJoin_subset Cs))

/-! ## The base case -/

/-- In `∂B * ∂(C' ∪ {c})`, the face `C'` has link `∂B`. -/
lemma isExch_boundary_join {B C' : Finset V} {c : V} (hc : c ∉ C') (hC' : C'.Nonempty)
    (hB : B.Nonempty) (hBC : Disjoint B (insert c C')) :
    IsExch ((boundary B).join (boundary (insert c C'))) C' B (simplex ∅) where
  nonempty_left := hC'
  nonempty_right := hB
  disjoint := disjoint_of_subset_right (subset_insert c C') hBC |>.symm
  disjoint_left_verts := by rw [verts_simplex]; exact disjoint_empty_right _
  disjoint_right_verts := by rw [verts_simplex]; exact disjoint_empty_right _
  empty_mem := mem_simplex.2 (empty_subset _)
  link_eq := by
    have h2 : 2 ≤ #(insert c C') := by
      rw [card_insert_of_notMem hc]; have := card_pos.2 hC'; omega
    rw [link_join_right (disjoint_of_subset_left (verts_boundary_subset B)
        (disjoint_of_subset_right (verts_boundary_subset _) hBC))
        (by rw [verts_boundary h2]; exact subset_insert c C'),
      link_boundary (ssubset_insert hc), insert_sdiff_of_notMem _ hc, sdiff_self, bot_eq_empty,
      insert_empty, boundary_singleton]
  notMem := by
    rw [mem_join]
    rintro ⟨p, hp, q, hq, he⟩
    rw [mem_boundary] at hp hq
    have hq0 : q = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      exact disjoint_left.1 hBC (he ▸ mem_union_right p hx) (hq.subset hx)
    rw [hq0, union_empty] at he
    exact hp.ne he

/-- **The key identity of the base case**: in `∂B * ∂(C' ∪ {c})`, the bistellar move `κ(C', B)`
gives `∂(B ∪ {c}) * ∂C'`. -/
theorem exch_boundary_join {B C' : Finset V} {c : V} (hc : c ∉ C')
    (hB : B.Nonempty) (hBC : Disjoint B (insert c C'))
    (h : IsExch ((boundary B).join (boundary (insert c C'))) C' B (simplex ∅)) :
    exch ((boundary B).join (boundary (insert c C'))) C' B (simplex ∅) h =
      (boundary (insert c B)).join (boundary C') := by
  have hcB : c ∉ B := fun h' => disjoint_left.1 hBC h' (mem_insert_self c C')
  have hBC' : Disjoint B C' := disjoint_of_subset_right (subset_insert c C') hBC
  refine ext_mem fun s => ?_
  rw [mem_exch, mem_join, mem_join]
  simp only [mem_boundary, mem_simplex, subset_empty]
  constructor
  · rintro (⟨⟨u, hu, v, hv, rfl⟩, hC's⟩ | ⟨t, ht, w, rfl, rfl⟩)
    · -- `u ⊂ B`, `v ⊂ C`, and `C' ⊄ u ∪ v`
      refine ⟨u ∪ (v ∩ {c}), ?_, v ∩ C', ?_, ?_⟩
      · obtain ⟨b, hbB, hbu⟩ := not_subset.1 hu.not_subset
        refine Finset.ssubset_iff_subset_ne.2 ⟨union_subset (hu.subset.trans (subset_insert c B))
          (fun x hx => by rw [mem_inter, mem_singleton] at hx; rw [hx.2]; exact mem_insert_self c B),
          fun e => ?_⟩
        have : b ∈ u ∪ (v ∩ {c}) := e ▸ mem_insert_of_mem hbB
        rcases mem_union.1 this with h' | h'
        · exact hbu h'
        · rw [mem_inter, mem_singleton] at h'
          exact hcB (h'.2 ▸ hbB)
      · refine Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_right, fun e => hC's ?_⟩
        rw [← e]
        exact inter_subset_left.trans subset_union_right
      · ext x
        have hxv : x ∈ v → x = c ∨ x ∈ C' := fun h' => mem_insert.1 (hv.subset h')
        simp only [mem_union, mem_inter, mem_singleton]
        tauto
    · refine ⟨B, ssubset_insert hcB, t, ht, ?_⟩
      rw [union_empty, union_comm]
  · rintro ⟨p, hp, q, hq, rfl⟩
    by_cases hBp : B ⊆ p
    · -- then `p = B`
      have hpB : p = B := by
        refine subset_antisymm (fun x hx => ?_) hBp
        rcases mem_insert.1 (hp.subset hx) with e | e
        · subst e
          exact absurd (subset_antisymm hp.subset (insert_subset hx hBp)) hp.ne
        · exact e
      subst hpB
      exact .inr ⟨q, hq, ∅, rfl, by rw [union_empty, union_comm]⟩
    · left
      obtain ⟨c', hc'C', hc'q⟩ := not_subset.1 hq.not_subset
      have hc'c : c' ≠ c := fun e => hc (e ▸ hc'C')
      refine ⟨⟨p ∩ B, Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_right,
        fun e => hBp (e ▸ inter_subset_left)⟩, (p \ B) ∪ q,
        Finset.ssubset_iff_subset_ne.2 ⟨union_subset (fun x hx => ?_)
          (hq.subset.trans (subset_insert c C')), fun e => ?_⟩, ?_⟩, ?_⟩
      · rw [mem_sdiff] at hx
        rcases mem_insert.1 (hp.subset hx.1) with h' | h'
        · rw [h']; exact mem_insert_self c C'
        · exact absurd h' hx.2
      · have : c' ∈ (p \ B) ∪ q := e ▸ mem_insert_of_mem hc'C'
        rcases mem_union.1 this with h' | h'
        · rw [mem_sdiff] at h'
          rcases mem_insert.1 (hp.subset h'.1) with h'' | h''
          · exact hc'c h''
          · exact h'.2 h''
        · exact hc'q h'
      · rw [← union_assoc, union_comm (p ∩ B), sdiff_union_inter]
      · intro h'
        rcases mem_union.1 (h' hc'C') with h'' | h''
        · rcases mem_insert.1 (hp.subset h'') with e | e
          · exact hc'c e
          · exact disjoint_left.1 hBC' e hc'C'
        · exact hc'q h''

/-- The key identity with an extra join factor `J`. -/
theorem exch_boundary_join_join {B C' : Finset V} {c : V} {J : SComplex V} (hc : c ∉ C')
    (hC' : C'.Nonempty) (hB : B.Nonempty) (hBC : Disjoint B (insert c C')) (hJ : ∅ ∈ J)
    (hJv : Disjoint J.verts (B ∪ insert c C'))
    (h : IsExch ((boundary B).join ((boundary (insert c C')).join J)) C' B J) :
    exch ((boundary B).join ((boundary (insert c C')).join J)) C' B J h =
      (boundary (insert c B)).join ((boundary C').join J) := by
  have h₀ := isExch_boundary_join hc hC' hB hBC
  have hJX : Disjoint J.verts ((boundary B).join (boundary (insert c C'))).verts :=
    disjoint_of_subset_right ((verts_join_subset _ _).trans
      (union_subset_union (verts_boundary_subset B) (verts_boundary_subset _))) hJv
  have hJB : Disjoint J.verts B := disjoint_of_subset_right subset_union_left hJv
  calc exch ((boundary B).join ((boundary (insert c C')).join J)) C' B J h
      = exch (J.join ((boundary B).join (boundary (insert c C')))) C' B (J.join (simplex ∅))
          (h₀.join_left hJ hJX hJB) :=
        exch_congr (by rw [join_comm J, join_assoc]) (by rw [join_simplex_empty]) _ _
    _ = J.join (exch _ C' B (simplex ∅) h₀) := exch_join h₀ hJ hJX hJB
    _ = J.join ((boundary (insert c B)).join (boundary C')) := by
        rw [exch_boundary_join hc hB hBC h₀]
    _ = (boundary (insert c B)).join ((boundary C').join J) := by
        rw [join_comm J, join_assoc]

/-- **Splitting an exchange whose link has a standard factor**: if `lk(A, K) = ∂B * ∂C * J` with
`C = C' ∪ {c}`, the exchange `κ(A, B)` is the exchange `κ(A ∪ C', B)` (complementary link `J`)
followed by `κ(A, B ∪ {c})` (complementary link `∂C' * J`). -/
theorem exch_std_split {K J : SComplex V} {A B C' : Finset V} {c : V}
    (hc : c ∉ C') (hcB : c ∉ B) (hAC' : Disjoint A C')
    (hBC' : Disjoint B C') (hAJ : Disjoint A J.verts) (hBJ : Disjoint B J.verts)
    (h : IsExch K A B ((boundary (insert c C')).join J)) (h₁ : IsExch K (A ∪ C') B J)
    (h₂ : IsExch (exch K (A ∪ C') B J h₁) A (insert c B) ((boundary C').join J)) :
    exch (exch K (A ∪ C') B J h₁) A (insert c B) ((boundary C').join J) h₂ =
      exch K A B ((boundary (insert c C')).join J) h := by
  apply eq_of_link_eq (B := B)
  · intro s hBs
    have hcBs : ¬ insert c B ⊆ s := fun h' => hBs ((subset_insert c B).trans h')
    rw [mem_exch_of_not_subset hcBs, mem_exch_of_not_subset hBs, mem_exch_of_not_subset hBs]
    constructor
    · rintro ⟨⟨hs, -⟩, hA⟩
      exact ⟨hs, hA⟩
    · rintro ⟨hs, hA⟩
      exact ⟨⟨hs, fun h' => hA (subset_union_left.trans h')⟩, hA⟩
  · rw [link_exch_right h]
    have hAB : Disjoint A B := h.disjoint
    refine ext_mem fun u => ?_
    rw [mem_link', mem_join]
    constructor
    · rintro ⟨hd, hu⟩
      rcases mem_exch.1 hu with ⟨hu₁, hA⟩ | ⟨t, ht, w, hw, he⟩
      · rcases mem_exch.1 hu₁ with ⟨hK, -⟩ | ⟨t, ht, w, hw, he⟩
        · exact absurd (subset_union_left) (h.not_subset hK)
        · have hwB : Disjoint w B := disjoint_of_subset_left (subset_verts hw) hBJ.symm
          have htB : Disjoint t B := disjoint_of_subset_left ht.subset
            (disjoint_union_left.2 ⟨hAB, hBC'.symm⟩)
          have hu' : u = t ∪ w := by
            ext x
            have hx := congrArg (x ∈ ·) he
            have h1 : x ∈ t → x ∉ B := fun h' => disjoint_left.1 htB h'
            have h2 : x ∈ w → x ∉ B := fun h' => disjoint_left.1 hwB h'
            have h3 : x ∈ u → x ∉ B := fun h' h'' => disjoint_left.1 hd h'' h'
            simp only [mem_union, eq_iff_iff] at hx ⊢
            tauto
          subst hu'
          have hAt : ¬ A ⊆ t := fun h' => hA (h'.trans (subset_union_left.trans subset_union_right))
          refine ⟨t ∩ A, mem_boundary.2 (Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_right,
            fun (e : t ∩ A = A) => hAt fun x hx => by
              rw [← e] at hx; exact (mem_inter.1 hx).1⟩), (t ∩ C') ∪ w, mem_join.2 ⟨t ∩ C',
            mem_boundary.2 ((inter_subset_right).trans_ssubset (ssubset_insert hc)), w, hw, rfl⟩, ?_⟩
          ext x
          have hxt : x ∈ t → x ∈ A ∨ x ∈ C' := fun h' => mem_union.1 (ht.subset h')
          simp only [mem_union, mem_inter]
          tauto
      · obtain ⟨q, hq, w', hw', rfl⟩ := mem_join.1 hw
        have hq' := mem_boundary.1 hq
        have hu' : u = t ∪ (insert c q ∪ w') := by
          have hnB : ∀ x, x ∈ t ∪ (insert c q ∪ w') → x ∉ B := by
            intro x hx hxB
            rcases mem_union.1 hx with h1 | h1
            · exact disjoint_left.1 hAB (ht.subset h1) hxB
            · rcases mem_union.1 h1 with h2 | h2
              · rcases mem_insert.1 h2 with h3 | h3
                · exact hcB (h3 ▸ hxB)
                · exact disjoint_left.1 hBC' hxB (hq'.subset h3)
              · exact disjoint_left.1 hBJ hxB (subset_verts hw' h2)
          have he' : t ∪ insert c B ∪ (q ∪ w') = B ∪ (t ∪ (insert c q ∪ w')) := by
            ext x
            simp only [mem_union, mem_insert]
            tauto
          rw [he'] at he
          ext x
          constructor
          · intro hx
            have : x ∈ B ∪ (t ∪ (insert c q ∪ w')) := he ▸ mem_union_right B hx
            rcases mem_union.1 this with h1 | h1
            · exact absurd h1 (disjoint_right.1 hd hx)
            · exact h1
          · intro hx
            have : x ∈ B ∪ u := he.symm ▸ mem_union_right B hx
            rcases mem_union.1 this with h1 | h1
            · exact absurd h1 (hnB x hx)
            · exact h1
        subst hu'
        refine ⟨t, mem_boundary.2 ht, insert c q ∪ w', mem_join.2 ⟨insert c q, mem_boundary.2 ?_,
          w', hw', rfl⟩, rfl⟩
        refine Finset.ssubset_iff_subset_ne.2 ⟨insert_subset_insert c hq'.subset, fun e => ?_⟩
        apply hq'.ne
        have hcq' : c ∉ q := fun h' => hc (hq'.subset h')
        calc q = (insert c q).erase c := (erase_insert hcq').symm
          _ = (insert c C').erase c := by rw [e]
          _ = C' := erase_insert hc
    · rintro ⟨p, hp₀, _, hqw, rfl⟩
      have hp := mem_boundary.1 hp₀
      obtain ⟨q, hq, w, hw, rfl⟩ := mem_join.1 hqw
      have hq' := mem_boundary.1 hq
      have hqC : ∀ x ∈ q, x = c ∨ x ∈ C' := fun x hx => mem_insert.1 (hq'.subset hx)
      have hdB : Disjoint B (p ∪ (q ∪ w)) := by
        refine disjoint_union_right.2 ⟨disjoint_of_subset_right hp.subset hAB.symm,
          disjoint_union_right.2 ⟨disjoint_left.2 fun x hxB hxq => ?_,
          disjoint_of_subset_right (subset_verts hw) hBJ⟩⟩
        rcases hqC x hxq with e | e
        · exact hcB (e ▸ hxB)
        · exact disjoint_left.1 hBC' hxB e
      refine ⟨hdB, ?_⟩
      by_cases hcq : c ∈ q
      · have hq'' : q.erase c ⊂ C' := by
          refine Finset.ssubset_iff_subset_ne.2 ⟨fun x hx => ?_, fun e => hq'.ne ?_⟩
          · rcases hqC x (mem_of_mem_erase hx) with e | e
            · exact absurd e (ne_of_mem_erase hx)
            · exact e
          · rw [← e, insert_erase hcq]
        refine mem_exch.2 (.inr ⟨p, hp, q.erase c ∪ w, mem_join.2 ⟨q.erase c, mem_boundary.2 hq'',
          w, hw, rfl⟩, ?_⟩)
        ext x
        have hx : x ∈ q ↔ x = c ∨ x ∈ q.erase c := by
          rw [mem_erase]
          constructor
          · intro h'
            by_cases e : x = c
            · exact .inl e
            · exact .inr ⟨e, h'⟩
          · rintro (e | ⟨-, h'⟩)
            · exact e ▸ hcq
            · exact h'
        simp only [mem_union, mem_insert] at hx ⊢
        tauto
      · have hqC' : q ⊆ C' := fun x hx => (hqC x hx).resolve_left fun e => hcq (e ▸ hx)
        refine mem_exch.2 (.inl ⟨mem_exch.2 (.inr ⟨p ∪ q, ?_, w, hw, ?_⟩), ?_⟩)
        · refine Finset.ssubset_iff_subset_ne.2 ⟨union_subset_union hp.subset hqC', fun e => ?_⟩
          obtain ⟨x, hxA, hxp⟩ := not_subset.1 hp.not_subset
          have : x ∈ p ∪ q := e ▸ mem_union_left C' hxA
          rcases mem_union.1 this with h1 | h1
          · exact hxp h1
          · exact disjoint_left.1 hAC' hxA (hqC' h1)
        · ac_rfl
        · intro hsub
          obtain ⟨x, hxA, hxp⟩ := not_subset.1 hp.not_subset
          rcases mem_union.1 (hsub hxA) with h1 | h1
          · exact disjoint_left.1 hAB hxA h1
          · rcases mem_union.1 h1 with h2 | h2
            · exact hxp h2
            · rcases mem_union.1 h2 with h3 | h3
              · exact disjoint_left.1 hAC' hxA (hqC' h3)
              · exact disjoint_left.1 hAJ hxA (subset_verts hw h3)

/-- With a face in the second factor, the vertices of the first factor are vertices of the join. -/
lemma verts_join_left_subset {K L : SComplex V} (hL : ∅ ∈ L) : K.verts ⊆ (K.join L).verts :=
  fun _ hx => mem_verts.2 (mem_join.2 ⟨_, mem_verts.1 hx, ∅, hL, union_empty _⟩)

/-- **The base case of Pachner's theorem**: an exchange `κ(A, B)` whose link is `∂B` joined with
a standard sphere `∂C₁ * ⋯ * ∂C_k` is a composite of bistellar moves. -/
theorem bistellarEquivIn_exch_std : ∀ (n : ℕ) (Cs : List (Finset V)), sizeList Cs = n →
    IsStdList Cs → ∀ (K : SComplex V) (A B : Finset V), Disjoint (A ∪ B) (suppList Cs) →
    ∀ h : IsExch K A B (stdJoin Cs), BistellarEquivIn K (exch K A B (stdJoin Cs) h) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Cs hn hstd K A B hdis h
  cases Cs with
  | nil => exact BistellarEquivIn.exch_simplex_empty h
  | cons C Cs' =>
    obtain ⟨hC, hCd, hCs'⟩ := hstd
    have hJ0 : ∅ ∈ stdJoin Cs' := empty_mem_stdJoin hCs'
    have hJv : (stdJoin Cs').verts ⊆ suppList Cs' := verts_stdJoin_subset Cs'
    simp only [suppList, sizeList] at hdis hn
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right] at hdis
    obtain ⟨⟨hAC, hAS⟩, hBC, hBS⟩ := hdis
    by_cases h1 : #C = 1
    · obtain ⟨c, rfl⟩ := card_eq_one.1 h1
      have hJeq : stdJoin ({c} :: Cs') = stdJoin Cs' := by
        change (boundary {c}).join (stdJoin Cs') = _
        rw [boundary_singleton, simplex_empty_join]
      have h' : IsExch K A B (stdJoin Cs') := hJeq ▸ h
      rw [exch_congr rfl hJeq h h']
      refine ih _ (by rw [card_singleton] at hn; omega) Cs' rfl hCs' K A B ?_ h'
      exact disjoint_union_left.2 ⟨hAS, hBS⟩
    · obtain ⟨c, hc⟩ := hC
      obtain ⟨C', hcC', rfl⟩ : ∃ C', c ∉ C' ∧ C = insert c C' :=
        ⟨C.erase c, notMem_erase c C, (insert_erase hc).symm⟩
      have hC'ne : C'.Nonempty := by
        rw [card_insert_of_notMem hcC'] at h1
        exact card_pos.1 (by omega)
      set J := stdJoin Cs' with hJdef
      change IsExch K A B ((boundary (insert c C')).join J) at h
      -- disjointness facts
      have hcA : c ∉ A := fun h' => disjoint_left.1 hAC h' (mem_insert_self c C')
      have hcB : c ∉ B := fun h' => disjoint_left.1 hBC h' (mem_insert_self c C')
      have hcJ : c ∉ J.verts := fun h' => disjoint_left.1 hCd (mem_insert_self c C') (hJv h')
      have hAC' : Disjoint A C' := disjoint_of_subset_right (subset_insert c C') hAC
      have hBC' : Disjoint B C' := disjoint_of_subset_right (subset_insert c C') hBC
      have hAJ : Disjoint A J.verts := disjoint_of_subset_right hJv hAS
      have hBJ : Disjoint B J.verts := disjoint_of_subset_right hJv hBS
      have hC'J : Disjoint C' J.verts :=
        disjoint_of_subset_right hJv (disjoint_of_subset_left (subset_insert c C') hCd)
      have hC'S : Disjoint C' (suppList Cs') := disjoint_of_subset_left (subset_insert c C') hCd
      have hcard2 : 2 ≤ #(insert c C') := by
        rw [card_insert_of_notMem hcC']; have := card_pos.2 hC'ne; omega
      -- the first exchange, at `A ∪ C'`
      have h₁ : IsExch K (A ∪ C') B J := {
        nonempty_left := h.nonempty_left.mono subset_union_left
        nonempty_right := h.nonempty_right
        disjoint := disjoint_union_left.2 ⟨h.disjoint, hBC'.symm⟩
        disjoint_left_verts := disjoint_union_left.2 ⟨hAJ, hC'J⟩
        disjoint_right_verts := hBJ
        empty_mem := hJ0
        link_eq := by
          have hv : (boundary (insert c C')).verts = insert c C' := verts_boundary hcard2
          rw [← link_link K hAC', h.link_eq,
            link_join_right (disjoint_of_subset_left (verts_boundary_subset B)
              (disjoint_of_subset_right (verts_join_subset _ _) (disjoint_union_right.2
                ⟨by rw [hv]; exact hBC, hBJ⟩)))
              ((by rw [hv]; exact subset_insert c C' : C' ⊆ (boundary (insert c C')).verts).trans
                (verts_join_left_subset hJ0)),
            join_comm (boundary (insert c C')),
            link_join_right (by rw [hv]; exact disjoint_comm.1 (disjoint_insert_left.2 ⟨hcJ, hC'J⟩))
              (by rw [hv]; exact subset_insert c C'),
            link_boundary (ssubset_insert hcC'), insert_sdiff_of_notMem _ hcC', sdiff_self,
            bot_eq_empty, insert_empty, boundary_singleton, join_simplex_empty]
        notMem := h.notMem }
      have IH1 : BistellarEquivIn K (exch K (A ∪ C') B J h₁) :=
        ih _ (by omega) Cs' rfl hCs' K (A ∪ C') B (disjoint_union_left.2
          ⟨disjoint_union_left.2 ⟨hAS, hC'S⟩, hBS⟩) h₁
      -- the second exchange, at `A` with `B ∪ {c}`
      have h₂ : IsExch (exch K (A ∪ C') B J h₁) A (insert c B) ((boundary C').join J) := {
        nonempty_left := h.nonempty_left
        nonempty_right := insert_nonempty c B
        disjoint := disjoint_insert_right.2 ⟨hcA, h.disjoint⟩
        disjoint_left_verts := disjoint_of_subset_right ((verts_join_subset _ _).trans
          (union_subset_union (verts_boundary_subset C') subset_rfl))
          (disjoint_union_right.2 ⟨hAC', hAJ⟩)
        disjoint_right_verts := disjoint_of_subset_right ((verts_join_subset _ _).trans
          (union_subset_union (verts_boundary_subset C') subset_rfl))
          (disjoint_union_right.2 ⟨disjoint_insert_left.2 ⟨hcC', hBC'⟩,
            disjoint_insert_left.2 ⟨hcJ, hBJ⟩⟩)
        empty_mem := mem_join.2 ⟨∅, mem_boundary.2 (Finset.ssubset_iff_subset_ne.2
          ⟨empty_subset _, hC'ne.ne_empty.symm⟩), ∅, hJ0, union_empty _⟩
        link_eq := by
          have hl := h₁.link hAC' hC'ne
          have hl' : IsExch ((boundary B).join ((boundary (insert c C')).join J)) C' B J :=
            h.link_eq ▸ hl
          rw [link_exch h₁ hAC' hC'ne h.disjoint hAJ, exch_congr h.link_eq rfl hl hl']
          exact exch_boundary_join_join hcC' hC'ne h.nonempty_right
            (disjoint_insert_right.2 ⟨hcB, hBC'⟩) hJ0
            (disjoint_comm.1 (disjoint_union_left.2 ⟨hBJ, disjoint_insert_left.2 ⟨hcJ, hC'J⟩⟩))
            hl'
        notMem := by
          rw [mem_exch]
          rintro (⟨hK, -⟩ | ⟨t, ht, w, hw, he⟩)
          · exact h.not_subset hK (subset_insert c B)
          · have : c ∈ t ∪ B ∪ w := he ▸ mem_insert_self c B
            rcases mem_union.1 this with h' | h'
            · rcases mem_union.1 h' with h'' | h''
              · rcases mem_union.1 (ht.subset h'') with h3 | h3
                · exact hcA h3
                · exact hcC' h3
              · exact hcB h''
            · exact hcJ (subset_verts hw h') }
      have IH2 : BistellarEquivIn (exch K (A ∪ C') B J h₁)
          (exch (exch K (A ∪ C') B J h₁) A (insert c B) ((boundary C').join J) h₂) :=
        ih _ (by simp only [sizeList]; rw [card_insert_of_notMem hcC'] at hn; omega) (C' :: Cs') rfl
          ⟨hC'ne, hC'S, hCs'⟩ _ A (insert c B) (by
            simp only [suppList]
            exact disjoint_union_left.2 ⟨disjoint_union_right.2 ⟨hAC', hAS⟩,
              disjoint_union_right.2 ⟨disjoint_insert_left.2 ⟨hcC', hBC'⟩,
                disjoint_insert_left.2 ⟨fun h' => disjoint_left.1 hCd (mem_insert_self c C') h',
                  hBS⟩⟩⟩) h₂
      rw [exch_std_split hcC' hcB hAC' hBC' hAJ hBJ h h₁ h₂] at IH2
      exact IH1.trans IH2

end SComplex

end Lightlike.PL
