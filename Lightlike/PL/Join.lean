import Lightlike.PL.Manifold

/-!
# Joins with spheres and balls

The link of the new vertex of a stellar subdivision `(A, a) K` is the join `∂A * lk(A, K)`. To
show that stellar moves preserve combinatorial manifolds (`Lightlike/PL/Links.lean`) we need that
the join of `∂A` with a PL sphere or ball is again a PL sphere or ball. This file proves it, inside
an infinite vertex type.

## Main results

* `join_starAt`: a subdivision of `K` gives a subdivision of `K * J`, when the vertex sets are
  disjoint.
* `StellarEquivIn.exists_avoiding`: a chain of stellar moves between two complexes can be chosen to
  avoid any finite set of vertices that the two complexes avoid (renaming its intermediate
  vertices by a permutation that fixes the end points).
* `StellarEquivIn.join_right`: stellar equivalence is compatible with joining a fixed complex.
* `exists_perm_map_eq`: two finite sets of the same size are related by a permutation; hence the
  model simplex of a PL sphere or ball can be chosen disjoint from any finite set.
* `starAt_boundary_eq_join`, `starAt_simplex_eq_join`: `∂(A ∪ x) * ∂B` and `Δ(A ∪ x) * ∂B` are
  subdivisions of `∂(A ∪ B)` and `Δ(A ∪ B)`.
* `IsSB.boundary_join`: the join of `∂A` with a PL `(m−1)`-sphere (or ball) is a PL
  `(m + #A − 2)`-sphere (or ball).
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V : Type*} [DecidableEq V]

/-! ## Joins and subdivisions -/

/-- `{∅}` is a unit for the join. -/
lemma join_simplex_empty (K : SComplex V) : K.join (simplex ∅) = K := ext_mem fun s => by
  rw [mem_join]
  constructor
  · rintro ⟨t, ht, u, hu, rfl⟩
    rw [mem_simplex, subset_empty] at hu
    rwa [hu, union_empty]
  · intro hs
    exact ⟨s, hs, ∅, mem_simplex.2 (empty_subset _), union_empty s⟩

/-- `{∅}` is a unit for the join. -/
lemma simplex_empty_join (K : SComplex V) : (simplex ∅).join K = K := by
  rw [join_comm, join_simplex_empty]

/-- The vertices of a join are vertices of the factors. -/
lemma verts_join_subset (K L : SComplex V) : (K.join L).verts ⊆ K.verts ∪ L.verts := by
  intro x hx
  obtain ⟨t, ht, u, hu, he⟩ := mem_join.1 (mem_verts.1 hx)
  have : x ∈ t ∪ u := he ▸ mem_singleton_self x
  rcases mem_union.1 this with h | h
  · exact mem_union_left _ (subset_verts ht h)
  · exact mem_union_right _ (subset_verts hu h)

/-- **Subdivision commutes with joins**: for `K`, `J` with disjoint vertex sets, `A` disjoint from
the vertices of `J`, `((A, a) K) * J = (A, a) (K * J)`. -/
theorem join_starAt {K J : SComplex V} {A : Finset V} {a : V} (hKJ : Disjoint K.verts J.verts)
    (hAJ : Disjoint A J.verts) :
    (K.starAt A a).join J = (K.join J).starAt A a := by
  -- a face of `K * J` determines its two parts
  have hpart : ∀ {t u : Finset V}, t ∈ K → u ∈ J → (t ∪ u) \ J.verts = t := by
    intro t u ht hu
    rw [union_sdiff_distrib, sdiff_eq_empty_iff_subset.2 (subset_verts hu), union_empty,
      sdiff_eq_self_of_disjoint (disjoint_of_subset_left (subset_verts ht) hKJ)]
  refine ext_mem fun s => ?_
  rw [mem_join, mem_starAt]
  constructor
  · rintro ⟨t, ht, u, hu, rfl⟩
    rcases mem_starAt.1 ht with ⟨ht, hAt⟩ | ⟨t', ht', hAt', hAt'K, rfl⟩
    · refine .inl ⟨mem_join.2 ⟨t, ht, u, hu, rfl⟩, fun h => hAt fun x hx => ?_⟩
      rcases mem_union.1 (h hx) with h' | h'
      · exact h'
      · exact absurd (subset_verts hu h') (disjoint_left.1 hAJ hx)
    · refine .inr ⟨t' ∪ u, mem_join.2 ⟨t', ht', u, hu, rfl⟩, fun h => hAt' fun x hx => ?_,
        mem_join.2 ⟨A ∪ t', hAt'K, u, hu, (union_assoc _ _ _)⟩, (insert_union a t' u).symm⟩
      rcases mem_union.1 (h hx) with h' | h'
      · exact h'
      · exact absurd (subset_verts hu h') (disjoint_left.1 hAJ hx)
  · rintro (⟨hs, hAs⟩ | ⟨r, hr, hAr, hAr', rfl⟩)
    · obtain ⟨t, ht, u, hu, rfl⟩ := mem_join.1 hs
      exact ⟨t, mem_starAt.2 (.inl ⟨ht, fun h => hAs (h.trans subset_union_left)⟩), u, hu, rfl⟩
    · obtain ⟨t, ht, u, hu, rfl⟩ := mem_join.1 hr
      obtain ⟨t'', ht'', u'', hu'', he⟩ := mem_join.1 hAr'
      have hAt : A ∪ t ∈ K := by
        have e1 : (A ∪ (t ∪ u)) \ J.verts = A ∪ t := by
          rw [← union_assoc, union_sdiff_distrib, sdiff_eq_empty_iff_subset.2 (subset_verts hu),
            union_empty, sdiff_eq_self_of_disjoint]
          rw [disjoint_union_left]
          exact ⟨hAJ, disjoint_of_subset_left (subset_verts ht) hKJ⟩
        rw [← e1, ← he, hpart ht'' hu'']
        exact ht''
      refine ⟨insert a t, mem_starAt.2 (.inr ⟨t, ht, fun h => hAr (h.trans subset_union_left),
        hAt, rfl⟩), u, hu, (insert_union a t u)⟩

/-! ## Chains of stellar moves avoiding a finite set -/

/-- A stellar step between complexes whose vertices lie in `U`. -/
def StepWithin (U : Finset V) (K L : SComplex V) : Prop :=
  StellarStep K L ∧ K.verts ⊆ U ∧ L.verts ⊆ U

/-- Every stellar equivalence inside `V` is a chain of steps within some finite set. -/
lemma StellarEquivIn.exists_within {K L : SComplex V} (h : StellarEquivIn K L) :
    ∃ U : Finset V, Relation.EqvGen (StepWithin U) K L := by
  have mono : ∀ {U U' : Finset V}, U ⊆ U' → ∀ {X Y : SComplex V},
      Relation.EqvGen (StepWithin U) X Y → Relation.EqvGen (StepWithin U') X Y :=
    fun hUU' X Y h => Relation.EqvGen.mono (fun _ _ h' => ⟨h'.1, h'.2.1.trans hUU',
      h'.2.2.trans hUU'⟩) X Y h
  induction h with
  | rel K L h => exact ⟨K.verts ∪ L.verts, .rel _ _ ⟨h, subset_union_left, subset_union_right⟩⟩
  | refl K => exact ⟨∅, .refl _⟩
  | symm _ _ _ ih =>
    obtain ⟨U, hU⟩ := ih
    exact ⟨U, hU.symm⟩
  | trans _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨U₁, h₁⟩ := ih₁
    obtain ⟨U₂, h₂⟩ := ih₂
    exact ⟨U₁ ∪ U₂, (mono subset_union_left h₁).trans _ _ _ (mono subset_union_right h₂)⟩

/-- Steps within `U` are transported by injective maps of the vertices. -/
lemma StepWithin.map {U : Finset V} {K L : SComplex V} (h : StepWithin U K L) (f : V ↪ V) :
    StepWithin (U.map f) (K.map f) (L.map f) := by
  obtain ⟨⟨hA, hne, ha⟩, hK, hL⟩ := h
  refine ⟨?_, by rw [verts_map]; exact Finset.map_subset_map.2 hK,
    by rw [verts_map]; exact Finset.map_subset_map.2 hL⟩
  rw [map_starAt]
  refine .starAt (map_mem_map.2 hA) hne.map ?_
  rw [verts_map, Finset.mem_map' f]
  exact ha

lemma eqvGen_stepWithin_map {U : Finset V} {K L : SComplex V}
    (h : Relation.EqvGen (StepWithin U) K L) (f : V ↪ V) :
    Relation.EqvGen (StepWithin (U.map f)) (K.map f) (L.map f) := by
  induction h with
  | rel K L h => exact .rel _ _ (h.map f)
  | refl K => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂

/-- A swap of two vertices outside `K` fixes `K`. -/
lemma map_swap_eq_self {K : SComplex V} {x y : V} (hx : x ∉ K.verts) (hy : y ∉ K.verts) :
    K.map (Equiv.swap x y).toEmbedding = K := by
  rw [map_congr (g := Function.Embedding.refl V), map_refl]
  intro v hv
  have hvx : v ≠ x := fun e => hx (e ▸ hv)
  have hvy : v ≠ y := fun e => hy (e ▸ hv)
  simp [Equiv.swap_apply_of_ne_of_ne hvx hvy]

/-- **Chains can avoid a finite set.** If `K` and `L` are stellar equivalent inside an infinite
type and both avoid the finite set `S`, there is a chain of steps between them all of whose
vertices avoid `S`. -/
theorem StellarEquivIn.exists_avoiding [Infinite V] {K L : SComplex V} (h : StellarEquivIn K L)
    (S : Finset V) (hK : Disjoint K.verts S) (hL : Disjoint L.verts S) :
    ∃ U : Finset V, Disjoint U S ∧ K.verts ⊆ U ∧ Relation.EqvGen (StepWithin U) K L := by
  obtain ⟨U₀, h₀⟩ := h.exists_within
  suffices H : ∀ n, ∀ U : Finset V, #(U ∩ S) = n → K.verts ⊆ U → L.verts ⊆ U →
      Relation.EqvGen (StepWithin U) K L →
      ∃ U' : Finset V, Disjoint U' S ∧ K.verts ⊆ U' ∧ Relation.EqvGen (StepWithin U') K L by
    refine H _ (U₀ ∪ K.verts ∪ L.verts) rfl (subset_union_right.trans subset_union_left)
      subset_union_right (Relation.EqvGen.mono (fun _ _ h' => ⟨h'.1,
        h'.2.1.trans (subset_union_left.trans subset_union_left),
        h'.2.2.trans (subset_union_left.trans subset_union_left)⟩) _ _ h₀)
  intro n
  induction n with
  | zero =>
    intro U hU hKU _ hch
    exact ⟨U, disjoint_iff_inter_eq_empty.2 (card_eq_zero.1 hU), hKU, hch⟩
  | succ n ih =>
    intro U hU hKU hLU hch
    obtain ⟨t, ht⟩ : (U ∩ S).Nonempty := card_pos.1 (by omega)
    obtain ⟨htU, htS⟩ := mem_inter.1 ht
    obtain ⟨f, hf⟩ := Infinite.exists_notMem_finset (U ∪ S)
    rw [mem_union, not_or] at hf
    have htK : t ∉ K.verts := fun h' => disjoint_left.1 hK h' htS
    have htL : t ∉ L.verts := fun h' => disjoint_left.1 hL h' htS
    have hfK : f ∉ K.verts := fun h' => hf.1 (hKU h')
    have hfL : f ∉ L.verts := fun h' => hf.1 (hLU h')
    have hch' := eqvGen_stepWithin_map hch (Equiv.swap t f).toEmbedding
    rw [map_swap_eq_self htK hfK, map_swap_eq_self htL hfL] at hch'
    -- the new set of vertices replaces `t` by `f`
    have hU' : U.map (Equiv.swap t f).toEmbedding = insert f (U.erase t) := by
      ext z
      rw [Finset.mem_map_equiv, Equiv.symm_swap, mem_insert, mem_erase]
      have htf : t ≠ f := fun e => hf.1 (e ▸ htU)
      by_cases hzt : z = t
      · subst hzt
        simp [Equiv.swap_apply_left, hf.1, htf]
      · by_cases hzf : z = f
        · subst hzf
          simp [Equiv.swap_apply_right, htU]
        · simp [Equiv.swap_apply_of_ne_of_ne hzt hzf, hzt, hzf]
    rw [hU'] at hch'
    refine ih _ ?_ ?_ ?_ hch'
    · have : insert f (U.erase t) ∩ S = (U ∩ S).erase t := by
        ext z
        simp only [mem_inter, mem_insert, mem_erase]
        constructor
        · rintro ⟨h₁ | ⟨h₁, h₂⟩, h₃⟩
          · exact absurd (h₁ ▸ h₃) hf.2
          · exact ⟨h₁, h₂, h₃⟩
        · rintro ⟨h₁, h₂, h₃⟩
          exact ⟨.inr ⟨h₁, h₂⟩, h₃⟩
      rw [this, card_erase_of_mem ht, hU]
      rfl
    · intro x hx
      exact mem_insert_of_mem (mem_erase.2 ⟨fun e => htK (e ▸ hx), hKU hx⟩)
    · intro x hx
      exact mem_insert_of_mem (mem_erase.2 ⟨fun e => htL (e ▸ hx), hLU hx⟩)

/-- One subdivision step, joined with `J`. -/
lemma join_step {X J : SComplex V} {A : Finset V} {a : V} (hA : A ∈ X) (hne : A.Nonempty)
    (ha : a ∉ X.verts) (hJ : ∅ ∈ J) (hXJ : Disjoint X.verts J.verts) (haJ : a ∉ J.verts) :
    StellarEquivIn (X.join J) ((X.starAt A a).join J) := by
  rw [join_starAt hXJ (disjoint_of_subset_left (subset_verts hA) hXJ)]
  refine StellarEquivIn.starAt (mem_join.2 ⟨_, hA, ∅, hJ, union_empty _⟩) hne ?_
  intro h'
  rcases mem_union.1 (verts_join_subset X J h') with h'' | h''
  · exact ha h''
  · exact haJ h''

/-- Along a chain of steps within `U`, a complex has its vertices in `U` exactly when the other
end does. -/
lemma verts_subset_iff_of_eqvGen {U : Finset V} {X Y : SComplex V}
    (h : Relation.EqvGen (StepWithin U) X Y) : X.verts ⊆ U ↔ Y.verts ⊆ U := by
  induction h with
  | rel X Y h => exact ⟨fun _ => h.2.2, fun _ => h.2.1⟩
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Stellar equivalence is compatible with joins**: if `L ∼ L'` inside an infinite type, and `J`
has a face and no vertex in common with `L` or `L'`, then `L * J ∼ L' * J`. -/
theorem StellarEquivIn.join_right [Infinite V] {L L' J : SComplex V} (h : StellarEquivIn L L')
    (hJ : ∅ ∈ J) (hL : Disjoint L.verts J.verts) (hL' : Disjoint L'.verts J.verts) :
    StellarEquivIn (L.join J) (L'.join J) := by
  obtain ⟨U, hUJ, hLU, hch⟩ := h.exists_avoiding J.verts hL hL'
  have key : ∀ X Y : SComplex V, Relation.EqvGen (StepWithin U) X Y → X.verts ⊆ U →
      StellarEquivIn (X.join J) (Y.join J) := by
    intro X Y hXY
    induction hXY with
    | rel X Y hXY =>
      intro _
      obtain ⟨hst, hXU, hYU⟩ := hXY
      cases hst with
      | starAt hA hne ha =>
        have hXJ : Disjoint X.verts J.verts := disjoint_of_subset_left hXU hUJ
        exact join_step hA hne ha hJ hXJ
          (fun h' => disjoint_left.1 hUJ (hYU (apex_mem_verts hA hne)) h')
    | refl => exact fun _ => .refl _
    | symm X Y hXY ih =>
      intro hY
      exact (ih ((verts_subset_iff_of_eqvGen hXY).2 hY)).symm
    | trans X Y Z hXY _ ih₁ ih₂ =>
      intro hX
      exact (ih₁ hX).trans (ih₂ ((verts_subset_iff_of_eqvGen hXY).1 hX))
  exact key _ _ hch hLU

/-! ## Moving the model simplex -/

/-- **Two finite sets of the same size are related by a permutation** of `V` (a product of swaps). -/
theorem exists_perm_map_eq {s t : Finset V} (h : #s = #t) :
    ∃ σ : Equiv.Perm V, s.map σ.toEmbedding = t := by
  suffices H : ∀ n, ∀ s : Finset V, #s = #t → #(s \ t) = n →
      ∃ σ : Equiv.Perm V, s.map σ.toEmbedding = t from H _ s h rfl
  intro n
  induction n with
  | zero =>
    intro s hs hn
    have hst : s ⊆ t := sdiff_eq_empty_iff_subset.1 (card_eq_zero.1 hn)
    refine ⟨Equiv.refl V, ?_⟩
    rw [eq_of_subset_of_card_le hst hs.ge]
    ext z; simp
  | succ n ih =>
    intro s hs hn
    obtain ⟨x, hx⟩ : (s \ t).Nonempty := card_pos.1 (by omega)
    have hcard : #(t \ s) = #(s \ t) := by
      have h1 := card_sdiff_add_card_inter s t
      have h2 := card_sdiff_add_card_inter t s
      rw [inter_comm] at h2
      omega
    obtain ⟨y, hy⟩ : (t \ s).Nonempty := card_pos.1 (by omega)
    rw [mem_sdiff] at hx hy
    have hs' : s.map (Equiv.swap x y).toEmbedding = insert y (s.erase x) := by
      rw [map_swap_face hy.2, ite_eq_left hx.1]
    have hn' : #(insert y (s.erase x) \ t) = n := by
      have : insert y (s.erase x) \ t = (s \ t).erase x := by
        ext z
        simp only [mem_sdiff, mem_insert, mem_erase]
        constructor
        · rintro ⟨h₁ | ⟨h₁, h₂⟩, h₃⟩
          · exact absurd (h₁ ▸ hy.1) h₃
          · exact ⟨h₁, h₂, h₃⟩
        · rintro ⟨h₁, h₂, h₃⟩
          exact ⟨.inr ⟨h₁, h₂⟩, h₃⟩
      rw [this, card_erase_of_mem (mem_sdiff.2 hx), hn]
      rfl
    have hc : #(insert y (s.erase x)) = #t := by rw [← hs', card_map, hs]
    obtain ⟨σ, hσ⟩ := ih _ hc hn'
    refine ⟨(Equiv.swap x y).trans σ, ?_⟩
    rw [← hσ, ← hs', Finset.map_map]
    rfl

/-- An infinite type has finite sets of every size avoiding a given finite set. -/
lemma exists_card_disjoint [Infinite V] (T : Finset V) (m : ℕ) :
    ∃ B : Finset V, #B = m ∧ Disjoint B T := by
  obtain ⟨u, hTu, hu⟩ := Infinite.exists_superset_card_eq T (#T + m) (by omega)
  refine ⟨u \ T, ?_, sdiff_disjoint⟩
  rw [card_sdiff_of_subset hTu, hu]
  omega

/-- Boundaries of simplices of the same size are stellar equivalent (they are isomorphic). -/
lemma StellarEquivIn.boundary_of_card [Infinite V] {A B : Finset V} (h : #A = #B) :
    StellarEquivIn (boundary A) (boundary B) := by
  obtain ⟨σ, hσ⟩ := exists_perm_map_eq h
  have := StellarEquivIn.map_perm (boundary A) σ
  rwa [map_boundary, hσ] at this

/-- Simplices of the same size are stellar equivalent (they are isomorphic). -/
lemma StellarEquivIn.simplex_of_card [Infinite V] {A B : Finset V} (h : #A = #B) :
    StellarEquivIn (simplex A) (simplex B) := by
  obtain ⟨σ, hσ⟩ := exists_perm_map_eq h
  have := StellarEquivIn.map_perm (simplex A) σ
  rwa [map_simplex, hσ] at this

/-! ## Joins of models -/

/-- **`∂(A' ∪ {x}) * ∂B` is a subdivision of `∂(A' ∪ B)`**: star `∂(A' ∪ B)` at `B` with the new
vertex `x`. -/
theorem starAt_boundary_eq_join {A' B : Finset V} {x : V} (hxA : x ∉ A') (hdis : Disjoint A' B) :
    (boundary (A' ∪ B)).starAt B x = (boundary (insert x A')).join (boundary B) := by
  refine ext_mem fun s => ?_
  rw [mem_starAt, mem_join]
  simp only [mem_boundary]
  constructor
  · rintro (⟨hs, hBs⟩ | ⟨t, ht, hBt, hBtC, rfl⟩)
    · refine ⟨s ∩ A', Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_right.trans
        (subset_insert x A'), fun e => hxA (inter_subset_right (e ▸ mem_insert_self x A'))⟩,
        s ∩ B, Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_right,
        fun e => hBs (e ▸ inter_subset_left)⟩, ?_⟩
      rw [← inter_union_distrib_left, inter_eq_left.2 hs.subset]
    · have htA : t ∩ A' ⊂ A' := Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_right, fun e => by
        have hA't : A' ⊆ t := e ▸ inter_subset_left
        exact hBtC.ne (subset_antisymm hBtC.subset
          (union_subset (hA't.trans subset_union_right) subset_union_left))⟩
      refine ⟨insert x (t ∩ A'), ?_, t ∩ B, Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_right,
        fun e => hBt (e ▸ inter_subset_left)⟩, ?_⟩
      · obtain ⟨a', ha'A, ha't⟩ := not_subset.1 htA.not_subset
        refine Finset.ssubset_iff_subset_ne.2 ⟨insert_subset_insert x htA.subset, fun e => ?_⟩
        have : a' ∈ insert x (t ∩ A') := e ▸ mem_insert_of_mem ha'A
        rcases mem_insert.1 this with h' | h'
        · exact hxA (h' ▸ ha'A)
        · exact ha't h'
      · rw [insert_union, ← inter_union_distrib_left, inter_eq_left.2 ht.subset]
  · rintro ⟨T, hT, u, hu, rfl⟩
    obtain ⟨b, hbB, hbu⟩ := not_subset.1 hu.not_subset
    have hbA : b ∉ A' := fun h' => disjoint_left.1 hdis h' hbB
    by_cases hxT : x ∈ T
    · right
      have hT' : T.erase x ⊂ A' := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨fun z hz => ?_, fun e => hT.ne ?_⟩
        · rcases mem_insert.1 (hT.subset (mem_of_mem_erase hz)) with h' | h'
          · exact absurd h' (ne_of_mem_erase hz)
          · exact h'
        · rw [← e, insert_erase hxT]
      have hbt : b ∉ T.erase x ∪ u := by
        rw [mem_union, not_or]
        exact ⟨fun h' => hbA (hT'.subset h'), hbu⟩
      refine ⟨T.erase x ∪ u, Finset.ssubset_iff_subset_ne.2 ⟨union_subset_union hT'.subset
        hu.subset, fun e => hbt (e ▸ mem_union_right _ hbB)⟩, fun h' => hbt (h' hbB), ?_, ?_⟩
      · obtain ⟨a', ha'A, ha'T⟩ := not_subset.1 hT'.not_subset
        refine Finset.ssubset_iff_subset_ne.2 ⟨union_subset subset_union_right
          (union_subset_union hT'.subset hu.subset), fun e => ?_⟩
        have : a' ∈ B ∪ (T.erase x ∪ u) := e ▸ mem_union_left _ ha'A
        rcases mem_union.1 this with h' | h'
        · exact disjoint_left.1 hdis ha'A h'
        · rcases mem_union.1 h' with h'' | h''
          · exact ha'T h''
          · exact disjoint_left.1 hdis ha'A (hu.subset h'')
      · rw [← insert_union, insert_erase hxT]
    · left
      have hTA : T ⊆ A' := fun z hz => by
        rcases mem_insert.1 (hT.subset hz) with h' | h'
        · exact absurd (h' ▸ hz) hxT
        · exact h'
      have hbs : b ∉ T ∪ u := by
        rw [mem_union, not_or]
        exact ⟨fun h' => hbA (hTA h'), hbu⟩
      exact ⟨Finset.ssubset_iff_subset_ne.2 ⟨union_subset_union hTA hu.subset,
        fun e => hbs (e ▸ mem_union_right _ hbB)⟩, fun h' => hbs (h' hbB)⟩

/-- **`Δ(A' ∪ {x}) * ∂B` is a subdivision of `Δ(A' ∪ B)`**: star `Δ(A' ∪ B)` at `B` with the new
vertex `x`. -/
theorem starAt_simplex_eq_join {A' B : Finset V} {x : V} (hdis : Disjoint A' B) :
    (simplex (A' ∪ B)).starAt B x = (simplex (insert x A')).join (boundary B) := by
  refine ext_mem fun s => ?_
  rw [mem_starAt, mem_join]
  simp only [mem_simplex, mem_boundary]
  constructor
  · rintro (⟨hs, hBs⟩ | ⟨t, ht, hBt, -, rfl⟩)
    · refine ⟨s ∩ A', inter_subset_right.trans (subset_insert x A'), s ∩ B,
        Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_right, fun e => hBs (e ▸ inter_subset_left)⟩,
        ?_⟩
      rw [← inter_union_distrib_left, inter_eq_left.2 hs]
    · refine ⟨insert x (t ∩ A'), insert_subset_insert x inter_subset_right, t ∩ B,
        Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_right, fun e => hBt (e ▸ inter_subset_left)⟩,
        ?_⟩
      rw [insert_union, ← inter_union_distrib_left, inter_eq_left.2 ht]
  · rintro ⟨T, hT, u, hu, rfl⟩
    obtain ⟨b, hbB, hbu⟩ := not_subset.1 hu.not_subset
    have hbA : b ∉ A' := fun h' => disjoint_left.1 hdis h' hbB
    by_cases hxT : x ∈ T
    · right
      have hT' : T.erase x ⊆ A' := fun z hz => by
        rcases mem_insert.1 (hT (mem_of_mem_erase hz)) with h' | h'
        · exact absurd h' (ne_of_mem_erase hz)
        · exact h'
      have hbt : b ∉ T.erase x ∪ u := by
        rw [mem_union, not_or]
        exact ⟨fun h' => hbA (hT' h'), hbu⟩
      exact ⟨T.erase x ∪ u, union_subset_union hT' hu.subset, fun h' => hbt (h' hbB),
        union_subset subset_union_right (union_subset_union hT' hu.subset),
        by rw [← insert_union, insert_erase hxT]⟩
    · left
      have hTA : T ⊆ A' := fun z hz => by
        rcases mem_insert.1 (hT hz) with h' | h'
        · exact absurd (h' ▸ hz) hxT
        · exact h'
      have hbs : b ∉ T ∪ u := by
        rw [mem_union, not_or]
        exact ⟨fun h' => hbA (hTA h'), hbu⟩
      exact ⟨union_subset_union hTA hu.subset, fun h' => hbs (h' hbB)⟩

/-! ## Joins of `∂A` with spheres and balls -/

/-- `L` is a PL `(m−1)`-sphere inside `V` or, when `b` is true, a PL `(m−1)`-sphere or
`(m−1)`-ball: stellar equivalent inside `V` to the boundary of a simplex on `m + 1` vertices, or to
a simplex on `m` vertices. (`b` selects closed manifolds or manifolds with boundary.) -/
def IsSB (b : Bool) (m : ℕ) (L : SComplex V) : Prop :=
  (∃ A : Finset V, #A = m + 1 ∧ StellarEquivIn L (boundary A)) ∨
    (b = true ∧ ∃ A : Finset V, #A = m ∧ StellarEquivIn L (simplex A))

lemma IsSB.of_stellarEquivIn {b : Bool} {m : ℕ} {L L' : SComplex V} (h : IsSB b m L)
    (h' : StellarEquivIn L L') : IsSB b m L' := by
  rcases h with ⟨A, hA, hLA⟩ | ⟨hb, A, hA, hLA⟩
  · exact .inl ⟨A, hA, h'.symm.trans hLA⟩
  · exact .inr ⟨hb, A, hA, h'.symm.trans hLA⟩

lemma isSB_iff_of_stellarEquivIn {b : Bool} {m : ℕ} {L L' : SComplex V}
    (h' : StellarEquivIn L L') : IsSB b m L ↔ IsSB b m L' :=
  ⟨fun h => h.of_stellarEquivIn h', fun h => h.of_stellarEquivIn h'.symm⟩

/-- **The join of `∂A` with a PL sphere is a PL sphere, and with a PL ball a PL ball**: if `L` is
a PL `(m−1)`-sphere (or ball) without vertices in `A`, then `∂A * L` is a PL `(m + #A − 2)`-sphere
(or ball). -/
theorem IsSB.boundary_join [Infinite V] {b : Bool} {m : ℕ} {A : Finset V} {L : SComplex V}
    (hL : IsSB b m L) (hA : A.Nonempty) (hdis : Disjoint A L.verts) :
    IsSB b (m + #A - 1) ((boundary A).join L) := by
  obtain ⟨x, hx⟩ := hA
  have hA : A = insert x (A.erase x) := (insert_erase hx).symm
  have hxA' : x ∉ A.erase x := notMem_erase x A
  have hcardA : #A = #(A.erase x) + 1 := by rw [card_erase_of_mem hx]; have := card_pos.2 ⟨x, hx⟩; omega
  rcases (A.erase x).eq_empty_or_nonempty with hA' | hA'
  · -- `A` is a single vertex: `∂A = {∅}` is a unit for the join
    rw [hA, hA', insert_empty, boundary_singleton, simplex_empty_join, card_singleton,
      Nat.add_sub_cancel]
    exact hL
  · have h0A : ∅ ∈ boundary A := mem_boundary.2 (Finset.ssubset_iff_subset_ne.2
      ⟨empty_subset _, (ne_empty_of_mem hx).symm⟩)
    have hvA : (boundary A).verts ⊆ A := fun z hz => (mem_boundary.1 (mem_verts.1 hz)).subset
      (mem_singleton_self z)
    -- a ball on no vertices is the `(−1)`-sphere
    have hL' : (∃ B : Finset V, #B = m + 1 ∧ StellarEquivIn L (boundary B)) ∨
        (b = true ∧ 1 ≤ m ∧ ∃ B : Finset V, #B = m ∧ StellarEquivIn L (simplex B)) := by
      rcases hL with h | ⟨hb, B, hB, hLB⟩
      · exact .inl h
      · rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm
          rw [card_eq_zero] at hB
          subst hB
          obtain ⟨z, -⟩ := Infinite.exists_notMem_finset (∅ : Finset V)
          exact .inl ⟨{z}, card_singleton z, by rw [boundary_singleton]; exact hLB⟩
        · exact .inr ⟨hb, hm, B, hB, hLB⟩
    rcases hL' with ⟨B₀, hB₀, hLB₀⟩ | ⟨hb, hm, B₀, hB₀, hLB₀⟩
    · -- sphere case
      obtain ⟨B, hB, hBdis⟩ := exists_card_disjoint (A ∪ L.verts) (m + 1)
      rw [disjoint_union_right] at hBdis
      have hLB : StellarEquivIn L (boundary B) :=
        hLB₀.trans (StellarEquivIn.boundary_of_card (hB₀.trans hB.symm))
      have hvB : (boundary B).verts ⊆ B := fun z hz => (mem_boundary.1 (mem_verts.1 hz)).subset
        (mem_singleton_self z)
      have h₁ : StellarEquivIn ((boundary A).join L) ((boundary A).join (boundary B)) := by
        rw [join_comm, join_comm (boundary A)]
        exact StellarEquivIn.join_right hLB h0A
          (disjoint_of_subset_right hvA (disjoint_comm.1 hdis))
          (disjoint_of_subset_left hvB (disjoint_of_subset_right hvA hBdis.1))
      have hxB : x ∉ B := fun h' => disjoint_left.1 hBdis.1 h' hx
      have hdis' : Disjoint (A.erase x) B :=
        disjoint_of_subset_left (erase_subset x A) (disjoint_comm.1 hBdis.1)
      have h₂ : StellarEquivIn (boundary (A.erase x ∪ B))
          ((boundary A).join (boundary B)) := by
        have e : (boundary A).join (boundary B) = (boundary (A.erase x ∪ B)).starAt B x := by
          rw [starAt_boundary_eq_join hxA' hdis', insert_erase hx]
        rw [e]
        obtain ⟨a', ha'⟩ := hA'
        refine StellarEquivIn.starAt (mem_boundary.2 (Finset.ssubset_iff_subset_ne.2
          ⟨subset_union_right, fun e => ?_⟩)) (card_pos.1 (by omega)) ?_
        · have : a' ∈ B := e ▸ mem_union_left B ha'
          exact disjoint_left.1 hdis' ha' this
        · intro h'
          have := (mem_boundary.1 (mem_verts.1 h')).subset (mem_singleton_self x)
          rcases mem_union.1 this with h'' | h''
          · exact hxA' h''
          · exact hxB h''
      refine .inl ⟨A.erase x ∪ B, ?_, h₁.trans h₂.symm⟩
      rw [card_union_of_disjoint hdis', hB]
      omega
    · -- ball case
      obtain ⟨B, hB, hBdis⟩ := exists_card_disjoint (A ∪ L.verts) m
      rw [disjoint_union_right] at hBdis
      have hLB : StellarEquivIn L (simplex B) :=
        hLB₀.trans (StellarEquivIn.simplex_of_card (hB₀.trans hB.symm))
      have h₁ : StellarEquivIn ((boundary A).join L) ((boundary A).join (simplex B)) := by
        rw [join_comm, join_comm (boundary A)]
        refine StellarEquivIn.join_right hLB h0A
          (disjoint_of_subset_right hvA (disjoint_comm.1 hdis)) ?_
        rw [verts_simplex]
        exact disjoint_of_subset_right hvA hBdis.1
      obtain ⟨y, hy⟩ : B.Nonempty := card_pos.1 (by omega)
      have hyB' : y ∉ B.erase y := notMem_erase y B
      have hyA : y ∉ A := fun h' => disjoint_left.1 hBdis.1 hy h'
      have hdis' : Disjoint (B.erase y) A :=
        disjoint_of_subset_left (erase_subset y B) hBdis.1
      have h₂ : StellarEquivIn (simplex (B.erase y ∪ A)) ((boundary A).join (simplex B)) := by
        have e : (boundary A).join (simplex B) = (simplex (B.erase y ∪ A)).starAt A y := by
          rw [starAt_simplex_eq_join hdis', insert_erase hy, join_comm]
        rw [e]
        refine StellarEquivIn.starAt (mem_simplex.2 subset_union_right) ⟨x, hx⟩ ?_
        rw [verts_simplex, mem_union, not_or]
        exact ⟨hyB', hyA⟩
      refine .inr ⟨hb, B.erase y ∪ A, ?_, h₁.trans h₂.symm⟩
      rw [card_union_of_disjoint hdis', card_erase_of_mem hy, hB]
      omega

end SComplex

end Lightlike.PL
