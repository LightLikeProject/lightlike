import Lightlike.PL.Pachner

/-!
# Pachner's theorem: the main induction

Lickorish's induction (1999, proof of Theorem 5.9). Suppose `lk(X, K) = ∂Y * S * L'` with `S` a
standard sphere and `L'` a PL sphere related to the boundary of a simplex `∂D₀` by a chain of `r`
stellar moves. The exchange `κ(X, Y)` is shown to be a composite of bistellar moves by induction
on `#D₀` (the dimension of `L'` plus two) and then on `r`. If the first move of the chain is the
exchange `κ(C, D)` of `L'`, with `lk(C, L') = ∂D * L''`, and `D ∉ K`, then

  `K →κ(X ∪ C, D)→ M₁ →κ(X, Y)→ M₂`  and  `K →κ(X, Y)→ K' →κ(Y ∪ C, D)→ M₂`

(`exch_comm`), where the exchanges at `X ∪ C` and `Y ∪ C` have the smaller sphere `L''` in their
links and the exchange `κ(X, Y)` on `M₁` has the shorter chain. If `D ∈ K`, the chain is renamed
so that `D` becomes new (`D` a vertex), or a vertex `u` of `D` is first moved to a new vertex `v`
by `κ(X ∪ u, v)` (the same identity with `C = {u}`, `D = {v}`).

## Main results

* `StepChain`: chains of a given length of stellar moves avoiding a finite set.
* `exch_comm`: the commutation identity.
* `exchStmt`: the main induction.
* `bistellarEquivIn_starAt`: every stellar subdivision of a closed combinatorial manifold is a
  composite of bistellar moves.
* `pachner`: **Pachner's theorem, stellar version** - closed combinatorial manifolds are stellar
  equivalent if and only if they are related by bistellar moves. The version with PL
  homeomorphisms (Lickorish 1999, Theorem 5.9) is `SComplex.pachner_plHomeomorphic` in
  `Lightlike/PL/PachnerPL.lean`, from this theorem and Newman's theorem.
* `IsClosedCombManifold.bistellarEquiv_map`, `IsClosedCombManifold.bistellarEquiv_of_iso`:
  renamings and isomorphisms of closed combinatorial manifolds are composites of bistellar
  moves.
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V : Type*} [DecidableEq V]

/-! ## Chains of stellar moves -/

/-- A **chain of `r` stellar moves** (subdivisions or welds inside `V`) from `L` to `N`, all of
whose complexes have no vertex in `F`. -/
inductive StepChain (F : Finset V) : ℕ → SComplex V → SComplex V → Prop
  /-- The chain of length `0`. -/
  | refl {L : SComplex V} (hL : Disjoint L.verts F) : StepChain F 0 L L
  /-- A stellar move in either direction, followed by a chain. -/
  | step {L M N : SComplex V} {r : ℕ} (hLM : StellarStep L M ∨ StellarStep M L)
      (hL : Disjoint L.verts F) (hMN : StepChain F r M N) : StepChain F (r + 1) L N

namespace StepChain

variable {F : Finset V}

lemma source {r : ℕ} {L N : SComplex V} (h : StepChain F r L N) : Disjoint L.verts F := by
  cases h with
  | refl hL => exact hL
  | step _ hL _ => exact hL

lemma target {r : ℕ} {L N : SComplex V} (h : StepChain F r L N) : Disjoint N.verts F := by
  induction h with
  | refl hL => exact hL
  | step _ _ _ ih => exact ih

lemma append {r s : ℕ} {L M N : SComplex V} (h₁ : StepChain F r L M) (h₂ : StepChain F s M N) :
    StepChain F (r + s) L N := by
  induction h₁ with
  | refl _ => simpa using h₂
  | step hLM hL _ ih =>
    rw [Nat.add_right_comm]
    exact .step hLM hL (ih h₂)

lemma single {L M : SComplex V} (hLM : StellarStep L M ∨ StellarStep M L)
    (hL : Disjoint L.verts F) (hM : Disjoint M.verts F) : StepChain F 1 L M :=
  .step hLM hL (.refl hM)

lemma reverse {r : ℕ} {L N : SComplex V} (h : StepChain F r L N) : StepChain F r N L := by
  induction h with
  | refl hL => exact .refl hL
  | @step L M N r hLM hL hMN ih =>
    have := ih.append (single hLM.symm hMN.source hL)
    exact this

/-- A stellar equivalence inside an infinite type is a chain avoiding any finite set that its
ends avoid. -/
theorem exists_of_stellarEquivIn [Infinite V] {L N : SComplex V} (h : StellarEquivIn L N)
    (hL : Disjoint L.verts F) (hN : Disjoint N.verts F) : ∃ r, StepChain F r L N := by
  obtain ⟨U, hUF, hLU, hch⟩ := h.exists_avoiding F hL hN
  have key : ∀ X Y : SComplex V, Relation.EqvGen (StepWithin U) X Y → X.verts ⊆ U →
      ∃ r, StepChain F r X Y := by
    intro X Y hXY
    induction hXY with
    | rel X Y hXY =>
      intro _
      exact ⟨1, single (.inl hXY.1) (disjoint_of_subset_left hXY.2.1 hUF)
        (disjoint_of_subset_left hXY.2.2 hUF)⟩
    | refl X => exact fun hX => ⟨0, .refl (disjoint_of_subset_left hX hUF)⟩
    | symm X Y hXY ih =>
      intro hY
      obtain ⟨r, hr⟩ := ih ((verts_subset_iff_of_eqvGen hXY).2 hY)
      exact ⟨r, hr.reverse⟩
    | trans X Y Z hXY _ ih₁ ih₂ =>
      intro hX
      obtain ⟨r, hr⟩ := ih₁ hX
      obtain ⟨s, hs⟩ := ih₂ ((verts_subset_iff_of_eqvGen hXY).1 hX)
      exact ⟨r + s, hr.append hs⟩
  exact key L N hch hLU

/-- A chain is a stellar equivalence. -/
lemma stellarEquivIn {r : ℕ} {L N : SComplex V} (h : StepChain F r L N) : StellarEquivIn L N := by
  induction h with
  | refl _ => exact .refl _
  | step hLM _ _ ih =>
    rcases hLM with h' | h'
    · exact (Relation.EqvGen.rel _ _ h').trans _ _ _ ih
    · exact (Relation.EqvGen.rel _ _ h').symm.trans _ _ _ ih

end StepChain

/-- Stellar steps are transported by injective maps of the vertices. -/
lemma StellarStep.map {W : Type*} [DecidableEq W] {L M : SComplex V} (h : StellarStep L M)
    (f : V ↪ W) : StellarStep (L.map f) (M.map f) := by
  obtain ⟨hA, hne, ha⟩ := h
  rw [map_starAt]
  refine .starAt (map_mem_map.2 hA) hne.map ?_
  rw [verts_map, Finset.mem_map' f]
  exact ha

/-- Chains are transported by permutations of the vertices. -/
lemma StepChain.map {F : Finset V} {r : ℕ} {L N : SComplex V} (h : StepChain F r L N)
    (σ : Equiv.Perm V) :
    StepChain (F.map σ.toEmbedding) r (L.map σ.toEmbedding) (N.map σ.toEmbedding) := by
  induction h with
  | refl hL => exact .refl (by rw [verts_map]; exact (Finset.disjoint_map _).2 hL)
  | step hLM hL _ ih =>
    refine .step ?_ (by rw [verts_map]; exact (Finset.disjoint_map _).2 hL) ih
    rcases hLM with h' | h'
    · exact .inl (h'.map _)
    · exact .inr (h'.map _)

/-! ## The commutation identity -/

/-- **The commutation identity** (Lickorish 1999, proof of Theorem 5.9): if `lk(X, K) = ∂Y * P * L'`
and `κ(C, D)` is an exchange of `L'` with complementary link `L''`, then

  `κ(X, Y) κ(X ∪ C, D) K = κ(Y ∪ C, D) κ(X, Y) K`.

Both sides have the same faces without `Y`, and the same link `∂X * P * κ(C, D) L'` of `Y`. -/
theorem exch_comm {K P L' L'' : SComplex V} {X Y C D : Finset V}
    (hP0 : ∅ ∈ P) (hXC : Disjoint X C) (hYC : Disjoint Y C) (hYD : Disjoint Y D)
    (hXP : Disjoint X P.verts) (hDP : Disjoint D P.verts)
    (hXL : Disjoint X L'.verts) (hPL : Disjoint P.verts L'.verts) (hXL'' : Disjoint X L''.verts)
    (h : IsExch K X Y (P.join L')) (hC : IsExch L' C D L'')
    (h₁ : IsExch K (X ∪ C) D (((boundary Y).join P).join L''))
    (h₂ : IsExch (exch K (X ∪ C) D _ h₁) X Y (P.join (exch L' C D L'' hC)))
    (h' : IsExch (exch K X Y (P.join L') h) (Y ∪ C) D (((boundary X).join P).join L'')) :
    exch (exch K (X ∪ C) D _ h₁) X Y (P.join (exch L' C D L'' hC)) h₂ =
      exch (exch K X Y (P.join L') h) (Y ∪ C) D _ h' := by
  have hXY : Disjoint X Y := h.disjoint
  have hXD : Disjoint X D := disjoint_of_subset_left subset_union_left h₁.disjoint
  have hCne : C.Nonempty := hC.nonempty_left
  apply eq_of_link_eq (B := Y)
  · intro s hYs
    rw [mem_exch_of_not_subset hYs, mem_exch, mem_exch]
    constructor
    · rintro ⟨⟨hs, hXCs⟩ | ⟨t, ht, u, hu, rfl⟩, hXs⟩
      · exact .inl ⟨(mem_exch_of_not_subset hYs).2 ⟨hs, hXs⟩,
          fun h'' => hYs (subset_union_left.trans h'')⟩
      · right
        obtain ⟨bp, hbp, l, hl, rfl⟩ := mem_join.1 hu
        obtain ⟨b, hb, p, hp, rfl⟩ := mem_join.1 hbp
        rw [mem_boundary] at hb
        have hXt : ¬ X ⊆ t := fun h'' => hXs (h''.trans (subset_union_left.trans
          subset_union_left))
        refine ⟨b ∪ (t ∩ C), ?_, ((t ∩ X) ∪ p) ∪ l, mem_join.2 ⟨(t ∩ X) ∪ p, mem_join.2
          ⟨t ∩ X, mem_boundary.2 (Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_right,
            fun e => hXt fun x hx => (mem_inter.1 (e.symm ▸ hx : x ∈ t ∩ X)).1⟩), p, hp, rfl⟩,
          l, hl, rfl⟩, ?_⟩
        · obtain ⟨y, hyY, hyb⟩ := not_subset.1 hb.not_subset
          refine Finset.ssubset_iff_subset_ne.2 ⟨union_subset_union hb.subset inter_subset_right,
            fun e => ?_⟩
          have : y ∈ b ∪ (t ∩ C) := e ▸ mem_union_left C hyY
          rcases mem_union.1 this with h3 | h3
          · exact hyb h3
          · exact disjoint_left.1 hYC hyY (mem_inter.1 h3).2
        · ext x
          have hx : x ∈ t → x ∈ X ∨ x ∈ C := fun hx => mem_union.1 (ht.subset hx)
          simp only [mem_union, mem_inter]
          tauto
    · rintro (⟨hs, hYCs⟩ | ⟨t, ht, u, hu, rfl⟩)
      · obtain ⟨hs', hXs⟩ := (mem_exch_of_not_subset hYs).1 hs
        exact ⟨.inl ⟨hs', fun h'' => hXs (subset_union_left.trans h'')⟩, hXs⟩
      · obtain ⟨ap, hap, l, hl, rfl⟩ := mem_join.1 hu
        obtain ⟨a, ha, p, hp, rfl⟩ := mem_join.1 hap
        rw [mem_boundary] at ha
        have hYt : ¬ Y ⊆ t := fun h'' => hYs (h''.trans (subset_union_left.trans
          subset_union_left))
        have htYC : ∀ x ∈ t, x ∈ Y ∨ x ∈ C := fun x hx => mem_union.1 (ht.subset hx)
        refine ⟨.inr ⟨a ∪ (t ∩ C), ?_, ((t ∩ Y) ∪ p) ∪ l, mem_join.2 ⟨(t ∩ Y) ∪ p, mem_join.2
          ⟨t ∩ Y, mem_boundary.2 (Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_right,
            fun e => hYt fun x hx => (mem_inter.1 (e.symm ▸ hx : x ∈ t ∩ Y)).1⟩), p, hp, rfl⟩,
          l, hl, rfl⟩, ?_⟩, ?_⟩
        · obtain ⟨x, hxX, hxa⟩ := not_subset.1 ha.not_subset
          refine Finset.ssubset_iff_subset_ne.2 ⟨union_subset_union ha.subset inter_subset_right,
            fun e => ?_⟩
          have : x ∈ a ∪ (t ∩ C) := e ▸ mem_union_left C hxX
          rcases mem_union.1 this with h3 | h3
          · exact hxa h3
          · exact disjoint_left.1 hXC hxX (mem_inter.1 h3).2
        · ext x
          have hx : x ∈ t → x ∈ Y ∨ x ∈ C := htYC x
          simp only [mem_union, mem_inter]
          tauto
        · intro hXs
          obtain ⟨x, hxX, hxa⟩ := not_subset.1 ha.not_subset
          have hx := hXs hxX
          simp only [mem_union] at hx
          rcases hx with (h3 | h3) | ((h3 | h3) | h3)
          · rcases htYC x h3 with h4 | h4
            · exact disjoint_left.1 hXY hxX h4
            · exact disjoint_left.1 hXC hxX h4
          · exact disjoint_left.1 hXD hxX h3
          · exact hxa h3
          · exact disjoint_left.1 hXP hxX (subset_verts hp h3)
          · exact disjoint_left.1 hXL'' hxX (subset_verts hl h3)
  · -- the links of `Y`
    have hXPv : ((boundary X).join P).verts ⊆ X ∪ P.verts :=
      (verts_join_subset _ _).trans (union_subset_union (verts_boundary_subset X) subset_rfl)
    have hYLc : Disjoint Y (((boundary X).join P).join L'').verts :=
      disjoint_of_subset_left subset_union_left h'.disjoint_left_verts
    rw [link_exch_right h₂, link_exch h' hYC hCne hYD hYLc]
    have h0 : ∅ ∈ (boundary X).join P := mem_join.2 ⟨∅, mem_boundary.2
      (Finset.ssubset_iff_subset_ne.2 ⟨empty_subset _, h.nonempty_left.ne_empty.symm⟩), ∅, hP0,
      union_empty _⟩
    have hk : IsExch (((boundary X).join P).join L') C D (((boundary X).join P).join L'') :=
      hC.join_left h0
        (disjoint_of_subset_left hXPv (disjoint_union_left.2 ⟨hXL, hPL⟩))
        (disjoint_of_subset_left hXPv (disjoint_union_left.2 ⟨hXD, hDP.symm⟩))
    rw [exch_congr (by rw [link_exch_right h, join_assoc]) rfl _ hk,
      exch_join hC h0 (disjoint_of_subset_left hXPv (disjoint_union_left.2 ⟨hXL, hPL⟩))
        (disjoint_of_subset_left hXPv (disjoint_union_left.2 ⟨hXD, hDP.symm⟩)), join_assoc]

/-! ## Exchanges and renamings -/

lemma map_join {W : Type*} [DecidableEq W] (K L : SComplex V) (f : V ↪ W) :
    (K.join L).map f = (K.map f).join (L.map f) := by
  refine (eq_map_of ?_ ?_).symm
  · intro s hs
    obtain ⟨t, ht, u, hu, rfl⟩ := mem_join.1 hs
    obtain ⟨t', rfl⟩ := exists_eq_map_of_mem_map ht
    obtain ⟨u', rfl⟩ := exists_eq_map_of_mem_map hu
    exact ⟨t' ∪ u', Finset.map_union t' u'⟩
  · intro s
    rw [mem_join, mem_join]
    constructor
    · rintro ⟨t, ht, u, hu, he⟩
      obtain ⟨t', rfl⟩ := exists_eq_map_of_mem_map ht
      obtain ⟨u', rfl⟩ := exists_eq_map_of_mem_map hu
      rw [← Finset.map_union, Finset.map_inj] at he
      exact ⟨t', map_mem_map.1 ht, u', map_mem_map.1 hu, he⟩
    · rintro ⟨t, ht, u, hu, rfl⟩
      exact ⟨t.map f, map_mem_map.2 ht, u.map f, map_mem_map.2 hu, (Finset.map_union t u).symm⟩

/-- The exchange conditions are transported by injective maps of the vertices. -/
lemma IsExch.map {W : Type*} [DecidableEq W] {K L : SComplex V} {A B : Finset V}
    (h : IsExch K A B L) (f : V ↪ W) : IsExch (K.map f) (A.map f) (B.map f) (L.map f) where
  nonempty_left := h.nonempty_left.map
  nonempty_right := h.nonempty_right.map
  disjoint := (Finset.disjoint_map f).2 h.disjoint
  disjoint_left_verts := by rw [verts_map]; exact (Finset.disjoint_map f).2 h.disjoint_left_verts
  disjoint_right_verts := by rw [verts_map]; exact (Finset.disjoint_map f).2 h.disjoint_right_verts
  empty_mem := by rw [← map_empty f]; exact map_mem_map.2 h.empty_mem
  link_eq := by rw [← map_link, h.link_eq, map_join, map_boundary]
  notMem := by rw [map_mem_map]; exact h.notMem

/-- **Exchanges commute with injective maps of the vertices.** -/
theorem map_exch {W : Type*} [DecidableEq W] {K L : SComplex V} {A B : Finset V}
    (h : IsExch K A B L) (f : V ↪ W) :
    (exch K A B L h).map f = exch (K.map f) (A.map f) (B.map f) (L.map f) (h.map f) := by
  refine (eq_map_of ?_ ?_).symm
  · intro s hs
    rcases mem_exch.1 hs with ⟨hs, -⟩ | ⟨t, ht, u, hu, rfl⟩
    · exact exists_eq_map_of_mem_map hs
    · obtain ⟨t', -, rfl⟩ := Finset.subset_map_iff.1 ht.subset
      obtain ⟨u', rfl⟩ := exists_eq_map_of_mem_map hu
      exact ⟨t' ∪ B ∪ u', by rw [Finset.map_union, Finset.map_union]⟩
  · intro t
    rw [mem_exch, mem_exch, map_mem_map, Finset.map_subset_map]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨a, ha, u, hu, he⟩
      obtain ⟨a', -, rfl⟩ := Finset.subset_map_iff.1 ha.subset
      obtain ⟨u', rfl⟩ := exists_eq_map_of_mem_map hu
      rw [← Finset.map_union, ← Finset.map_union, Finset.map_inj] at he
      exact ⟨a', Finset.map_ssubset_map.1 ha, u', map_mem_map.1 hu, he⟩
    · rintro ⟨a, ha, u, hu, rfl⟩
      exact ⟨a.map f, Finset.map_ssubset_map.2 ha, u.map f, map_mem_map.2 hu,
        by rw [Finset.map_union, Finset.map_union]⟩

/-! ## The first move of a chain -/

/-- **A stellar move, in either direction, is an exchange** `κ(C, D)` whose complementary link is
the link of a nonempty face of one of the two complexes. -/
lemma exists_exch_of_step {L M : SComplex V} (h : StellarStep L M ∨ StellarStep M L) :
    ∃ (C D : Finset V) (L'' : SComplex V) (hC : IsExch L C D L''), M = exch L C D L'' hC ∧
      ((C ∈ L ∧ C.Nonempty ∧ L'' = L.link C) ∨ (D ∈ M ∧ D.Nonempty ∧ L'' = M.link D)) := by
  rcases h with h | h
  · obtain ⟨hA, hne, ha⟩ := h
    exact ⟨_, _, _, isExch_starAt hA hne ha, (exch_eq_starAt hA hne ha).symm,
      .inl ⟨hA, hne, rfl⟩⟩
  · obtain ⟨hA, hne, ha⟩ := h
    have h0 := isExch_starAt hA hne ha
    rw [← exch_eq_starAt hA hne ha]
    exact ⟨_, _, _, isExch_exch h0, (exch_exch h0).symm, .inr ⟨hA, hne, rfl⟩⟩

/-! ## Links of faces of spheres -/

/-- **The link of a nonempty face `σ` of a PL sphere is a PL sphere** whose model simplex has
`#σ` fewer vertices. -/
lemma link_of_stellarEquivIn_boundary [Infinite V] {Z : SComplex V} {D₀ : Finset V}
    (hZ : StellarEquivIn Z (boundary D₀)) {σ : Finset V} (hσ : σ ∈ Z) (hne : σ.Nonempty) :
    ∃ D'' : Finset V, #D'' + #σ = #D₀ ∧ StellarEquivIn (Z.link σ) (boundary D'') := by
  obtain ⟨n, hn⟩ : ∃ n, #D₀ = n + 2 := by
    by_contra hlt
    have hle : #D₀ ≤ 1 := by
      by_contra h'
      exact hlt ⟨#D₀ - 2, by omega⟩
    have hmax : Z.maxCard ≤ 0 := by
      rw [hZ.maxCard_eq]
      refine maxCard_le fun s hs => ?_
      have := card_lt_card (mem_boundary.1 hs)
      omega
    have := card_le_maxCard hσ
    have := card_pos.2 hne
    omega
  have hMfd := (isMfdIn_main false n).2 Z (.inl ⟨D₀, hn, hZ⟩)
  obtain ⟨m, hm, hSB⟩ := (isMfdIn_main false n).1 Z hMfd σ hσ hne
  rcases hSB with ⟨A, hA, hlk⟩ | ⟨hb, -⟩
  · exact ⟨A, by omega, hlk⟩
  · exact absurd hb (by decide)

/-- A PL sphere is related, by a chain avoiding any finite set that it avoids, to the boundary of
a simplex of the same size avoiding that set. -/
lemma exists_chain_of_stellarEquivIn_boundary [Infinite V] {L : SComplex V} {D₀ : Finset V}
    (h : StellarEquivIn L (boundary D₀)) {F : Finset V} (hL : Disjoint L.verts F) :
    ∃ (D₁ : Finset V) (r : ℕ), #D₁ = #D₀ ∧ StepChain F r L (boundary D₁) := by
  obtain ⟨D₁, hD₁, hdis⟩ := exists_card_disjoint F #D₀
  have h' := h.trans (StellarEquivIn.boundary_of_card hD₁.symm)
  obtain ⟨r, hr⟩ := StepChain.exists_of_stellarEquivIn h' hL
    (disjoint_of_subset_left (verts_boundary_subset D₁) hdis)
  exact ⟨D₁, r, hD₁, hr⟩

/-! ## The exchanges of the inductive step -/

lemma verts_triple_subset (Z : Finset V) (P L : SComplex V) :
    (((boundary Z).join P).join L).verts ⊆ Z ∪ P.verts ∪ L.verts :=
  (verts_join_subset _ _).trans (union_subset_union ((verts_join_subset _ _).trans
    (union_subset_union (verts_boundary_subset Z) subset_rfl)) subset_rfl)

lemma empty_mem_boundary_join {Z : Finset V} {P : SComplex V} (hZ : Z.Nonempty) (hP : ∅ ∈ P) :
    ∅ ∈ (boundary Z).join P :=
  mem_join.2 ⟨∅, mem_boundary.2 (Finset.ssubset_iff_subset_ne.2 ⟨empty_subset _,
    hZ.ne_empty.symm⟩), ∅, hP, union_empty _⟩

/-- The link of `X ∪ C` when `lk(X, K) = ∂Y * P * L'` and `lk(C, L') = ∂D * L''`. -/
lemma link_union_eq {K P L' L'' : SComplex V} {X Y C D : Finset V}
    (hlk : K.link X = (boundary Y).join (P.join L')) (hC : IsExch L' C D L'')
    (hXC : Disjoint X C) (hYPL : Disjoint ((boundary Y).join P).verts L'.verts) :
    K.link (X ∪ C) = (boundary D).join (((boundary Y).join P).join L'') := by
  rw [← link_link K hXC, hlk, ← join_assoc, link_join_right hYPL (subset_verts hC.mem),
    hC.link_eq, join_left_comm]

/-- The exchange `κ(X ∪ C, D)` of the inductive step is defined. -/
lemma isExch_union {K P L' L'' : SComplex V} {X Y C D : Finset V} (hP0 : ∅ ∈ P)
    (h : IsExch K X Y (P.join L')) (hC : IsExch L' C D L'') (hDK : D ∉ K)
    (hXC : Disjoint X C) (hXD : Disjoint X D) (hYC : Disjoint Y C) (hYD : Disjoint Y D)
    (hXP : Disjoint X P.verts) (hCP : Disjoint C P.verts) (hDP : Disjoint D P.verts)
    (hYL : Disjoint Y L'.verts) (hPL : Disjoint P.verts L'.verts)
    (hXL'' : Disjoint X L''.verts) :
    IsExch K (X ∪ C) D (((boundary Y).join P).join L'') where
  nonempty_left := h.nonempty_left.mono subset_union_left
  nonempty_right := hC.nonempty_right
  disjoint := disjoint_union_left.2 ⟨hXD, hC.disjoint⟩
  disjoint_left_verts := disjoint_of_subset_right (verts_triple_subset Y P L'')
    (disjoint_union_left.2 ⟨disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨h.disjoint, hXP⟩,
      hXL''⟩, disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨hYC.symm, hCP⟩,
      hC.disjoint_left_verts⟩⟩)
  disjoint_right_verts := disjoint_of_subset_right (verts_triple_subset Y P L'')
    (disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨hYD.symm, hDP⟩, hC.disjoint_right_verts⟩)
  empty_mem := mem_join.2 ⟨∅, empty_mem_boundary_join h.nonempty_right hP0, ∅, hC.empty_mem,
    union_empty _⟩
  link_eq := link_union_eq h.link_eq hC hXC (disjoint_of_subset_left ((verts_join_subset _ _).trans
    (union_subset_union (verts_boundary_subset Y) subset_rfl)) (disjoint_union_left.2 ⟨hYL, hPL⟩))
  notMem := hDK

/-- After `κ(X ∪ C, D)`, the exchange `κ(X, Y)` is defined, with `L'` replaced by `κ(C, D) L'`. -/
lemma isExch_after {K P L' L'' : SComplex V} {X Y C D : Finset V} (hP0 : ∅ ∈ P)
    (h : IsExch K X Y (P.join L')) (hC : IsExch L' C D L'')
    (h₁ : IsExch K (X ∪ C) D (((boundary Y).join P).join L''))
    (hXC : Disjoint X C) (hXD : Disjoint X D) (hYC : Disjoint Y C) (hYD : Disjoint Y D)
    (hXP : Disjoint X P.verts) (hYP : Disjoint Y P.verts) (hDP : Disjoint D P.verts)
    (hYL : Disjoint Y L'.verts) (hPL : Disjoint P.verts L'.verts) (hXL'' : Disjoint X L''.verts)
    (hYL'' : Disjoint Y L''.verts) (hXM : Disjoint X (exch L' C D L'' hC).verts)
    (hYM : Disjoint Y (exch L' C D L'' hC).verts) :
    IsExch (exch K (X ∪ C) D _ h₁) X Y (P.join (exch L' C D L'' hC)) where
  nonempty_left := h.nonempty_left
  nonempty_right := h.nonempty_right
  disjoint := h.disjoint
  disjoint_left_verts := disjoint_of_subset_right (verts_join_subset _ _)
    (disjoint_union_right.2 ⟨hXP, hXM⟩)
  disjoint_right_verts := disjoint_of_subset_right (verts_join_subset _ _)
    (disjoint_union_right.2 ⟨hYP, hYM⟩)
  empty_mem := mem_join.2 ⟨∅, hP0, ∅, mem_exch.2 (.inl ⟨empty_mem hC.mem, fun h' =>
    hC.nonempty_left.ne_empty (subset_empty.1 h')⟩), union_empty _⟩
  link_eq := by
    have hYPv : ((boundary Y).join P).verts ⊆ Y ∪ P.verts :=
      (verts_join_subset _ _).trans (union_subset_union (verts_boundary_subset Y) subset_rfl)
    have hXLc : Disjoint X (((boundary Y).join P).join L'').verts :=
      disjoint_of_subset_right (verts_triple_subset Y P L'')
        (disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨h.disjoint, hXP⟩, hXL''⟩)
    have h0 := empty_mem_boundary_join h.nonempty_right hP0
    have hk : IsExch (((boundary Y).join P).join L') C D (((boundary Y).join P).join L'') :=
      hC.join_left h0 (disjoint_of_subset_left hYPv (disjoint_union_left.2 ⟨hYL, hPL⟩))
        (disjoint_of_subset_left hYPv (disjoint_union_left.2 ⟨hYD, hDP.symm⟩))
    rw [link_exch h₁ hXC hC.nonempty_left hXD hXLc,
      exch_congr (by rw [h.link_eq, join_assoc]) rfl _ hk,
      exch_join hC h0 (disjoint_of_subset_left hYPv (disjoint_union_left.2 ⟨hYL, hPL⟩))
        (disjoint_of_subset_left hYPv (disjoint_union_left.2 ⟨hYD, hDP.symm⟩)), join_assoc]
  notMem := by
    rw [mem_exch]
    rintro (⟨hK, -⟩ | ⟨t, ht, u, hu, he⟩)
    · exact h.not_subset hK subset_rfl
    · obtain ⟨bp, hbp, l, hl, rfl⟩ := mem_join.1 hu
      obtain ⟨b, hb, p, hp, rfl⟩ := mem_join.1 hbp
      rw [mem_boundary] at hb
      obtain ⟨y, hyY, hyb⟩ := not_subset.1 hb.not_subset
      have : y ∈ t ∪ D ∪ (b ∪ p ∪ l) := he ▸ hyY
      simp only [mem_union] at this
      rcases this with (h3 | h3) | ((h3 | h3) | h3)
      · rcases mem_union.1 (ht.subset h3) with h4 | h4
        · exact disjoint_left.1 h.disjoint h4 hyY
        · exact disjoint_left.1 hYC hyY h4
      · exact disjoint_left.1 hYD hyY h3
      · exact hyb h3
      · exact disjoint_left.1 hYP hyY (subset_verts hp h3)
      · exact disjoint_left.1 hYL'' hyY (subset_verts hl h3)

/-! ## The main induction -/

/-- The statement of the main induction for spheres `L'` whose model simplex has `d` vertices and
chains of length `r`: every exchange `κ(X, Y)` with link `∂Y * S * L'` (`S` standard) is a
composite of bistellar moves. -/
def ExchStmt (d r : ℕ) : Prop :=
  ∀ (S : List (Finset V)) (L' K : SComplex V) (X Y D₀ : Finset V), IsStdList S → #D₀ = d →
    Disjoint (X ∪ Y) (suppList S) → StepChain (X ∪ Y ∪ suppList S) r L' (boundary D₀) →
    ∀ h : IsExch K X Y ((stdJoin S).join L'),
      BistellarEquivIn K (exch K X Y ((stdJoin S).join L') h)

/-- The induction hypothesis for smaller spheres, applied to a sphere (not a chain). -/
lemma exch_of_sphere [Infinite V] {d : ℕ} (ihd : ∀ r, ExchStmt (V := V) d r)
    {S : List (Finset V)} {L K : SComplex V} {X Y D₁ : Finset V} (hS : IsStdList S)
    (hD₁ : #D₁ = d) (hdis : Disjoint (X ∪ Y) (suppList S))
    (hsph : StellarEquivIn L (boundary D₁)) (hL : Disjoint L.verts (X ∪ Y ∪ suppList S))
    (h : IsExch K X Y ((stdJoin S).join L)) :
    BistellarEquivIn K (exch K X Y ((stdJoin S).join L) h) := by
  obtain ⟨D₂, r, hD₂, hch⟩ := exists_chain_of_stellarEquivIn_boundary hsph hL
  exact ihd r S L K X Y D₂ hS (hD₂.trans hD₁) hdis hch h

/-- **The inductive step, given the middle equivalence**: if the move `κ(C, D)` of `L'` has
`D ∉ K` and a smaller sphere `L''`, and `κ(X, Y)` after `κ(X ∪ C, D)` is a composite of bistellar
moves, then so is `κ(X, Y)`. -/
lemma exch_of_comm [Infinite V] {d : ℕ}
    (ihd : ∀ d' < d, ∀ r', ExchStmt (V := V) d' r')
    {S : List (Finset V)} {L' K L'' : SComplex V} {X Y C D : Finset V}
    (hS : IsStdList S) (hdis : Disjoint (X ∪ Y) (suppList S))
    (hL' : Disjoint L'.verts (X ∪ Y ∪ suppList S)) (hC : IsExch L' C D L'')
    (hM : Disjoint (exch L' C D L'' hC).verts (X ∪ Y ∪ suppList S))
    (hL'' : ∃ D'', #D'' < d ∧ StellarEquivIn L'' (boundary D''))
    (hDK : D ∉ K) (h : IsExch K X Y ((stdJoin S).join L'))
    (he₂ : ∀ (h₁ : IsExch K (X ∪ C) D (((boundary Y).join (stdJoin S)).join L''))
      (h₂ : IsExch (exch K (X ∪ C) D _ h₁) X Y ((stdJoin S).join (exch L' C D L'' hC))),
      BistellarEquivIn (exch K (X ∪ C) D _ h₁)
        (exch (exch K (X ∪ C) D _ h₁) X Y ((stdJoin S).join (exch L' C D L'' hC)) h₂)) :
    BistellarEquivIn K (exch K X Y ((stdJoin S).join L') h) := by
  obtain ⟨D'', hD''d, hsph⟩ := hL''
  have hP0 : ∅ ∈ stdJoin S := empty_mem_stdJoin hS
  have hPv : (stdJoin S).verts ⊆ suppList S := verts_stdJoin_subset S
  rw [disjoint_union_left] at hdis
  obtain ⟨hXS, hYS⟩ := hdis
  -- the vertices of the pieces avoid `X`, `Y` and `S`
  have hCL : C ⊆ L'.verts := subset_verts hC.mem
  have hDM : D ⊆ (exch L' C D L'' hC).verts := subset_verts (mem_exch.2 (.inr ⟨∅,
    Finset.ssubset_iff_subset_ne.2 ⟨empty_subset _, hC.nonempty_left.ne_empty.symm⟩, ∅,
    hC.empty_mem, by rw [empty_union, union_empty]⟩))
  have hL''v : L''.verts ⊆ L'.verts := by
    intro x hx
    have : {x} ∈ L'.link C := by
      rw [hC.link_eq]
      exact mem_join.2 ⟨∅, mem_boundary.2 (Finset.ssubset_iff_subset_ne.2 ⟨empty_subset _,
        hC.nonempty_right.ne_empty.symm⟩), {x}, mem_verts.1 hx, empty_union _⟩
    exact subset_verts (mem_link'.1 this).2 (mem_union_right _ (mem_singleton_self x))
  have avoid : ∀ {T : Finset V}, T ⊆ L'.verts ∨ T ⊆ (exch L' C D L'' hC).verts →
      Disjoint X T ∧ Disjoint Y T ∧ Disjoint (suppList S) T := by
    intro T hT
    have hF : Disjoint T (X ∪ Y ∪ suppList S) := by
      rcases hT with hT | hT
      · exact disjoint_of_subset_left hT hL'
      · exact disjoint_of_subset_left hT hM
    rw [disjoint_union_right, disjoint_union_right] at hF
    exact ⟨hF.1.1.symm, hF.1.2.symm, hF.2.symm⟩
  obtain ⟨hXC, hYC, hSC⟩ := avoid (.inl hCL)
  obtain ⟨hXD, hYD, hSD⟩ := avoid (.inr hDM)
  obtain ⟨hXL, hYL, hSL⟩ := avoid (.inl subset_rfl)
  obtain ⟨hXL'', hYL'', hSL''⟩ := avoid (.inl hL''v)
  obtain ⟨hXM, hYM, -⟩ := avoid (.inr subset_rfl)
  have hXP : Disjoint X (stdJoin S).verts := disjoint_of_subset_right hPv hXS
  have hYP : Disjoint Y (stdJoin S).verts := disjoint_of_subset_right hPv hYS
  have hCP : Disjoint C (stdJoin S).verts := disjoint_of_subset_right hPv hSC.symm
  have hDP : Disjoint D (stdJoin S).verts := disjoint_of_subset_right hPv hSD.symm
  have hPL : Disjoint (stdJoin S).verts L'.verts := disjoint_of_subset_left hPv hSL
  -- the three exchanges
  have h₁ := isExch_union hP0 h hC hDK hXC hXD hYC hYD hXP hCP hDP hYL hPL hXL''
  have h₂ := isExch_after hP0 h hC h₁ hXC hXD hYC hYD hXP hYP hDP hYL hPL hXL'' hYL'' hXM hYM
  have hK' := isExch_exch h
  have hDK' : D ∉ exch K X Y ((stdJoin S).join L') h := by
    rw [mem_exch]
    rintro (⟨hK, -⟩ | ⟨t, -, u, -, he⟩)
    · exact hDK hK
    · obtain ⟨y, hy⟩ := h.nonempty_right
      exact disjoint_left.1 hYD hy (he ▸ mem_union_left u (mem_union_right t hy))
  have h' := isExch_union hP0 hK' hC hDK' hYC hYD hXC hXD hYP hCP hDP hXL hPL hYL''
  -- the induction hypotheses
  have hstd : ∀ {Z : Finset V}, Z.Nonempty → Disjoint Z (suppList S) → IsStdList (Z :: S) :=
    fun hZ hZS => ⟨hZ, hZS, hS⟩
  have e₁ : BistellarEquivIn K (exch K (X ∪ C) D (((boundary Y).join (stdJoin S)).join L'') h₁) :=
    exch_of_sphere (ihd _ hD''d) (S := Y :: S) (hstd h.nonempty_right hYS) rfl
      (by
        simp only [suppList]
        exact disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨disjoint_union_right.2
          ⟨h.disjoint, hXS⟩, disjoint_union_right.2 ⟨hYC.symm, hSC.symm⟩⟩,
          disjoint_union_right.2 ⟨hYD.symm, hSD.symm⟩⟩)
      hsph
      (by
        simp only [suppList]
        exact disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨disjoint_union_right.2
          ⟨hXL''.symm, hC.disjoint_left_verts.symm⟩, hC.disjoint_right_verts.symm⟩,
          disjoint_union_right.2 ⟨hYL''.symm, hSL''.symm⟩⟩)
      h₁
  have e₂ := he₂ h₁ h₂
  have e₃ : BistellarEquivIn (exch K X Y ((stdJoin S).join L') h)
      (exch (exch K X Y ((stdJoin S).join L') h) (Y ∪ C) D
        (((boundary X).join (stdJoin S)).join L'') h') :=
    exch_of_sphere (ihd _ hD''d) (S := X :: S) (hstd h.nonempty_left hXS) rfl
      (by
        simp only [suppList]
        exact disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨disjoint_union_right.2
          ⟨h.disjoint.symm, hYS⟩, disjoint_union_right.2 ⟨hXC.symm, hSC.symm⟩⟩,
          disjoint_union_right.2 ⟨hXD.symm, hSD.symm⟩⟩)
      hsph
      (by
        simp only [suppList]
        exact disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨disjoint_union_right.2
          ⟨hYL''.symm, hC.disjoint_left_verts.symm⟩, hC.disjoint_right_verts.symm⟩,
          disjoint_union_right.2 ⟨hXL''.symm, hSL''.symm⟩⟩)
      h'
  rw [exch_comm hP0 hXC hYC hYD hXP hDP hXL hPL hXL'' h hC h₁ h₂ h'] at e₂
  exact e₁.trans (e₂.trans e₃.symm)

/-- **The first case of the inductive step**: the first move `κ(C, D)` of the chain has `D ∉ K`. -/
lemma exch_first_case [Infinite V] {d r : ℕ}
    (ihd : ∀ d' < d, ∀ r', ExchStmt (V := V) d' r') (ihr : ExchStmt (V := V) d r)
    {S : List (Finset V)} {L' K L'' : SComplex V} {X Y D₀ C D : Finset V}
    (hS : IsStdList S) (hD₀ : #D₀ = d) (hdis : Disjoint (X ∪ Y) (suppList S))
    (hL' : Disjoint L'.verts (X ∪ Y ∪ suppList S)) (hC : IsExch L' C D L'')
    (hMN : StepChain (X ∪ Y ∪ suppList S) r (exch L' C D L'' hC) (boundary D₀))
    (hL'' : ∃ D'', #D'' < d ∧ StellarEquivIn L'' (boundary D''))
    (hDK : D ∉ K) (h : IsExch K X Y ((stdJoin S).join L')) :
    BistellarEquivIn K (exch K X Y ((stdJoin S).join L') h) :=
  exch_of_comm ihd hS hdis hL' hC hMN.source hL'' hDK h fun _ h₂ =>
    ihr S _ _ X Y D₀ hS hD₀ hdis hMN h₂

/-- Exchanges with equal data are equal. -/
lemma exch_congr' {K K' L L' : SComplex V} {A A' B B' : Finset V} (hK : K = K') (hA : A = A')
    (hB : B = B') (hL : L = L') (h : IsExch K A B L) (h' : IsExch K' A' B' L') :
    exch K A B L h = exch K' A' B' L' h' := by
  subst hK hA hB hL
  rfl

/-- A swap of two elements outside a finite set fixes it. -/
lemma map_swap_finset {x y : V} {T : Finset V} (hx : x ∉ T) (hy : y ∉ T) :
    T.map (Equiv.swap x y).toEmbedding = T := by
  ext z
  rw [Finset.mem_map_equiv, Equiv.symm_swap]
  by_cases hzx : z = x
  · subst hzx
    rw [Equiv.swap_apply_left]
    exact ⟨fun h => absurd h hy, fun h => absurd h hx⟩
  · by_cases hzy : z = y
    · subst hzy
      rw [Equiv.swap_apply_right]
      exact ⟨fun h => absurd h hx, fun h => absurd h hy⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]

/-- **The main induction** of Lickorish's proof of Pachner's theorem: for every size `d` of the
model simplex and every length `r` of the chain, the statement `ExchStmt d r` holds. -/
theorem exchStmt [Infinite V] : ∀ d r, ExchStmt (V := V) d r := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro r
  induction r with
  | zero =>
    intro S L' K X Y D₀ hS hD₀ hdis hch h
    cases hch with
    | refl hL =>
    rcases Nat.lt_or_ge #D₀ 2 with hlt | hge
    · rcases Nat.lt_or_ge #D₀ 1 with hlt' | hge'
      · have : D₀ = ∅ := card_eq_zero.1 (by omega)
        subst this
        exfalso
        obtain ⟨t, -, u, hu, -⟩ := mem_join.1 h.empty_mem
        rw [mem_boundary] at hu
        exact Finset.not_ssubset_empty u hu
      · obtain ⟨x, rfl⟩ := card_eq_one.1 (by omega : #D₀ = 1)
        have he : (stdJoin S).join (boundary {x}) = stdJoin S := by
          rw [boundary_singleton, join_simplex_empty]
        have h' : IsExch K X Y (stdJoin S) := he ▸ h
        rw [exch_congr rfl he h h']
        exact bistellarEquivIn_exch_std _ S rfl hS K X Y hdis h'
    · have hv : (boundary D₀).verts = D₀ := verts_boundary hge
      rw [hv] at hL
      have he : (stdJoin S).join (boundary D₀) = stdJoin (D₀ :: S) := join_comm _ _
      have h' : IsExch K X Y (stdJoin (D₀ :: S)) := he ▸ h
      rw [exch_congr rfl he h h']
      refine bistellarEquivIn_exch_std _ (D₀ :: S) rfl ⟨card_pos.1 (by omega),
        disjoint_of_subset_right subset_union_right hL, hS⟩ K X Y ?_ h'
      simp only [suppList]
      exact disjoint_union_right.2 ⟨(disjoint_of_subset_right subset_union_left hL).symm, hdis⟩
  | succ r ihr =>
    intro S L' K X Y D₀ hS hD₀ hdis hch h
    cases hch with
    | step hLM hL hMN =>
    obtain ⟨C, D, L'', hC, rfl, hface⟩ := exists_exch_of_step hLM
    have hL'sph : StellarEquivIn L' (boundary D₀) := by
      have hM := hMN.stellarEquivIn
      rcases hLM with h' | h'
      · exact (Relation.EqvGen.rel _ _ h').trans _ _ _ hM
      · exact (Relation.EqvGen.rel _ _ h').symm.trans _ _ _ hM
    have hsph : ∃ D'', #D'' < d ∧ StellarEquivIn L'' (boundary D'') := by
      rcases hface with ⟨hCm, hCne, hLe⟩ | ⟨hDm, hDne, hLe⟩
      · obtain ⟨D'', hc, hl⟩ := link_of_stellarEquivIn_boundary hL'sph hCm hCne
        rw [hLe]
        exact ⟨D'', by have := card_pos.2 hCne; omega, hl⟩
      · obtain ⟨D'', hc, hl⟩ := link_of_stellarEquivIn_boundary hMN.stellarEquivIn hDm hDne
        rw [hLe]
        exact ⟨D'', by have := card_pos.2 hDne; omega, hl⟩
    by_cases hDK : D ∈ K
    swap
    · exact exch_first_case (fun d' hd' => ihd d' hd') ihr hS hD₀ hdis hL hC hMN hsph hDK h
    have hMF := hMN.source
    have hDM : D ⊆ (exch L' C D L'' hC).verts := subset_verts (mem_exch.2 (.inr ⟨∅,
      Finset.ssubset_iff_subset_ne.2 ⟨empty_subset _, hC.nonempty_left.ne_empty.symm⟩, ∅,
      hC.empty_mem, by rw [empty_union, union_empty]⟩))
    have hDF : Disjoint D (X ∪ Y ∪ suppList S) := disjoint_of_subset_left hDM hMF
    have hL''v : L''.verts ⊆ L'.verts := by
      intro x hx
      have : {x} ∈ L'.link C := by
        rw [hC.link_eq]
        exact mem_join.2 ⟨∅, mem_boundary.2 (Finset.ssubset_iff_subset_ne.2 ⟨empty_subset _,
          hC.nonempty_right.ne_empty.symm⟩), {x}, mem_verts.1 hx, empty_union _⟩
      exact subset_verts (mem_link'.1 this).2 (mem_union_right _ (mem_singleton_self x))
    by_cases h1 : #D = 1
    · -- `D` is a vertex: rename it to a new vertex
      obtain ⟨x, rfl⟩ := card_eq_one.1 h1
      have hxL : x ∉ L'.verts := fun hx => hC.notMem (mem_verts.1 hx)
      obtain ⟨x', hx'⟩ := Infinite.exists_notMem_finset (K.verts ∪ (X ∪ Y ∪ suppList S) ∪ L'.verts)
      simp only [mem_union, not_or] at hx'
      obtain ⟨⟨hx'K, hx'F⟩, hx'L⟩ := hx'
      have hxF : x ∉ X ∪ Y ∪ suppList S := fun h' => disjoint_left.1 hDF (mem_singleton_self x) h'
      have hx'F' : x' ∉ X ∪ Y ∪ suppList S := by
        simp only [mem_union, not_or]; exact hx'F
      have hFσ := map_swap_finset hxF hx'F'
      have hLσ : L'.map (Equiv.swap x x').toEmbedding = L' := map_swap_eq_self hxL hx'L
      have hL''σ : L''.map (Equiv.swap x x').toEmbedding = L'' :=
        map_swap_eq_self (fun h' => hxL (hL''v h')) (fun h' => hx'L (hL''v h'))
      have hCσ : C.map (Equiv.swap x x').toEmbedding = C :=
        map_swap_finset (fun h' => hxL (subset_verts hC.mem h'))
          (fun h' => hx'L (subset_verts hC.mem h'))
      have hDσ : ({x} : Finset V).map (Equiv.swap x x').toEmbedding = {x'} := by
        rw [map_singleton, Equiv.toEmbedding_apply, Equiv.swap_apply_left]
      have hC' : IsExch L' C {x'} L'' := by
        have := hC.map (Equiv.swap x x').toEmbedding
        rwa [hLσ, hCσ, hDσ, hL''σ] at this
      have hMσ : (exch L' C {x} L'' hC).map (Equiv.swap x x').toEmbedding =
          exch L' C {x'} L'' hC' := by
        rw [map_exch]
        exact exch_congr' hLσ hCσ hDσ hL''σ _ _
      have hch' := hMN.map (Equiv.swap x x')
      rw [hFσ, hMσ, map_boundary] at hch'
      exact exch_first_case (fun d' hd' => ihd d' hd') ihr hS (by rw [card_map]; exact hD₀) hdis
        hL hC' hch' hsph (fun h' => hx'K (mem_verts.2 h')) h
    · -- a vertex `u` of `D` is first moved to a new vertex `v`
      have hD2 : 2 ≤ #D := by have := card_pos.2 hC.nonempty_right; omega
      obtain ⟨u, huD⟩ := hC.nonempty_right
      have huL : {u} ∈ L' := by
        have : {u} ∈ L'.link C := by
          rw [hC.link_eq]
          refine mem_join.2 ⟨{u}, mem_boundary.2 (Finset.ssubset_iff_subset_ne.2
            ⟨singleton_subset_iff.2 huD, fun e => ?_⟩), ∅, hC.empty_mem, union_empty _⟩
          rw [← e, card_singleton] at hD2
          omega
        exact down_mem (mem_link'.1 this).2 subset_union_right
      have huF : u ∉ X ∪ Y ∪ suppList S := fun h' => disjoint_left.1 hDF huD h'
      obtain ⟨v, hv⟩ := Infinite.exists_notMem_finset
        (K.verts ∪ (X ∪ Y ∪ suppList S) ∪ L'.verts ∪ D)
      simp only [mem_union, not_or] at hv
      obtain ⟨⟨⟨hvK, hvF⟩, hvL⟩, hvD⟩ := hv
      have hvF' : v ∉ X ∪ Y ∪ suppList S := by simp only [mem_union, not_or]; exact hvF
      have hFσ := map_swap_finset huF hvF'
      have hCu := isExch_starAt huL (singleton_nonempty u) hvL
      have hL'u : exch L' {u} {v} (L'.link {u}) hCu = L'.map (Equiv.swap u v).toEmbedding := by
        rw [exch_eq_starAt huL (singleton_nonempty u) hvL, starAt_singleton hvL]
      have hLσF : Disjoint (L'.map (Equiv.swap u v).toEmbedding).verts (X ∪ Y ∪ suppList S) := by
        rw [verts_map, ← hFσ]
        exact (Finset.disjoint_map _).2 hL
      obtain ⟨Du, hDu, hlu⟩ := link_of_stellarEquivIn_boundary hL'sph huL (singleton_nonempty u)
      have hvKs : ({v} : Finset V) ∉ K := fun h' => hvK (mem_verts.2 h')
      refine exch_of_comm (fun d' hd' => ihd d' hd') hS hdis hL hCu (by rw [hL'u]; exact hLσF)
        ⟨Du, by rw [card_singleton] at hDu; omega, hlu⟩ hvKs h fun h₁ h₂ => ?_
      -- the exchange `κ(X, Y)` after `κ(X ∪ u, v)`: the first case for the renamed chain
      have hCσ := hC.map (Equiv.swap u v).toEmbedding
      have hch' := hMN.map (Equiv.swap u v)
      rw [hFσ, map_exch hC, map_boundary] at hch'
      have h₂' : IsExch (exch K (X ∪ {u}) {v} _ h₁) X Y
          ((stdJoin S).join (L'.map (Equiv.swap u v).toEmbedding)) := hL'u ▸ h₂
      rw [exch_congr rfl (by rw [hL'u]) h₂ h₂']
      obtain ⟨D'', hD''d, hsph''⟩ := hsph
      have hsphσ : ∃ D₂, #D₂ < d ∧ StellarEquivIn (L''.map (Equiv.swap u v).toEmbedding)
          (boundary D₂) :=
        ⟨D''.map (Equiv.swap u v).toEmbedding, by rw [card_map]; exact hD''d, by
          rw [← map_boundary]; exact hsph''.map _⟩
      refine exch_first_case (fun d' hd' => ihd d' hd') ihr hS (by rw [card_map]; exact hD₀) hdis
        hLσF hCσ hch' hsphσ ?_ h₂'
      -- the renamed new face is not a face after `κ(X ∪ u, v)`
      rw [map_swap_face hvD, ite_eq_left huD, mem_exch]
      rintro (⟨hK, -⟩ | ⟨t, ht, w, hw, he⟩)
      · exact hvK (subset_verts hK (mem_insert_self v _))
      · apply hC.notMem
        have hwD : w = D.erase u := by
          have hP := verts_stdJoin_subset S
          have hwv : ∀ z ∈ w, z ∈ Y ∨ z ∈ suppList S ∨ z ∈ L'.verts := by
            intro z hz
            have := verts_triple_subset Y (stdJoin S) (L'.link {u}) (subset_verts hw hz)
            simp only [mem_union] at this
            rcases this with (h3 | h3) | h3
            · exact .inl h3
            · exact .inr (.inl (hP h3))
            · exact .inr (.inr (verts_link_subset L' {u} h3))
          ext z
          constructor
          · intro hz
            have : z ∈ insert v (D.erase u) := he ▸ mem_union_right _ hz
            rcases mem_insert.1 this with e | e
            · subst e
              rcases hwv z hz with h3 | h3 | h3
              · exact absurd (mem_union_left _ (mem_union_right _ h3)) hvF'
              · exact absurd (mem_union_right _ h3) hvF'
              · exact absurd h3 hvL
            · exact e
          · intro hz
            have : z ∈ t ∪ {v} ∪ w := he.symm ▸ mem_insert_of_mem hz
            rcases mem_union.1 this with h3 | h3
            · rcases mem_union.1 h3 with h4 | h4
              · rcases mem_union.1 (ht.subset h4) with h5 | h5
                · exact absurd (mem_union_left _ (mem_union_left _ h5))
                    (disjoint_left.1 hDF (mem_of_mem_erase hz))
                · exact absurd (mem_singleton.1 h5) (ne_of_mem_erase hz)
              · exact absurd (mem_singleton.1 h4 ▸ mem_of_mem_erase hz) hvD
            · exact h3
        -- `w` lies in the `L'`-part
        obtain ⟨bp, hbp, l, hl, hwe⟩ := mem_join.1 hw
        obtain ⟨b, hb, p, hp, rfl⟩ := mem_join.1 hbp
        have hbpe : b ∪ p = ∅ := by
          refine eq_empty_of_forall_notMem fun z hz => ?_
          have hzw : z ∈ D.erase u := hwD ▸ hwe ▸ mem_union_left l hz
          have hzD := disjoint_left.1 hDF (mem_of_mem_erase hzw)
          rcases mem_union.1 hz with h3 | h3
          · exact hzD (mem_union_left _ (mem_union_right _ ((mem_boundary.1 hb).subset h3)))
          · exact hzD (mem_union_right _ (verts_stdJoin_subset S (subset_verts hp h3)))
        rw [hbpe, empty_union] at hwe
        have hl' := mem_link'.1 hl
        rw [hwe, hwD, ← insert_eq, insert_erase huD] at hl'
        exact hl'.2

/-! ## Pachner's theorem -/

/-- **Every stellar subdivision of a closed combinatorial manifold is a composite of bistellar
moves** (inside an infinite vertex type). -/
theorem bistellarEquivIn_starAt [Infinite V] {n : ℕ} {K : SComplex V} (hK : IsMfdIn false n K)
    {A : Finset V} (hA : A ∈ K) (hne : A.Nonempty) {a : V} (ha : a ∉ K.verts) :
    BistellarEquivIn K (K.starAt A a) := by
  obtain ⟨m, -, hSB⟩ := (isMfdIn_main false n).1 K hK A hA hne
  obtain ⟨D₁, -, hsph⟩ : ∃ D₁ : Finset V, #D₁ = m + 1 ∧ StellarEquivIn (K.link A) (boundary D₁) := by
    rcases hSB with h' | ⟨hb, -⟩
    · exact h'
    · exact absurd hb (by decide)
  have h := isExch_starAt hA hne ha
  have he : (stdJoin ([] : List (Finset V))).join (K.link A) = K.link A := simplex_empty_join _
  have h' : IsExch K A {a} ((stdJoin ([] : List (Finset V))).join (K.link A)) := by
    rw [he]; exact h
  have hL : Disjoint (K.link A).verts (A ∪ {a} ∪ suppList ([] : List (Finset V))) := by
    simp only [suppList, union_empty]
    exact disjoint_union_right.2 ⟨(disjoint_verts_link K A).symm,
      disjoint_singleton_right.2 fun h'' => ha (verts_link_subset K A h'')⟩
  obtain ⟨D₂, r, hD₂, hch⟩ := exists_chain_of_stellarEquivIn_boundary hsph hL
  have := exchStmt #D₂ r [] (K.link A) K A {a} D₂ trivial rfl (by simp [suppList]) hch h'
  rwa [exch_congr rfl he h' h, exch_eq_starAt hA hne ha] at this

/-- **Pachner's theorem inside an infinite vertex type**: a closed combinatorial manifold is
bistellar equivalent to every complex stellar equivalent to it. -/
theorem StellarEquivIn.bistellarEquivIn [Infinite V] {n : ℕ} {K L : SComplex V}
    (h : StellarEquivIn K L) (hK : IsMfdIn false n K) : BistellarEquivIn K L := by
  have hinv : ∀ {X Y : SComplex V}, StellarEquivIn X Y → (IsMfdIn false n X ↔ IsMfdIn false n Y) :=
    fun hXY => isMfdIn_iff_of_stellarEquivIn (isMfdIn_main false n).1 hXY
  induction h with
  | rel X Y hXY =>
    obtain ⟨hA, hne, ha⟩ := hXY
    exact bistellarEquivIn_starAt hK hA hne ha
  | refl => exact .refl _
  | symm X Y hXY ih => exact (ih ((hinv hXY).2 hK)).symm
  | trans X Y Z hXY _ ih₁ ih₂ => exact (ih₁ hK).trans (ih₂ ((hinv hXY).1 hK))

/-- **Pachner's theorem, stellar version: closed combinatorial manifolds are stellar equivalent
iff related by bistellar moves** (no renamings of the vertices are needed). The closed
combinatorial manifolds are the stellar ones of `Lightlike/PL/Manifold.lean` (Lickorish 1999,
Definition 3.1). Lickorish's Theorem 5.9 (Newman, Pachner) has "PL homeomorphic" in place of
"stellar equivalent"; that form is `pachner_plHomeomorphic`, from this theorem and Newman's theorem.

The complexes are finite (`SComplex`). Finiteness is needed: the quadrant `[0, ∞)²` cut into unit squares, every square split along its `/` diagonal,
versus every square split along its `\` diagonal, are PL homeomorphic, but no finite sequence of bistellar moves
and isomorphisms joins them. The boundary is essential: on the whole plane the two grids are mirror images, hence
isomorphic. -/
theorem pachner {n : ℕ} {K L : SComplex V} (hK : IsClosedCombManifold n K) :
    StellarEquiv K L ↔ BistellarEquiv K L :=
  ⟨fun h => StellarEquivIn.bistellarEquivIn h (isMfdIn_false_iff.2 hK),
    BistellarEquiv.stellarEquiv⟩

/-- **Renamings are bistellar**: a closed combinatorial manifold is bistellar equivalent to every
complex obtained from it by renaming the vertices, so bistellar equivalence needs no separate
simplicial isomorphisms. -/
theorem IsClosedCombManifold.bistellarEquiv_map {n : ℕ} {K : SComplex V}
    (hK : IsClosedCombManifold n K) (e : Equiv.Perm V) : BistellarEquiv K (K.map e.toEmbedding) :=
  (pachner hK).1 (StellarEquiv.map_perm K e)

/-- **Isomorphisms are bistellar**: if `L` consists of the images of the faces of a closed
combinatorial manifold `K` under a map that is injective on the vertices of `K`, then `K` and `L`
are bistellar equivalent. -/
theorem IsClosedCombManifold.bistellarEquiv_of_iso {n : ℕ} {K L : SComplex V} {f : V → V}
    (hK : IsClosedCombManifold n K) (hf : Set.InjOn f K.verts)
    (hL : L.faces = K.faces.image (Finset.image f)) : BistellarEquiv K L :=
  (pachner hK).1 (StellarEquiv.of_iso hf hL)

end SComplex

end Lightlike.PL
