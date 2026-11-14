import Lightlike.PL.Stellar

/-!
# Invariants of stellar equivalence: dimension and connectedness

Two simple invariants of stellar equivalence, used to tell PL spheres and balls apart from other
complexes:

* `maxCard K`: the largest number of vertices of a face (the dimension plus one).
* `IsConnected K`: `K` has a vertex, and every set of vertices that each face either lies in or
  misses contains all vertices or none. (A set with this property is a union of components of the
  1-skeleton, so this is connectedness of the 1-skeleton, stated without paths.)

## Main results

* `maxCard_starAt`, `maxCard_map`, `StellarEquiv.maxCard_eq`: the dimension is invariant under
  subdivisions, injective maps of the vertices and stellar equivalence.
* `isConnected_starAt_iff`, `isConnected_map_iff`, `StellarEquiv.isConnected_iff`:
  so is connectedness.
* `maxCard_simplex`, `maxCard_boundary`, `isConnected_simplex`, `isConnected_boundary`: the values
  on simplices and their boundaries; the boundary of a simplex with at least three vertices is
  connected, the 0-sphere (two points) is not.
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V : Type*} [DecidableEq V]

/-! ## Dimension -/

/-- The largest number of vertices of a face of `K` (its dimension plus one; `0` for the complexes
`∅` and `{∅}`). -/
def maxCard (K : SComplex V) : ℕ := K.faces.sup card

omit [DecidableEq V] in
lemma card_le_maxCard {K : SComplex V} {s : Finset V} (hs : s ∈ K) : #s ≤ K.maxCard :=
  le_sup (f := card) (mem_faces.2 hs)

omit [DecidableEq V] in
lemma maxCard_le {K : SComplex V} {n : ℕ} (h : ∀ s ∈ K, #s ≤ n) : K.maxCard ≤ n :=
  Finset.sup_le fun s hs => h s hs

omit [DecidableEq V] in
lemma exists_card_eq_maxCard {K : SComplex V} (hK : ∅ ∈ K) : ∃ s ∈ K, #s = K.maxCard := by
  obtain ⟨s, hs, he⟩ := exists_mem_eq_sup K.faces ⟨∅, hK⟩ card
  exact ⟨s, hs, he.symm⟩

/-- **Stellar subdivision preserves the dimension.** -/
theorem maxCard_starAt {K : SComplex V} {A : Finset V} {a : V} (hA : A ∈ K) (hne : A.Nonempty)
    (ha : a ∉ K.verts) : (K.starAt A a).maxCard = K.maxCard := by
  apply le_antisymm
  · refine maxCard_le fun s hs => ?_
    rcases mem_starAt.1 hs with ⟨hs, -⟩ | ⟨t, ht, hAt, hAtK, rfl⟩
    · exact card_le_maxCard hs
    · refine (card_insert_le a t).trans ((?_ : #t + 1 ≤ #(A ∪ t)).trans (card_le_maxCard hAtK))
      obtain ⟨x, hxA, hxt⟩ := not_subset.1 hAt
      calc #t + 1 = #(insert x t) := (card_insert_of_notMem hxt).symm
        _ ≤ #(A ∪ t) := card_le_card (insert_subset (mem_union_left _ hxA) subset_union_right)
  · obtain ⟨s, hs, he⟩ := exists_card_eq_maxCard (empty_mem hA)
    rw [← he]
    by_cases hAs : A ⊆ s
    · obtain ⟨x, hx⟩ := hne
      have hxs : x ∈ s := hAs hx
      have hat : a ∉ s.erase x := fun h => notMem_of_notMem_verts ha hs (mem_of_mem_erase h)
      have hmem : insert a (s.erase x) ∈ K.starAt A a := by
        refine (insert_mem_starAt ha hat).2 ⟨down_mem hs (erase_subset x s), fun h => ?_, ?_⟩
        · exact (mem_erase.1 (h hx)).1 rfl
        · exact down_mem hs (union_subset hAs (erase_subset x s))
      refine le_trans (le_of_eq ?_) (card_le_maxCard hmem)
      rw [card_insert_of_notMem hat, card_erase_of_mem hxs]
      have : 0 < #s := card_pos.2 ⟨x, hxs⟩
      omega
    · exact card_le_maxCard ((mem_starAt_of_notMem (notMem_of_notMem_verts ha hs)).2 ⟨hs, hAs⟩)

omit [DecidableEq V] in
/-- Injective maps of the vertices preserve the dimension. -/
theorem maxCard_map {W : Type*} [DecidableEq W] (K : SComplex V) (f : V ↪ W) :
    (K.map f).maxCard = K.maxCard := by
  apply le_antisymm
  · refine maxCard_le fun s hs => ?_
    obtain ⟨t, ht, rfl⟩ := mem_map.1 hs
    rw [card_map]
    exact card_le_maxCard ht
  · refine maxCard_le fun s hs => ?_
    rw [← card_map f]
    exact card_le_maxCard (map_mem_map.2 hs)

/-- The dimension is an invariant of stellar equivalence inside `V`. -/
theorem StellarEquivIn.maxCard_eq {K L : SComplex V} (h : StellarEquivIn K L) :
    K.maxCard = L.maxCard := by
  induction h with
  | rel K L h =>
    obtain ⟨hA, hne, ha⟩ := h
    exact (maxCard_starAt hA hne ha).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **The dimension is an invariant of stellar equivalence.** -/
theorem StellarEquiv.maxCard_eq {K L : SComplex V} (h : StellarEquiv K L) :
    K.maxCard = L.maxCard := by
  have := StellarEquivIn.maxCard_eq h
  simpa only [lift, maxCard_map] using this

omit [DecidableEq V] in
/-- The `n`-simplex has faces of `n + 1` vertices. -/
lemma maxCard_simplex (A : Finset V) : (simplex A).maxCard = #A :=
  le_antisymm (maxCard_le fun _ hs => card_le_card (mem_simplex.1 hs))
    (card_le_maxCard (mem_simplex.2 subset_rfl))

/-- The boundary of the `n`-simplex has faces of `n` vertices. -/
lemma maxCard_boundary {A : Finset V} (hA : A.Nonempty) : (boundary A).maxCard = #A - 1 := by
  apply le_antisymm
  · refine maxCard_le fun s hs => ?_
    have := card_lt_card (mem_boundary.1 hs)
    omega
  · obtain ⟨x, hx⟩ := hA
    have := card_le_maxCard (mem_boundary.2 (erase_ssubset hx) : A.erase x ∈ boundary A)
    rwa [card_erase_of_mem hx] at this

/-! ## Connectedness -/

/-- `S` **separates** `K`: every face of `K` lies in `S` or misses it. -/
def Separates (S : Finset V) (K : SComplex V) : Prop := ∀ s ∈ K, s ⊆ S ∨ Disjoint s S

/-- `K` is **connected**: it has a vertex, and every set separating `K` contains all of its
vertices or none of them. -/
def IsConnected (K : SComplex V) : Prop :=
  K.verts.Nonempty ∧ ∀ S : Finset V, Separates S K → K.verts ⊆ S ∨ Disjoint K.verts S

/-- In a stellar subdivision at `A`, a vertex `x ∈ A` that is still a vertex shares a face with the
apex, so a separating set contains both or neither. -/
lemma Separates.apex_iff {K : SComplex V} {A : Finset V} {a : V} {S : Finset V}
    (hS : Separates S (K.starAt A a)) (hA : A ∈ K) (ha : a ∉ K.verts) {x : V} (hx : x ∈ A)
    {y : V} (hy : y ∈ A) (hxy : x ≠ y) : (x ∈ S ↔ a ∈ S) := by
  have hat : a ∉ A.erase y := fun h => notMem_of_notMem_verts ha hA (mem_of_mem_erase h)
  have hmem : insert a (A.erase y) ∈ K.starAt A a := by
    refine (insert_mem_starAt ha hat).2 ⟨down_mem hA (erase_subset y A), fun h => ?_, ?_⟩
    · exact (mem_erase.1 (h hy)).1 rfl
    · rwa [union_eq_left.2 (erase_subset y A)]
  have hxF : x ∈ insert a (A.erase y) := mem_insert_of_mem (mem_erase.2 ⟨hxy, hx⟩)
  rcases hS _ hmem with h | h
  · exact ⟨fun _ => h (mem_insert_self a _), fun _ => h hxF⟩
  · exact ⟨fun hxS => absurd hxS (disjoint_left.1 h hxF),
      fun haS => absurd haS (disjoint_left.1 h (mem_insert_self a _))⟩

/-- The vertices of a stellar subdivision: the apex, and the vertices `x` of `K` with `A ≠ {x}`. -/
lemma mem_verts_starAt {K : SComplex V} {A : Finset V} {a : V} (hA : A ∈ K) (hne : A.Nonempty)
    (ha : a ∉ K.verts) {x : V} : x ∈ (K.starAt A a).verts ↔ x = a ∨ (x ∈ K.verts ∧ ¬ A ⊆ {x}) := by
  by_cases hxa : x = a
  · subst hxa
    exact ⟨fun _ => .inl rfl, fun _ => apex_mem_verts hA hne⟩
  · rw [mem_verts, mem_verts, mem_starAt_of_notMem (by simpa using Ne.symm hxa)]
    simp [hxa]

/-- **Stellar subdivision preserves connectedness**, in both directions. -/
theorem isConnected_starAt_iff {K : SComplex V} {A : Finset V} {a : V} (hA : A ∈ K)
    (hne : A.Nonempty) (ha : a ∉ K.verts) : (K.starAt A a).IsConnected ↔ K.IsConnected := by
  have haA : a ∉ A := notMem_of_notMem_verts ha hA
  have hAv : A ⊆ K.verts := subset_verts hA
  obtain ⟨x₀, hx₀⟩ := hne
  -- a vertex `v` of `K` with `A ⊆ {v}` is the unique element of `A`
  have hsingle : ∀ v, A ⊆ {v} → A = {v} := fun v h =>
    (subset_singleton_iff.1 h).resolve_left (ne_empty_of_mem hx₀)
  constructor
  · rintro ⟨-, hconn⟩
    refine ⟨⟨x₀, hAv hx₀⟩, fun S hS => ?_⟩
    -- the separating set for the subdivision
    let S' : Finset V := if A ⊆ S then insert a S else S.erase a
    have hAS : A ⊆ S ∨ Disjoint A S := hS A hA
    have hS' : Separates S' (K.starAt A a) := by
      intro s hs
      rcases mem_starAt.1 hs with ⟨hs, -⟩ | ⟨t, -, -, hAt, rfl⟩
      · have has : a ∉ s := notMem_of_notMem_verts ha hs
        rcases hS s hs with h | h
        · left; intro y hy
          simp only [S']; split_ifs
          · exact mem_insert_of_mem (h hy)
          · exact mem_erase.2 ⟨fun e => has (e ▸ hy), h hy⟩
        · right; refine disjoint_left.2 fun y hy hyS => ?_
          simp only [S'] at hyS; split_ifs at hyS
          · rcases mem_insert.1 hyS with e | e
            · exact has (e ▸ hy)
            · exact disjoint_left.1 h hy e
          · exact disjoint_left.1 h hy (mem_of_mem_erase hyS)
      · rcases hS _ hAt with h | h
        · have hAS' : A ⊆ S := subset_union_left.trans h
          left; intro y hy
          simp only [S', ite_eq_left hAS']
          rcases mem_insert.1 hy with e | e
          · exact e ▸ mem_insert_self a S
          · exact mem_insert_of_mem (h (mem_union_right _ e))
        · have hAS' : ¬ A ⊆ S := fun h' =>
            disjoint_left.1 h (mem_union_left _ hx₀) (h' hx₀)
          right; refine disjoint_left.2 fun y hy hyS => ?_
          simp only [S', ite_eq_right hAS'] at hyS
          rcases mem_insert.1 hy with e | e
          · exact (mem_erase.1 hyS).1 e
          · exact disjoint_left.1 h (mem_union_right _ e) (mem_of_mem_erase hyS)
    have hapex : a ∈ (K.starAt A a).verts := apex_mem_verts hA ⟨x₀, hx₀⟩
    rcases hconn S' hS' with h | h
    · have haS' : a ∈ S' := h hapex
      have hAS' : A ⊆ S := by
        by_contra hn
        simp only [S', ite_eq_right hn] at haS'
        exact (mem_erase.1 haS').1 rfl
      left; intro v hv
      by_cases hvA : A ⊆ {v}
      · rw [hsingle v hvA] at hAS'
        exact hAS' (mem_singleton_self v)
      · have hv' := h ((mem_verts_starAt hA ⟨x₀, hx₀⟩ ha).2 (.inr ⟨hv, hvA⟩))
        simp only [S', ite_eq_left hAS'] at hv'
        rcases mem_insert.1 hv' with e | e
        · exact absurd (e ▸ hv) ha
        · exact e
    · have haS' : a ∉ S' := disjoint_left.1 h hapex
      have hAS' : ¬ A ⊆ S := fun h' => by
        simp only [S', ite_eq_left h'] at haS'
        exact haS' (mem_insert_self a S)
      have hdis : Disjoint A S := hAS.resolve_left hAS'
      right; refine disjoint_left.2 fun v hv hvS => ?_
      by_cases hvA : A ⊆ {v}
      · rw [hsingle v hvA] at hdis
        exact disjoint_left.1 hdis (mem_singleton_self v) hvS
      · have hv' := (mem_verts_starAt hA ⟨x₀, hx₀⟩ ha).2 (.inr ⟨hv, hvA⟩)
        have hva : v ≠ a := fun e => ha (e ▸ hv)
        refine disjoint_left.1 h hv' ?_
        simp only [S', ite_eq_right hAS']
        exact mem_erase.2 ⟨hva, hvS⟩
  · rintro ⟨-, hconn⟩
    refine ⟨⟨a, apex_mem_verts hA ⟨x₀, hx₀⟩⟩, fun S hS => ?_⟩
    -- the separating set for `K`
    let S' : Finset V := if a ∈ S then S ∪ A else S \ A
    have hS' : Separates S' K := by
      intro s hs
      by_cases hAs : A ⊆ s
      · have hx₀s : x₀ ∈ s := hAs hx₀
        have hat : a ∉ s.erase x₀ := fun h => notMem_of_notMem_verts ha hs (mem_of_mem_erase h)
        have hF : insert a (s.erase x₀) ∈ K.starAt A a := by
          refine (insert_mem_starAt ha hat).2 ⟨down_mem hs (erase_subset x₀ s), fun h => ?_, ?_⟩
          · exact (mem_erase.1 (h hx₀)).1 rfl
          · refine down_mem hs (union_subset hAs (erase_subset x₀ s))
        rcases hS _ hF with h | h
        · have haS : a ∈ S := h (mem_insert_self a _)
          left; intro y hy
          simp only [S', ite_eq_left haS]
          by_cases hyA : y ∈ A
          · exact mem_union_right _ hyA
          · refine mem_union_left _ (h (mem_insert_of_mem (mem_erase.2 ⟨?_, hy⟩)))
            rintro rfl; exact hyA hx₀
        · have haS : a ∉ S := disjoint_left.1 h (mem_insert_self a _)
          right; refine disjoint_left.2 fun y hy hyS => ?_
          simp only [S', ite_eq_right haS] at hyS
          rw [mem_sdiff] at hyS
          refine disjoint_left.1 h (mem_insert_of_mem (mem_erase.2 ⟨?_, hy⟩)) hyS.1
          rintro rfl; exact hyS.2 hx₀
      · have hs' : s ∈ K.starAt A a := (mem_starAt_of_notMem
          (notMem_of_notMem_verts ha hs)).2 ⟨hs, hAs⟩
        -- the elements of `s ∩ A` lie in `S` exactly when `a` does
        have hsA : ∀ y ∈ s, y ∈ A → (y ∈ S ↔ a ∈ S) := by
          intro y hys hyA
          obtain ⟨z, hzA, hzs⟩ := not_subset.1 hAs
          exact hS.apex_iff hA ha hyA hzA (fun e => hzs (e ▸ hys))
        rcases hS s hs' with h | h
        · left; intro y hy
          by_cases hyA : y ∈ A
          · have haS : a ∈ S := (hsA y hy hyA).1 (h hy)
            simp only [S', ite_eq_left haS]; exact mem_union_right _ hyA
          · simp only [S']; split_ifs
            · exact mem_union_left _ (h hy)
            · exact mem_sdiff.2 ⟨h hy, hyA⟩
        · right; refine disjoint_left.2 fun y hy hyS => ?_
          simp only [S'] at hyS; split_ifs at hyS with haS
          · rcases mem_union.1 hyS with e | e
            · exact disjoint_left.1 h hy e
            · exact disjoint_left.1 h hy ((hsA y hy e).2 haS)
          · exact disjoint_left.1 h hy (mem_sdiff.1 hyS).1
    rcases hconn S' hS' with h | h
    · have hx₀S' : x₀ ∈ S' := h (hAv hx₀)
      have haS : a ∈ S := by
        by_contra hn
        simp only [S', ite_eq_right hn] at hx₀S'
        exact (mem_sdiff.1 hx₀S').2 hx₀
      left; intro v hv
      rcases (mem_verts_starAt hA ⟨x₀, hx₀⟩ ha).1 hv with rfl | ⟨hvK, hvA⟩
      · exact haS
      · have := h hvK
        simp only [S', ite_eq_left haS] at this
        rcases mem_union.1 this with e | e
        · exact e
        · obtain ⟨z, hzA, hzv⟩ := not_subset.1 hvA
          exact (hS.apex_iff hA ha e hzA (fun h' => hzv (h' ▸ mem_singleton_self v))).2 haS
    · have hx₀S' : x₀ ∉ S' := disjoint_left.1 h (hAv hx₀)
      have haS : a ∉ S := fun haS => by
        simp only [S', ite_eq_left haS] at hx₀S'
        exact hx₀S' (mem_union_right _ hx₀)
      right; refine disjoint_left.2 fun v hv hvS => ?_
      rcases (mem_verts_starAt hA ⟨x₀, hx₀⟩ ha).1 hv with rfl | ⟨hvK, hvA⟩
      · exact haS hvS
      · by_cases hvA' : v ∈ A
        · obtain ⟨z, hzA, hzv⟩ := not_subset.1 hvA
          exact haS ((hS.apex_iff hA ha hvA' hzA (fun h' => hzv (h' ▸ mem_singleton_self v))).1
            hvS)
        · refine disjoint_left.1 h hvK ?_
          simp only [S', ite_eq_right haS]
          exact mem_sdiff.2 ⟨hvS, hvA'⟩

/-- **Injective maps of the vertices preserve connectedness**, in both directions. -/
theorem isConnected_map_iff {W : Type*} [DecidableEq W] (K : SComplex V) (f : V ↪ W) :
    (K.map f).IsConnected ↔ K.IsConnected := by
  rw [IsConnected, IsConnected, verts_map, Finset.map_nonempty]
  refine and_congr Iff.rfl ⟨fun h S hS => ?_, fun h S hS => ?_⟩
  · have hS' : Separates (S.map f) (K.map f) := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := mem_map.1 hs
      rcases hS t ht with h' | h'
      · exact .inl (Finset.map_subset_map.2 h')
      · exact .inr ((Finset.disjoint_map f).2 h')
    rcases h _ hS' with h' | h'
    · exact .inl (Finset.map_subset_map.1 h')
    · exact .inr ((Finset.disjoint_map f).1 h')
  · have hS' : Separates (K.verts.filter fun x => f x ∈ S) K := by
      intro t ht
      rcases hS _ (map_mem_map.2 ht) with h' | h'
      · left; intro x hx
        exact mem_filter.2 ⟨subset_verts ht hx, h' (Finset.mem_map_of_mem f hx)⟩
      · right; refine disjoint_left.2 fun x hx hxS => ?_
        exact disjoint_left.1 h' (Finset.mem_map_of_mem f hx) (mem_filter.1 hxS).2
    rcases h _ hS' with h' | h'
    · left; intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
      exact (mem_filter.1 (h' hx)).2
    · right; refine disjoint_left.2 fun y hy hyS => ?_
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
      exact disjoint_left.1 h' hx (mem_filter.2 ⟨hx, hyS⟩)

/-- Connectedness is an invariant of stellar equivalence inside `V`. -/
theorem StellarEquivIn.isConnected_iff {K L : SComplex V} (h : StellarEquivIn K L) :
    K.IsConnected ↔ L.IsConnected := by
  induction h with
  | rel K L h =>
    obtain ⟨hA, hne, ha⟩ := h
    exact (isConnected_starAt_iff hA hne ha).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Connectedness is an invariant of stellar equivalence.** -/
theorem StellarEquiv.isConnected_iff {K L : SComplex V} (h : StellarEquiv K L) :
    K.IsConnected ↔ L.IsConnected := by
  have := StellarEquivIn.isConnected_iff h
  simpa only [lift, isConnected_map_iff] using this

/-- A simplex with at least one vertex is connected. -/
lemma isConnected_simplex {A : Finset V} (hA : A.Nonempty) : (simplex A).IsConnected := by
  rw [IsConnected, verts_simplex]
  exact ⟨hA, fun S hS => hS A (mem_simplex.2 subset_rfl)⟩

/-- The boundary of a simplex with at least three vertices (a sphere of dimension at least one) is
connected. -/
lemma isConnected_boundary {A : Finset V} (hA : 3 ≤ #A) : (boundary A).IsConnected := by
  rw [IsConnected, verts_boundary (by omega)]
  refine ⟨card_pos.1 (by omega), fun S hS => ?_⟩
  by_cases h : Disjoint A S
  · exact .inr h
  · left
    obtain ⟨x, hxA, hxS⟩ := not_disjoint_iff.1 h
    intro y hy
    have hpair : {x, y} ∈ boundary A := by
      rw [mem_boundary]
      refine Finset.ssubset_iff_subset_ne.2 ⟨insert_subset hxA (singleton_subset_iff.2 hy),
        fun e => ?_⟩
      have := card_le_two (a := x) (b := y)
      rw [e] at this
      omega
    rcases hS _ hpair with h' | h'
    · exact h' (mem_insert_of_mem (mem_singleton_self y))
    · exact absurd hxS (disjoint_left.1 h' (mem_insert_self x {y}))

/-- The 0-sphere (two points) is not connected: a deliberately wrong input for
`isConnected_boundary`. -/
lemma not_isConnected_boundary_pair {x y : V} (hxy : x ≠ y) : ¬ (boundary {x, y}).IsConnected := by
  rintro ⟨-, h⟩
  have hS : Separates {x} (boundary {x, y}) := by
    intro s hs
    rw [mem_boundary] at hs
    have hsub := hs.subset
    by_cases hx : x ∈ s
    · left; intro z hz
      rcases mem_insert.1 (hsub hz) with rfl | e
      · exact mem_singleton_self z
      · rw [mem_singleton] at e; subst e
        exact absurd (Finset.Subset.antisymm hsub (insert_subset hx (singleton_subset_iff.2 hz)))
          hs.ne
    · right; exact disjoint_singleton_right.2 hx
  rcases h {x} hS with h' | h'
  · have hy : y ∈ (boundary {x, y}).verts := by
      rw [verts_boundary (by rw [card_pair hxy])]; simp
    exact hxy (mem_singleton.1 (h' hy)).symm
  · have hx : x ∈ (boundary {x, y}).verts := by
      rw [verts_boundary (by rw [card_pair hxy])]; simp
    exact disjoint_left.1 h' hx (mem_singleton_self x)

end SComplex

end Lightlike.PL
