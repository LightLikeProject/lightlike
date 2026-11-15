import Lightlike.PL.Complex
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.EquivFin

/-!
# Stellar subdivisions, welds and stellar equivalence

The **stellar subdivision** of a complex `K` at a face `A` with a new vertex `a` (Alexander,
Newman; Lickorish 1999, §1) replaces the closed star `A * lk(A, K)` by the cone
`a * ∂A * lk(A, K)`:

  `(A, a) K = (K − A * lk(A, K)) ∪ a * ∂A * lk(A, K)`.

The faces removed are exactly the faces containing `A`. A **weld** is the inverse operation: if
the link of a vertex `a` of `K` is `∂A * L` with `A` not a face of `K`, the weld replaces
`a * ∂A * L` by `A * L`. Two complexes are **stellar equivalent** when a finite sequence of stellar
subdivisions, welds and renamings of the vertices leads from one to the other; by Newman's theorem
(Lickorish §4, `StellarEquiv.of_plHomeomorphic` in `Lightlike/PL/Newman.lean`), two complexes that
both have the empty face, or both lack it, are stellar equivalent exactly when their realisations
are PL homeomorphic.

## Definitions

* `starAt K A a`: the stellar subdivision. Its faces are the faces `s` of `K` with `A ⊄ s`, and
  the sets `insert a s` for the faces `s` with `A ⊄ s` and `A ∪ s ∈ K`.
* `weld K a A`: the faces of `K` without `a`, and the sets `A ∪ u` for the faces `u` (without `a`,
  disjoint from `A`) with `insert a ((A ∖ {x}) ∪ u) ∈ K` for every `x ∈ A`.
* `StellarStep`: a stellar subdivision at a nonempty face with a vertex of `V` not in the complex;
  `StellarEquivIn` is the equivalence relation it generates (new vertices taken from `V`).
* `StellarEquiv K L`: the lifts of `K` and `L` to `V ⊕ ℕ` are related by `StellarEquivIn`. This is
  stellar equivalence with an unlimited supply of new vertices, and does not depend on how many
  vertices `V` has to spare (inside `V`, a complex using every vertex of `V` admits no
  subdivision at all).

Both `starAt` and `weld` are defined for all arguments and always give a simplicial complex; the
theorems state the conditions under which they are the operations described above.

## Main results

* `link_starAt_apex`: the link of the new vertex is `∂A * lk(A, K)`.
* `weld_starAt`: welding undoes a stellar subdivision.
* `starAt_weld`: subdividing undoes a weld, when the link of `a` is `∂A * L`, `L` has no vertex in
  `A`, and `A` is not a face.
* `map_starAt`, `StellarEquivIn.map`: subdivisions, and hence stellar equivalence, are transported
  by injective maps of the vertices; so `StellarEquivIn` implies `StellarEquiv` (`of_in`).
* `StellarEquiv.weld`: a weld is a stellar equivalence.
* `starAt_singleton`, `StellarEquiv.map_perm`: subdividing a vertex renames it, and isomorphic
  complexes are stellar equivalent.
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V : Type*} [DecidableEq V]

/-- `insert a` is injective on sets not containing `a`. -/
lemma insert_cancel {a : V} {s t : Finset V} (hs : a ∉ s) (ht : a ∉ t)
    (h : insert a s = insert a t) : s = t := by
  rw [← erase_insert hs, h, erase_insert ht]

/-! ## Stellar subdivision -/

/-- The **stellar subdivision** `(A, a) K` of `K` at `A` with apex `a`: the faces of `K` not
containing `A`, together with the cone from `a` on the faces `s ∌ A` with `A ∪ s ∈ K` (which form
`∂A * lk(A, K)`). -/
def starAt (K : SComplex V) (A : Finset V) (a : V) : SComplex V where
  faces := K.faces.filter (fun s => ¬ A ⊆ s) ∪
    (K.faces.filter fun s => ¬ A ⊆ s ∧ A ∪ s ∈ K.faces).image (insert a)
  down s hs t ht := by
    simp only [mem_union, mem_filter, mem_image, mem_faces] at hs ⊢
    rcases hs with ⟨hs, hA⟩ | ⟨s', ⟨hs', hA, hAs⟩, rfl⟩
    · exact .inl ⟨down_mem hs ht, fun h => hA (h.trans ht)⟩
    · by_cases ha : a ∈ t
      · have hsub : t.erase a ⊆ s' := fun x hx => by
          have := ht (mem_of_mem_erase hx)
          rcases mem_insert.1 this with h | h
          · exact absurd h (ne_of_mem_erase hx)
          · exact h
        exact .inr ⟨t.erase a, ⟨down_mem hs' hsub, fun h => hA (h.trans hsub),
          down_mem hAs (union_subset_union_right hsub)⟩, insert_erase ha⟩
      · have hsub : t ⊆ s' := fun x hx => by
          rcases mem_insert.1 (ht hx) with h | h
          · exact absurd (h ▸ hx) ha
          · exact h
        exact .inl ⟨down_mem hs' hsub, fun h => hA (h.trans hsub)⟩

lemma mem_starAt {K : SComplex V} {A : Finset V} {a : V} {s : Finset V} :
    s ∈ K.starAt A a ↔ (s ∈ K ∧ ¬ A ⊆ s) ∨ ∃ t ∈ K, ¬ A ⊆ t ∧ A ∪ t ∈ K ∧ insert a t = s := by
  change s ∈ K.faces.filter (fun s => ¬ A ⊆ s) ∪
    (K.faces.filter fun s => ¬ A ⊆ s ∧ A ∪ s ∈ K.faces).image (insert a) ↔ _
  simp only [mem_union, mem_filter, mem_image, mem_faces]
  constructor
  · rintro (h | ⟨t, ⟨ht, h⟩, rfl⟩)
    · exact .inl h
    · exact .inr ⟨t, ht, h.1, h.2, rfl⟩
  · rintro (h | ⟨t, ht, h₁, h₂, rfl⟩)
    · exact .inl h
    · exact .inr ⟨t, ⟨ht, h₁, h₂⟩, rfl⟩

/-- A face of the subdivision without the apex `a` is a face of `K` not containing `A`. -/
lemma mem_starAt_of_notMem {K : SComplex V} {A : Finset V} {a : V}
    {s : Finset V} (hs : a ∉ s) : s ∈ K.starAt A a ↔ s ∈ K ∧ ¬ A ⊆ s := by
  rw [mem_starAt]
  refine ⟨fun h => h.elim id ?_, .inl⟩
  rintro ⟨t, -, -, -, rfl⟩
  exact absurd (mem_insert_self a t) hs

/-- The faces of the subdivision through the apex `a` are the cones `insert a s` on the faces of
`∂A * lk(A, K)`. -/
lemma insert_mem_starAt {K : SComplex V} {A : Finset V} {a : V} (ha : a ∉ K.verts)
    {s : Finset V} (hs : a ∉ s) :
    insert a s ∈ K.starAt A a ↔ s ∈ K ∧ ¬ A ⊆ s ∧ A ∪ s ∈ K := by
  rw [mem_starAt]
  constructor
  · rintro (⟨h, -⟩ | ⟨t, ht, h₁, h₂, he⟩)
    · exact absurd (subset_verts h (mem_insert_self a s)) ha
    · rw [← insert_cancel (notMem_of_notMem_verts ha ht) hs he]
      exact ⟨ht, h₁, h₂⟩
  · rintro ⟨h, h₁, h₂⟩
    exact .inr ⟨s, h, h₁, h₂, rfl⟩

/-- The faces `s ∌ A` with `A ∪ s ∈ K` are exactly the faces of `∂A * lk(A, K)`. -/
lemma mem_boundary_join_link {K : SComplex V} {A s : Finset V} :
    s ∈ (boundary A).join (K.link A) ↔ ¬ A ⊆ s ∧ A ∪ s ∈ K := by
  rw [mem_join]
  constructor
  · rintro ⟨t, ht, u, hu, rfl⟩
    rw [mem_boundary] at ht
    rw [mem_link'] at hu
    obtain ⟨x, hxA, hxt⟩ := not_subset.1 ht.not_subset
    refine ⟨fun h => ?_, ?_⟩
    · rcases mem_union.1 (h hxA) with h' | h'
      · exact hxt h'
      · exact disjoint_left.1 hu.1 hxA h'
    · rw [← union_assoc, union_eq_left.2 ht.subset]
      exact hu.2
  · rintro ⟨hA, hAs⟩
    refine ⟨s ∩ A, mem_boundary.2 (Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_right, fun h => ?_⟩),
      s \ A, mem_link'.2 ⟨disjoint_sdiff, by rwa [union_sdiff_self_eq_union]⟩, ?_⟩
    · exact hA (h ▸ inter_subset_left)
    · rw [union_comm, sdiff_union_inter]

/-- The **link of the apex** of a stellar subdivision is `∂A * lk(A, K)`. -/
theorem link_starAt_apex {K : SComplex V} {A : Finset V} {a : V} (ha : a ∉ K.verts) :
    (K.starAt A a).link {a} = (boundary A).join (K.link A) := by
  refine ext_mem fun s => ?_
  rw [mem_link', disjoint_singleton_left, mem_boundary_join_link, ← insert_eq]
  constructor
  · rintro ⟨hs, h⟩
    exact ((insert_mem_starAt ha hs).1 h).2
  · intro h
    have hs : a ∉ s := fun has => ha (subset_verts h.2 (mem_union_right _ has))
    exact ⟨hs, (insert_mem_starAt ha hs).2 ⟨down_mem h.2 subset_union_right, h⟩⟩

/-- The apex is a vertex of the subdivision at a nonempty face. -/
lemma apex_mem_verts {K : SComplex V} {A : Finset V} {a : V} (hA : A ∈ K) (hne : A.Nonempty) :
    a ∈ (K.starAt A a).verts := by
  rw [mem_verts, mem_starAt]
  refine .inr ⟨∅, empty_mem hA, fun h => ?_, by rwa [union_empty], rfl⟩
  exact hne.ne_empty (subset_empty.1 h)

/-- No face of the subdivision contains `A` (when `a ∉ A`). -/
lemma not_subset_of_mem_starAt {K : SComplex V} {A : Finset V} {a : V} (haA : a ∉ A)
    {s : Finset V} (hs : s ∈ K.starAt A a) : ¬ A ⊆ s := by
  rw [mem_starAt] at hs
  rcases hs with ⟨-, h⟩ | ⟨t, -, hA, -, rfl⟩
  · exact h
  · intro h
    refine hA fun x hx => ?_
    rcases mem_insert.1 (h hx) with h' | h'
    · exact absurd (h' ▸ hx) haA
    · exact h'

/-! ## Welds -/

/-- The **weld** of `K` at the vertex `a` along `A`: remove the faces through `a` and add the
sets `A ∪ u` for the faces `u` (without `a`, disjoint from `A`) such that `a ∪ (A ∖ {x}) ∪ u` is a
face for every `x ∈ A`. When the link of `a` is `∂A * L` these `u` are the faces of `L`, and the
weld replaces `a * ∂A * L` by `A * L`. -/
def weld (K : SComplex V) (a : V) (A : Finset V) : SComplex V where
  faces := K.faces.filter (fun s => a ∉ s) ∪
    (K.faces.filter fun u => a ∉ u ∧ a ∉ A ∧ Disjoint A u ∧
      ∀ x ∈ A, insert a (A.erase x ∪ u) ∈ K.faces).image (A ∪ ·)
  down s hs t ht := by
    simp only [mem_union, mem_filter, mem_image, mem_faces] at hs ⊢
    rcases hs with ⟨hs, ha⟩ | ⟨u, ⟨hu, hau, haA, hdis, hx⟩, rfl⟩
    · exact .inl ⟨down_mem hs ht, fun h => ha (ht h)⟩
    · by_cases hAt : A ⊆ t
      · have hsub : t \ A ⊆ u := by
          intro y hy
          rw [mem_sdiff] at hy
          rcases mem_union.1 (ht hy.1) with h | h
          · exact absurd h hy.2
          · exact h
        refine .inr ⟨t \ A, ⟨down_mem hu hsub, fun h => hau (hsub h), haA, disjoint_sdiff,
          fun x hxA => down_mem (hx x hxA) ?_⟩, union_sdiff_of_subset hAt⟩
        exact insert_subset_insert a (union_subset_union_right hsub)
      · obtain ⟨x, hxA, hxt⟩ := not_subset.1 hAt
        have hsub : t ⊆ insert a (A.erase x ∪ u) := by
          intro y hy
          rcases mem_union.1 (ht hy) with h | h
          · exact mem_insert_of_mem (mem_union_left _ (mem_erase.2 ⟨fun e => hxt (e ▸ hy), h⟩))
          · exact mem_insert_of_mem (mem_union_right _ h)
        refine .inl ⟨down_mem (hx x hxA) hsub, fun h => ?_⟩
        rcases mem_union.1 (ht h) with h' | h'
        · exact haA h'
        · exact hau h'

lemma mem_weld {K : SComplex V} {a : V} {A s : Finset V} :
    s ∈ K.weld a A ↔ (s ∈ K ∧ a ∉ s) ∨ ∃ u ∈ K, a ∉ u ∧ a ∉ A ∧ Disjoint A u ∧
      (∀ x ∈ A, insert a (A.erase x ∪ u) ∈ K) ∧ A ∪ u = s := by
  change s ∈ K.faces.filter (fun s => a ∉ s) ∪
    (K.faces.filter fun u => a ∉ u ∧ a ∉ A ∧ Disjoint A u ∧
      ∀ x ∈ A, insert a (A.erase x ∪ u) ∈ K.faces).image (A ∪ ·) ↔ _
  simp only [mem_union, mem_filter, mem_image, mem_faces]
  constructor
  · rintro (h | ⟨u, ⟨hu, h⟩, rfl⟩)
    · exact .inl h
    · exact .inr ⟨u, hu, h.1, h.2.1, h.2.2.1, h.2.2.2, rfl⟩
  · rintro (h | ⟨u, hu, h₁, h₂, h₃, h₄, rfl⟩)
    · exact .inl h
    · exact .inr ⟨u, ⟨hu, h₁, h₂, h₃, h₄⟩, rfl⟩

/-- `a` is not a vertex of a weld at `a`. -/
lemma notMem_verts_weld (K : SComplex V) (a : V) (A : Finset V) : a ∉ (K.weld a A).verts := by
  rw [mem_verts, mem_weld]
  rintro (⟨-, h⟩ | ⟨u, -, hau, haA, -, -, he⟩)
  · exact h (mem_singleton_self a)
  · have : a ∈ A ∪ u := he ▸ mem_singleton_self a
    rcases mem_union.1 this with h | h
    · exact haA h
    · exact hau h

/-- **Welding undoes a stellar subdivision**: `(A, a)⁻¹ (A, a) K = K` for a nonempty face `A` and
a vertex `a` not in `K`. -/
theorem weld_starAt {K : SComplex V} {A : Finset V} {a : V} (hA : A ∈ K) (hne : A.Nonempty)
    (ha : a ∉ K.verts) : (K.starAt A a).weld a A = K := by
  have haA : a ∉ A := notMem_of_notMem_verts ha hA
  refine ext_mem fun s => ?_
  rw [mem_weld]
  constructor
  · rintro (⟨hs, has⟩ | ⟨u, hu, hau, -, hdis, hx, rfl⟩)
    · exact ((mem_starAt_of_notMem has).1 hs).1
    · obtain ⟨x, hx'⟩ := hne
      have hnot : a ∉ A.erase x ∪ u := by
        rw [mem_union, not_or]
        exact ⟨fun h => haA (mem_of_mem_erase h), hau⟩
      have h := ((insert_mem_starAt ha hnot).1 (hx x hx')).2.2
      refine down_mem h (union_subset subset_union_left ?_)
      exact subset_union_right.trans subset_union_right
  · intro hs
    have has : a ∉ s := notMem_of_notMem_verts ha hs
    by_cases hAs : A ⊆ s
    · right
      obtain ⟨y, hy⟩ := hne
      have hu : s \ A ∈ K := down_mem hs sdiff_subset
      refine ⟨s \ A, (mem_starAt_of_notMem (fun h => has (mem_sdiff.1 h).1)).2
        ⟨hu, fun h => (mem_sdiff.1 (h hy)).2 hy⟩, fun h => has (mem_sdiff.1 h).1, haA,
        disjoint_sdiff, fun x hx => ?_, union_sdiff_of_subset hAs⟩
      have hnot : a ∉ A.erase x ∪ s \ A := by
        rw [mem_union, not_or]
        exact ⟨fun h => haA (mem_of_mem_erase h), fun h => has (mem_sdiff.1 h).1⟩
      refine (insert_mem_starAt ha hnot).2 ⟨down_mem hs ?_, fun h => ?_, ?_⟩
      · exact union_subset ((erase_subset x A).trans hAs) sdiff_subset
      · rcases mem_union.1 (h hx) with h' | h'
        · exact (mem_erase.1 h').1 rfl
        · exact (mem_sdiff.1 h').2 hx
      · rwa [← union_assoc, union_eq_left.2 (erase_subset x A), union_sdiff_of_subset hAs]
    · exact .inl ⟨(mem_starAt_of_notMem has).2 ⟨hs, hAs⟩, has⟩

/-- **Subdividing undoes a weld.** Suppose the link of `a` in `K` is `∂A * L`, where `L` has no
vertex in `A`, `a ∉ A`, `A` is nonempty and not a face of `K`. Then `(A, a)` applied to the weld
gives `K` back. -/
theorem starAt_weld {K L : SComplex V} {a : V} {A : Finset V} (haA : a ∉ A) (hne : A.Nonempty)
    (hAK : A ∉ K) (hL : Disjoint A L.verts) (hlk : K.link {a} = (boundary A).join L) :
    (K.weld a A).starAt A a = K := by
  -- faces of `K` through `a` are the cones on `∂A * L`
  have hcone : ∀ v, a ∉ v → (insert a v ∈ K ↔ v ∈ (boundary A).join L) := by
    intro v hv
    rw [← hlk, mem_link', disjoint_singleton_left, ← insert_eq]
    exact ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩
  have hjK : ∀ v ∈ (boundary A).join L, v ∈ K ∧ a ∉ v := by
    intro v hv
    rw [← hlk, mem_link, disjoint_singleton_left] at hv
    exact ⟨hv.1, hv.2.1⟩
  have hLj : ∀ u ∈ L, u ∈ (boundary A).join L := fun u hu =>
    mem_join.2 ⟨∅, mem_boundary.2 (Finset.ssubset_iff_subset_ne.2 ⟨empty_subset _,
      hne.ne_empty.symm⟩), u, hu, empty_union u⟩
  have hdisL : ∀ u ∈ L, Disjoint A u := fun u hu =>
    disjoint_of_subset_right (subset_verts hu) hL
  -- no face of `K` contains `A`
  have hnA : ∀ s ∈ K, ¬ A ⊆ s := fun s hs h => hAK (down_mem hs h)
  -- the decomposition of a face of `∂A * L`
  have hdec : ∀ v, v ∈ (boundary A).join L ↔ ¬ A ⊆ v ∧ v \ A ∈ L ∧ v ∩ A ⊆ A := by
    intro v
    rw [mem_join]
    constructor
    · rintro ⟨t, ht, u, hu, rfl⟩
      rw [mem_boundary] at ht
      have hd := hdisL u hu
      obtain ⟨x, hxA, hxt⟩ := not_subset.1 ht.not_subset
      refine ⟨fun h => ?_, ?_, inter_subset_right⟩
      · rcases mem_union.1 (h hxA) with h' | h'
        · exact hxt h'
        · exact disjoint_left.1 hd hxA h'
      · rw [union_sdiff_distrib, sdiff_eq_empty_iff_subset.2 ht.subset, empty_union,
          sdiff_eq_self_of_disjoint hd.symm]
        exact hu
    · rintro ⟨hA, hu, -⟩
      refine ⟨v ∩ A, mem_boundary.2 (Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_right,
        fun h => hA (h ▸ inter_subset_left)⟩), v \ A, hu, ?_⟩
      rw [union_comm, sdiff_union_inter]
  -- the condition in the weld picks out the faces of `L`
  have hcond : ∀ u, a ∉ u → Disjoint A u →
      ((∀ x ∈ A, insert a (A.erase x ∪ u) ∈ K) ↔ u ∈ L) := by
    intro u hau hd
    constructor
    · intro h
      obtain ⟨x, hx⟩ := hne
      have hnot : a ∉ A.erase x ∪ u := by
        rw [mem_union, not_or]
        exact ⟨fun h => haA (mem_of_mem_erase h), hau⟩
      have := ((hdec _).1 ((hcone _ hnot).1 (h x hx))).2.1
      rwa [union_sdiff_distrib, sdiff_eq_empty_iff_subset.2 (erase_subset x A), empty_union,
        sdiff_eq_self_of_disjoint hd.symm] at this
    · intro hu x hx
      have hnot : a ∉ A.erase x ∪ u := by
        rw [mem_union, not_or]
        exact ⟨fun h => haA (mem_of_mem_erase h), hau⟩
      refine (hcone _ hnot).2 (mem_join.2 ⟨A.erase x, mem_boundary.2 (erase_ssubset hx), u, hu,
        rfl⟩)
  -- faces of the weld
  have hW : ∀ s, s ∈ K.weld a A ↔ (s ∈ K ∧ a ∉ s) ∨ ∃ u ∈ L, A ∪ u = s := by
    intro s
    rw [mem_weld]
    constructor
    · rintro (h | ⟨u, -, hau, -, hd, hx, rfl⟩)
      · exact .inl h
      · exact .inr ⟨u, (hcond u hau hd).1 hx, rfl⟩
    · rintro (h | ⟨u, hu, rfl⟩)
      · exact .inl h
      · obtain ⟨huK, hau⟩ := hjK u (hLj u hu)
        exact .inr ⟨u, huK, hau, haA, hdisL u hu, (hcond u hau (hdisL u hu)).2 hu, rfl⟩
  refine ext_mem fun s => ?_
  rw [mem_starAt]
  constructor
  · rintro (⟨hs, hsA⟩ | ⟨t, ht, htA, hAt, rfl⟩)
    · rcases (hW s).1 hs with ⟨h, -⟩ | ⟨u, -, rfl⟩
      · exact h
      · exact absurd subset_union_left hsA
    · rcases (hW t).1 ht with ⟨htK, hat⟩ | ⟨u, -, rfl⟩
      · rcases (hW _).1 hAt with ⟨h, -⟩ | ⟨u, hu, hu'⟩
        · exact absurd subset_union_left (hnA _ h)
        · refine (hcone t hat).2 ((hdec t).2 ⟨htA, ?_, inter_subset_right⟩)
          have : t \ A = u := by
            rw [← union_sdiff_left, ← hu', union_sdiff_left,
              sdiff_eq_self_of_disjoint (hdisL u hu).symm]
          rw [this]; exact hu
      · exact absurd subset_union_left htA
  · intro hs
    by_cases has : a ∈ s
    · right
      have hv : a ∉ s.erase a := notMem_erase a s
      have hj := (hcone _ hv).1 (by rwa [insert_erase has])
      obtain ⟨hA, hu, -⟩ := (hdec _).1 hj
      refine ⟨s.erase a, (hW _).2 (.inl (hjK _ hj)), hA, (hW _).2 (.inr ⟨_, hu, ?_⟩),
        insert_erase has⟩
      rw [union_sdiff_self_eq_union]
    · exact .inl ⟨(hW s).2 (.inl ⟨hs, has⟩), hnA s hs⟩

/-! ## Injective maps of the vertices -/

/-- **Stellar subdivision commutes with injective maps of the vertices.** -/
theorem map_starAt {W : Type*} [DecidableEq W] (K : SComplex V) (A : Finset V) (a : V)
    (f : V ↪ W) : (K.starAt A a).map f = (K.map f).starAt (A.map f) (f a) := by
  refine (eq_map_of ?_ ?_).symm
  · intro s hs
    rcases mem_starAt.1 hs with ⟨hs, -⟩ | ⟨t, ht, -, -, rfl⟩
    · exact exists_eq_map_of_mem_map hs
    · obtain ⟨u, rfl⟩ := exists_eq_map_of_mem_map ht
      exact ⟨insert a u, Finset.map_insert f a u⟩
  · intro t
    rw [mem_starAt, mem_starAt, map_mem_map, Finset.map_subset_map]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨u, hu, h₁, h₂, he⟩
      obtain ⟨u', rfl⟩ := exists_eq_map_of_mem_map hu
      rw [map_mem_map] at hu
      rw [Finset.map_subset_map] at h₁
      rw [← Finset.map_union, map_mem_map] at h₂
      rw [← Finset.map_insert, Finset.map_inj] at he
      exact ⟨u', hu, h₁, h₂, he⟩
    · rintro ⟨u, hu, h₁, h₂, rfl⟩
      exact ⟨u.map f, map_mem_map.2 hu, by rwa [Finset.map_subset_map],
        by rwa [← Finset.map_union, map_mem_map], (Finset.map_insert f a u).symm⟩

/-! ## Stellar equivalence -/

/-- An elementary **stellar step** inside the vertex type `V`: a stellar subdivision at a nonempty
face with a vertex of `V` not in the complex. -/
inductive StellarStep : SComplex V → SComplex V → Prop
  /-- Stellar subdivision `(A, a)` at a nonempty face `A` with a new vertex `a`. -/
  | starAt {K : SComplex V} {A : Finset V} {a : V} (hA : A ∈ K) (hne : A.Nonempty)
      (ha : a ∉ K.verts) : StellarStep K (K.starAt A a)

/-- `K` and `L` are **stellar equivalent inside `V`**: they are related by a finite sequence of
stellar subdivisions and welds (inverse subdivisions) whose new vertices are taken from `V`. This
depends on how many vertices `V` has to spare; `StellarEquiv` does not. -/
def StellarEquivIn (K L : SComplex V) : Prop := Relation.EqvGen StellarStep K L

/-- `K` and `L` are **stellar equivalent**: they are related by stellar subdivisions and welds,
with an unlimited supply of new vertices. Formally, their lifts to `V ⊕ ℕ` are stellar equivalent
inside `V ⊕ ℕ`. -/
def StellarEquiv (K L : SComplex V) : Prop := StellarEquivIn K.lift L.lift

namespace StellarEquivIn

@[refl] lemma refl (K : SComplex V) : StellarEquivIn K K := Relation.EqvGen.refl K

@[symm] lemma symm {K L : SComplex V} (h : StellarEquivIn K L) : StellarEquivIn L K :=
  Relation.EqvGen.symm _ _ h

@[trans] lemma trans {K L M : SComplex V} (h₁ : StellarEquivIn K L) (h₂ : StellarEquivIn L M) :
    StellarEquivIn K M := Relation.EqvGen.trans _ _ _ h₁ h₂

/-- A stellar subdivision is a stellar equivalence. -/
lemma starAt {K : SComplex V} {A : Finset V} {a : V} (hA : A ∈ K) (hne : A.Nonempty)
    (ha : a ∉ K.verts) : StellarEquivIn K (K.starAt A a) :=
  Relation.EqvGen.rel _ _ (.starAt hA hne ha)

/-- **Stellar equivalence is transported by injective maps of the vertices.** -/
theorem map {W : Type*} [DecidableEq W] {K L : SComplex V} (h : StellarEquivIn K L)
    (f : V ↪ W) : StellarEquivIn (K.map f) (L.map f) := by
  induction h with
  | rel K L h =>
    obtain ⟨hA, hne, ha⟩ := h
    rw [map_starAt]
    refine Relation.EqvGen.rel _ _ (.starAt (map_mem_map.2 hA) (hne.map) ?_)
    rw [verts_map, Finset.mem_map' f]
    exact ha
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **A weld is a stellar equivalence inside `V`**, under the conditions of `starAt_weld`. -/
theorem weld {K L : SComplex V} {a : V} {A : Finset V} (ha : a ∈ K.verts) (haA : a ∉ A)
    (hne : A.Nonempty) (hAK : A ∉ K) (hL : Disjoint A L.verts)
    (hlk : K.link {a} = (boundary A).join L) : StellarEquivIn K (K.weld a A) := by
  have h := starAt_weld haA hne hAK hL hlk
  have h0K : ∅ ∈ K.link {a} :=
    mem_link'.2 ⟨disjoint_empty_right _, by rwa [union_empty, ← mem_verts]⟩
  -- `A` is a face of the weld: it is `A ∪ ∅` with `∅ ∈ L`
  have h0 : ∅ ∈ L := by
    have := h0K
    rw [hlk, mem_join] at this
    obtain ⟨_, -, u, hu, he⟩ := this
    rw [union_eq_empty] at he
    exact he.2 ▸ hu
  have hAW : A ∈ K.weld a A := by
    rw [mem_weld]
    refine .inr ⟨∅, (mem_link.1 h0K).1, notMem_empty a, haA, disjoint_empty_right _,
      fun x hx => ?_, union_empty A⟩
    rw [union_empty]
    have hj : A.erase x ∈ (boundary A).join L :=
      mem_join.2 ⟨A.erase x, mem_boundary.2 (erase_ssubset hx), ∅, h0, union_empty _⟩
    rw [← hlk, mem_link', disjoint_singleton_left, ← insert_eq] at hj
    exact hj.2
  have := starAt hAW hne (notMem_verts_weld K a A)
  rw [h] at this
  exact this.symm

end StellarEquivIn

namespace StellarEquiv

@[refl] lemma refl (K : SComplex V) : StellarEquiv K K := StellarEquivIn.refl _

@[symm] lemma symm {K L : SComplex V} (h : StellarEquiv K L) : StellarEquiv L K :=
  StellarEquivIn.symm h

@[trans] lemma trans {K L M : SComplex V} (h₁ : StellarEquiv K L) (h₂ : StellarEquiv L M) :
    StellarEquiv K M := StellarEquivIn.trans h₁ h₂

/-- Stellar equivalence inside `V` implies stellar equivalence. -/
lemma of_in {K L : SComplex V} (h : StellarEquivIn K L) : StellarEquiv K L := h.map _

/-- A stellar subdivision is a stellar equivalence. -/
lemma starAt {K : SComplex V} {A : Finset V} {a : V} (hA : A ∈ K) (hne : A.Nonempty)
    (ha : a ∉ K.verts) : StellarEquiv K (K.starAt A a) :=
  of_in (StellarEquivIn.starAt hA hne ha)

/-- **A weld is a stellar equivalence**, under the conditions of `starAt_weld`. -/
theorem weld {K L : SComplex V} {a : V} {A : Finset V} (ha : a ∈ K.verts) (haA : a ∉ A)
    (hne : A.Nonempty) (hAK : A ∉ K) (hL : Disjoint A L.verts)
    (hlk : K.link {a} = (boundary A).join L) : StellarEquiv K (K.weld a A) :=
  of_in (StellarEquivIn.weld ha haA hne hAK hL hlk)

end StellarEquiv

/-! ## Renamings -/

/-- Renaming `x` to `y` on a face not containing `y`. -/
lemma map_swap_face {x y : V} {t : Finset V} (hy : y ∉ t) :
    t.map (Equiv.swap x y).toEmbedding = if x ∈ t then insert y (t.erase x) else t := by
  ext z
  rw [Finset.mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_def]
  by_cases hx : x ∈ t
  · have hxy : x ≠ y := fun e => hy (e ▸ hx)
    simp only [hx, ite_true, mem_insert, mem_erase]
    by_cases hzx : z = x
    · subst hzx; simp [hy, hxy]
    · by_cases hzy : z = y
      · subst hzy; simp [hx, hzx]
      · simp [hzx, hzy]
  · simp only [hx, ite_false]
    by_cases hzx : z = x
    · subst hzx; simp [hy, hx]
    · by_cases hzy : z = y
      · subst hzy; simp [hx, hy, hzx]
      · simp [hzx, hzy]

/-- **Subdividing a vertex renames it**: starring `K` at the vertex `x` with a vertex `y` not in
`K` replaces `x` by `y`. -/
theorem starAt_singleton {K : SComplex V} {x y : V} (hy : y ∉ K.verts) :
    K.starAt {x} y = K.map (Equiv.swap x y).toEmbedding := by
  refine ext_mem fun s => ?_
  rw [mem_starAt, mem_map]
  simp only [singleton_subset_iff, ← insert_eq]
  constructor
  · rintro (⟨hs, hx⟩ | ⟨t, ht, hx, hxt, rfl⟩)
    · exact ⟨s, hs, by rw [map_swap_face (notMem_of_notMem_verts hy hs)]; simp [hx]⟩
    · refine ⟨insert x t, hxt, ?_⟩
      rw [map_swap_face (notMem_of_notMem_verts hy hxt)]
      simp [erase_insert hx]
  · rintro ⟨t, ht, rfl⟩
    rw [map_swap_face (notMem_of_notMem_verts hy ht)]
    by_cases hx : x ∈ t
    · rw [ite_eq_left hx]
      exact .inr ⟨t.erase x, down_mem ht (erase_subset x t), notMem_erase x t,
        by rwa [insert_erase hx], rfl⟩
    · rw [ite_eq_right hx]
      exact .inl ⟨ht, hx⟩

/-- Renaming a vertex to a vertex not in `K` is a stellar equivalence inside `V`. -/
lemma StellarEquivIn.map_swap_of_notMem {K : SComplex V} {x y : V} (hy : y ∉ K.verts) :
    StellarEquivIn K (K.map (Equiv.swap x y).toEmbedding) := by
  by_cases hx : {x} ∈ K
  · rw [← starAt_singleton hy]
    exact StellarEquivIn.starAt hx (singleton_nonempty x) hy
  · have : K.map (Equiv.swap x y).toEmbedding = K := by
      rw [map_congr (g := Function.Embedding.refl V), map_refl]
      intro v hv
      have hvx : v ≠ x := fun e => hx (e ▸ mem_verts.1 hv)
      have hvy : v ≠ y := fun e => hy (e ▸ hv)
      simp [Equiv.swap_apply_of_ne_of_ne hvx hvy]
    rw [this]

/-- In an infinite vertex type, exchanging any two vertices is a stellar equivalence: rename `x`
to a new vertex `z`, then `y` to `x`, then `z` to `y`. -/
lemma StellarEquivIn.map_swap [Infinite V] (K : SComplex V) (x y : V) :
    StellarEquivIn K (K.map (Equiv.swap x y).toEmbedding) := by
  by_cases hy : y ∈ K.verts
  · by_cases hx : x ∈ K.verts
    · obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset (K.verts ∪ {x, y})
      simp only [mem_union, mem_insert, mem_singleton, not_or] at hz
      obtain ⟨hzK, hzx, hzy⟩ := hz
      have h₁ := map_swap_of_notMem (x := x) hzK
      have hx₁ : x ∉ (K.map (Equiv.swap x z).toEmbedding).verts := by
        rw [verts_map, Finset.mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_left]
        exact hzK
      have h₂ := map_swap_of_notMem (x := y) hx₁
      have hy₂ : y ∉ ((K.map (Equiv.swap x z).toEmbedding).map
          (Equiv.swap y x).toEmbedding).verts := by
        rw [verts_map, verts_map, Finset.mem_map_equiv, Finset.mem_map_equiv, Equiv.symm_swap,
          Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_left]
        exact hzK
      have h₃ := map_swap_of_notMem (x := z) hy₂
      have he : (((K.map (Equiv.swap x z).toEmbedding).map (Equiv.swap y x).toEmbedding).map
          (Equiv.swap z y).toEmbedding) = K.map (Equiv.swap x y).toEmbedding := by
        rw [map_map, map_map]
        apply map_congr
        intro v hv
        have hvz : v ≠ z := fun e => hzK (e ▸ hv)
        simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.swap_apply_def]
        by_cases hvx : v = x
        · subst hvx; simp [hzx, hzy]
        · by_cases hvy : v = y
          · subst hvy
            simp only [hvx, hvz, ite_false, ite_true]
            split_ifs <;> simp_all
          · simp [hvx, hvy, hvz]
      exact h₁.trans (h₂.trans (he ▸ h₃))
    · rw [Equiv.swap_comm]
      exact map_swap_of_notMem hx
  · exact map_swap_of_notMem hy

/-- **Isomorphic complexes are stellar equivalent** inside an infinite vertex type: renaming the
vertices by any permutation is a composite of renamings to new vertices. -/
theorem StellarEquivIn.map_perm [Infinite V] (K : SComplex V) (e : Equiv.Perm V) :
    StellarEquivIn K (K.map e.toEmbedding) := by
  suffices H : ∀ n, ∀ e : Equiv.Perm V, #(K.verts.filter fun v => e v ≠ v) = n →
      StellarEquivIn K (K.map e.toEmbedding) from H _ e rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro e hn
    by_cases h : ∃ x ∈ K.verts, e x ≠ x
    · obtain ⟨x, hx, hex⟩ := h
      let e' : Equiv.Perm V := e.trans (Equiv.swap (e x) x)
      have he'x : e' x = x := by simp [e']
      have hlt : #(K.verts.filter fun v => e' v ≠ v) < n := by
        rw [← hn]
        refine card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨fun v hv => ?_, fun heq => ?_⟩)
        · rw [mem_filter] at hv ⊢
          refine ⟨hv.1, fun hev => hv.2 ?_⟩
          have hvx : v ≠ x := fun h' => hex (h' ▸ hev)
          have hvex : v ≠ e x := fun h' => hex (e.injective (by rw [← h', hev, h']))
          simp only [e', Equiv.trans_apply, hev]
          exact Equiv.swap_apply_of_ne_of_ne hvex hvx
        · have : x ∈ K.verts.filter fun v => e v ≠ v := mem_filter.2 ⟨hx, hex⟩
          rw [← heq, mem_filter] at this
          exact this.2 he'x
      have h₁ := ih _ hlt e' rfl
      have h₂ := StellarEquivIn.map_swap (K.map e'.toEmbedding) (e x) x
      have he : (K.map e'.toEmbedding).map (Equiv.swap (e x) x).toEmbedding =
          K.map e.toEmbedding := by
        rw [map_map]
        congr 1
        ext v
        simp [e', Equiv.swap_apply_self]
      exact h₁.trans (he ▸ h₂)
    · have : K.map e.toEmbedding = K := by
        rw [map_congr (g := Function.Embedding.refl V), map_refl]
        intro v hv
        by_contra hne
        exact h ⟨v, hv, hne⟩
      rw [this]

/-- **Isomorphic complexes are stellar equivalent.** -/
theorem StellarEquiv.map_perm (K : SComplex V) (e : Equiv.Perm V) :
    StellarEquiv K (K.map e.toEmbedding) := by
  have h : (K.map e.toEmbedding).lift = K.lift.map (Equiv.sumCongr e (Equiv.refl ℕ)).toEmbedding := by
    simp only [lift, map_map]
    congr 1
  change StellarEquivIn K.lift (K.map e.toEmbedding).lift
  rw [h]
  exact StellarEquivIn.map_perm _ _

/-- **A map injective on a finite set agrees there with a permutation**: compose with
transpositions one point at a time. -/
theorem exists_perm_eqOn {s : Finset V} {f : V → V} (hf : Set.InjOn f s) :
    ∃ e : Equiv.Perm V, ∀ x ∈ s, e x = f x := by
  induction s using Finset.induction_on with
  | empty => exact ⟨Equiv.refl V, by simp⟩
  | insert x s hx ih =>
    obtain ⟨e, he⟩ := ih (hf.mono (Finset.coe_subset.2 (Finset.subset_insert x s)))
    refine ⟨e.trans (Equiv.swap (e x) (f x)), fun w hw => ?_⟩
    rw [Equiv.trans_apply]
    rcases mem_insert.1 hw with rfl | hw
    · exact Equiv.swap_apply_left _ _
    · rw [he w hw]
      refine Equiv.swap_apply_of_ne_of_ne (fun h => ?_) (fun h => ?_)
      · rw [← he w hw] at h
        exact hx (e.injective h ▸ hw)
      · exact hx (hf (by simp [hw]) (by simp) h ▸ hw)

/-- **An isomorphism of complexes on `V` is a renaming by a permutation**: if the faces of `L` are
the images of the faces of `K` under a map injective on the vertices of `K`, then `L = K.map e` for
a permutation `e` of `V`. -/
theorem exists_perm_eq_of_iso {K L : SComplex V} {f : V → V} (hf : Set.InjOn f K.verts)
    (hL : L.faces = K.faces.image (Finset.image f)) :
    ∃ e : Equiv.Perm V, K.map e.toEmbedding = L := by
  obtain ⟨e, he⟩ := exists_perm_eqOn hf
  refine ⟨e, SComplex.ext ?_⟩
  change K.faces.image (Finset.map e.toEmbedding) = L.faces
  rw [hL]
  refine Finset.image_congr fun s hs => ?_
  simp only [Finset.map_eq_image]
  exact Finset.image_congr fun x hx => he x (subset_verts (mem_faces.1 hs) hx)

/-- **Isomorphic complexes are stellar equivalent**, for an isomorphism given by a map injective
on the vertices. -/
theorem StellarEquiv.of_iso {K L : SComplex V} {f : V → V} (hf : Set.InjOn f K.verts)
    (hL : L.faces = K.faces.image (Finset.image f)) : StellarEquiv K L := by
  obtain ⟨e, rfl⟩ := exists_perm_eq_of_iso hf hL
  exact StellarEquiv.map_perm K e

end SComplex

end Lightlike.PL
