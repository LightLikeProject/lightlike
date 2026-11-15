import Lightlike.PL.Boundary

/-!
# Balls are starrable

Lickorish's Theorem 3.6 (*Simplicial moves on complexes and manifolds*, 1999, §3): a PL ball is
starrable relative to its boundary.

* `bd_simplex`, `starrable_simplex`: the boundary of a simplex, and a simplex is starrable.
* `starrable_simplex_join`: Lemma 3.5 iterated: `Δ_A * L` is starrable when `L` is.
* `starrable_rename`: starrability of a subdivision does not depend on the name of the new apex.
* `IsMfdIn.starrable_starAt`: a subdivision of a starrable manifold is starrable relative to its
  own boundary.
* `starrable_of_starAt_of_notMem_bd`: conversely, when the subdivided face is not in the
  boundary.
* `IsMfdIn.link_bd_eq`: the link of a boundary face in the boundary is the boundary of its link.
* `starrable_of_starAt_of_link`: starrability across a boundary face, by a chain of three
  tame segments.
* `starrable_ball`: a PL ball is starrable relative to its boundary (Lickorish, Theorem 3.6).
-/

open Finset

namespace Lightlike.PL
namespace SComplex
variable {V : Type*} [DecidableEq V]

/-- Starrability of a subdivision does not depend on the name of the new apex. -/
theorem starrable_rename [Infinite V] {E K : SComplex V} {A : Finset V} {a a' : V}
    (hEK : E.verts ⊆ K.verts) (ha : a ∉ K.verts) (ha' : a' ∉ K.verts)
    (h : Starrable E (K.starAt A a)) (hAK : A ⊆ K.verts) :
    Starrable E (K.starAt A a') := by
  have hσ : ∀ x ∈ K.verts, (Equiv.swap a a').toEmbedding x = x := fun x hx =>
    Equiv.swap_apply_of_ne_of_ne (fun e => ha (e ▸ hx)) (fun e => ha' (e ▸ hx))
  have h1 := h.map_perm (Equiv.swap a a')
  rw [map_starAt, map_eq_self hσ, map_eq_self (K := E) (fun x hx => hσ x (hEK hx))] at h1
  have hA : A.map (Equiv.swap a a').toEmbedding = A := by
    ext x
    rw [Finset.mem_map]
    exact ⟨fun ⟨y, hy, he⟩ => by rwa [← he, hσ y (hAK hy)], fun hx => ⟨x, hx, hσ x (hAK hx)⟩⟩
  rw [hA] at h1
  simpa using h1

/-- Renaming the new apex of a subdivision of a pair `E ⊆ K`: starrability of
`(A, a) K` relative to `(A, a) E` does not depend on the name of the apex. -/
theorem starrable_rename_pair [Infinite V] {E K : SComplex V} {A : Finset V} {a a' : V}
    (hEK : E.verts ⊆ K.verts) (ha : a ∉ K.verts) (ha' : a' ∉ K.verts)
    (h : Starrable (E.starAt A a) (K.starAt A a)) (hAK : A ⊆ K.verts) :
    Starrable (E.starAt A a') (K.starAt A a') := by
  have hσ : ∀ x ∈ K.verts, (Equiv.swap a a').toEmbedding x = x := fun x hx =>
    Equiv.swap_apply_of_ne_of_ne (fun e => ha (e ▸ hx)) (fun e => ha' (e ▸ hx))
  have h1 := h.map_perm (Equiv.swap a a')
  rw [map_starAt, map_starAt, map_eq_self hσ, map_eq_self (K := E) (fun x hx => hσ x (hEK hx))] at h1
  have hA : A.map (Equiv.swap a a').toEmbedding = A := by
    ext x
    rw [Finset.mem_map]
    exact ⟨fun ⟨y, hy, he⟩ => by rwa [← he, hσ y (hAK hy)], fun hx => ⟨x, hx, hσ x (hAK hx)⟩⟩
  rw [hA] at h1
  simpa using h1

/-- A subdivision of a starrable manifold is starrable relative to its own boundary. -/
theorem IsMfdIn.starrable_starAt [Infinite V] {n : ℕ} {K : SComplex V} (hK : IsMfdIn true n K)
    {A : Finset V} {a : V} (hA : A ∈ K) (hne : A.Nonempty) (ha : a ∉ K.verts)
    (h : Starrable K.bd K) : Starrable (K.starAt A a).bd (K.starAt A a) := by
  have haE : a ∉ K.bd.verts := fun h' => ha (mem_verts.2 (bd_subset (mem_verts.1 h')))
  by_cases hb : A ∈ K.bd
  · rw [hK.bd_starAt_of_mem hA hne ha]
    exact h.starAt hA hne ha haE
  · rw [hK.bd_starAt_of_notMem hA hne ha hb]
    have := h.starAt hA hne ha haE
    rwa [starAt_of_notMem hb] at this

/-- Subdividing at a face outside the boundary: starrability of the subdivision gives
starrability of the manifold. -/
theorem starrable_of_starAt_of_notMem_bd [Infinite V] {K : SComplex V}
    {A : Finset V} {a : V} (hA : A ∈ K) (hne : A.Nonempty)
    (ha : a ∉ K.verts) (hAb : A ∉ K.bd) (h : Starrable K.bd (K.starAt A a)) :
    Starrable K.bd K := by
  intro S hS w hwS hwK hwE
  have hEK : K.bd.verts ⊆ K.verts := fun x hx => mem_verts.2 (bd_subset (mem_verts.1 hx))
  obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset (K.verts ∪ S ∪ {w, a})
  simp only [Finset.mem_union, mem_insert, mem_singleton, not_or] at hb
  obtain ⟨⟨hbK, hbS⟩, hbw, hba⟩ := hb
  have h' := starrable_rename hEK ha hbK h (subset_verts hA)
  have hsub : IsSub K.bd S K A b := by
    refine ⟨hA, hne, hAb, hbK, hbS, fun h => hbK (hEK h), fun x hx hAx => hAb ?_⟩
    have hxK : x ∈ K.verts := mem_verts.2 (hAx ▸ hA)
    rw [hAx]
    exact mem_verts.1 (hS x hx hxK)
  refine Relation.ReflTransGen.head (.inl ⟨A, b, hsub, rfl⟩) (h' S ?_ w hwS ?_ hwE)
  · intro x hx hxv
    refine hS x hx ?_
    rcases mem_insert.1 (verts_starAt_subset K A b hxv) with rfl | h
    · exact absurd hx hbS
    · exact h
  · intro hw
    rcases mem_insert.1 (verts_starAt_subset K A b hw) with rfl | h
    · exact hbw rfl
    · exact hwK h

/-! ## The simplex -/

/-- A simplex on a nonempty vertex set is a PL ball. -/
lemma isBallIn_simplex {C : Finset V} (hC : C.Nonempty) : IsBallIn (simplex C) :=
  ⟨#C - 1, C, by have := hC.card_pos; omega, StellarEquivIn.refl _⟩

/-- The simplex on the empty vertex set is not a PL ball. -/
lemma not_isBallIn_simplex_empty [Infinite V] : ¬ IsBallIn (simplex (∅ : Finset V)) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty V)
  exact IsSB.not_isBallIn (m := 0) (A := {x}) (by simp) (by rw [boundary_singleton])

/-- The boundary of a simplex on a nonempty vertex set is the boundary complex. -/
theorem bd_simplex [Infinite V] {B : Finset V} (hB : B.Nonempty) :
    (simplex B).bd = boundary B := by
  have key : ∀ τ ⊆ B, IsBallIn ((simplex B).link τ) ↔ τ ⊂ B := fun τ hτ => by
    rw [link_simplex hτ]
    constructor
    · intro h
      refine Finset.ssubset_iff_subset_ne.2 ⟨hτ, fun e => ?_⟩
      rw [e, sdiff_self] at h
      exact not_isBallIn_simplex_empty h
    · intro h
      exact isBallIn_simplex (sdiff_nonempty.2 h.2)
  refine ext_mem fun σ => ?_
  rw [mem_bd, mem_boundary, mem_simplex]
  constructor
  · rintro ⟨hσ, rfl | ⟨τ, hτ, hστ, hτne, hb⟩⟩
    · exact Finset.empty_ssubset.2 hB
    · rw [mem_simplex] at hτ
      exact hστ.trans_ssubset ((key τ hτ).1 hb)
  · intro h
    refine ⟨h.1, ?_⟩
    rcases σ.eq_empty_or_nonempty with rfl | hne
    · exact .inl rfl
    · exact .inr ⟨σ, mem_simplex.2 h.1, subset_rfl, hne, (key σ h.1).2 h⟩

/-- A simplex is starrable relative to its boundary: subdivide it once at its top face. -/
theorem starrable_simplex [Infinite V] {B : Finset V} (hB : B.Nonempty) :
    Starrable (boundary B) (simplex B) := by
  intro S hS w hwS hwX hwE
  have hsub : IsSub (boundary B) S (simplex B) B w := by
    refine ⟨mem_simplex.2 subset_rfl, hB, by simp, hwX, hwS, hwE,
      fun x hx hBx => ?_⟩
    have hxB : x ∈ (simplex B).verts := by rw [verts_simplex, hBx]; simp
    have h1 := hS x hx hxB
    rw [mem_verts, mem_boundary, ← hBx] at h1
    exact lt_irrefl _ h1
  have e := starAt_simplex_eq_join (A' := (∅ : Finset V)) (B := B) (x := w) (disjoint_empty_left B)
  rw [empty_union, insert_empty_eq] at e
  exact Relation.ReflTransGen.single (.inl ⟨B, w, hsub, e.symm⟩)

/-! ## Deletion and the deleted star -/

/-- The **deletion** of `A` from `K`: the faces that do not contain `A`. -/
def del (K : SComplex V) (A : Finset V) : SComplex V where
  faces := K.faces.filter fun s => ¬ A ⊆ s
  down s hs t ht := by
    simp only [mem_filter, mem_faces] at hs ⊢
    exact ⟨down_mem hs.1 ht, fun h => hs.2 (h.trans ht)⟩

@[simp] lemma mem_del {K : SComplex V} {A s : Finset V} : s ∈ K.del A ↔ s ∈ K ∧ ¬ A ⊆ s := by
  change s ∈ K.faces.filter _ ↔ _
  simp

lemma del_union_star (K : SComplex V) (A : Finset V) :
    K = (K.del A).union (K.star A) := by
  refine ext_mem fun s => ?_
  rw [mem_union_iff, mem_del, mem_star]
  constructor
  · intro hs
    by_cases h : A ⊆ s
    · exact .inr (by rwa [union_eq_right.2 h])
    · exact .inl ⟨hs, h⟩
  · rintro (h | h)
    · exact h.1
    · exact down_mem h subset_union_right

/-- A stellar subdivision is the deletion of `A` together with the cone from the new vertex on the
deleted star. -/
lemma starAt_eq_del_cone (K : SComplex V) (A : Finset V) (c : V) :
    K.starAt A c = (K.del A).union (cone c ((K.star A).del A)) := by
  refine ext_mem fun s => ?_
  simp only [mem_starAt, mem_union_iff, mem_del, mem_cone, mem_star]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨t, ht, hAt, hAt', rfl⟩)
    · exact .inl ⟨h1, h2⟩
    · exact .inr ⟨t, ⟨hAt', hAt⟩, .inr rfl⟩
  · rintro (⟨h1, h2⟩ | ⟨t, ⟨ht, hAt⟩, rfl | rfl⟩)
    · exact .inl ⟨h1, h2⟩
    · exact .inl ⟨down_mem ht subset_union_right, hAt⟩
    · exact .inr ⟨t, down_mem ht subset_union_right, hAt, ht, rfl⟩

/-! ## Joins with a simplex -/

/-- The join distributes over unions. -/
lemma join_union_left (K K' L : SComplex V) :
    (K.union K').join L = (K.join L).union (K'.join L) := ext_mem fun s => by
  simp only [mem_join, mem_union_iff]
  constructor
  · rintro ⟨t, ht | ht, u, hu, h⟩
    · exact .inl ⟨t, ht, u, hu, h⟩
    · exact .inr ⟨t, ht, u, hu, h⟩
  · rintro (⟨t, ht, u, hu, h⟩ | ⟨t, ht, u, hu, h⟩)
    · exact ⟨t, .inl ht, u, hu, h⟩
    · exact ⟨t, .inr ht, u, hu, h⟩

/-- The cone on a join with `L` is the join of the cone with `L`. -/
lemma cone_join (v : V) (K L : SComplex V) : (cone v K).join L = cone v (K.join L) := by
  rw [cone, cone, join_assoc]

/-- A simplex is the cone on a simplex with one vertex fewer. -/
lemma simplex_insert_eq_cone {v : V} {A : Finset V} : simplex (insert v A) = cone v (simplex A) := by
  refine ext_mem fun s => ?_
  rw [mem_simplex, mem_cone]
  constructor
  · intro h
    refine ⟨s.erase v, mem_simplex.2 ?_, ?_⟩
    · intro x hx
      rw [mem_erase] at hx
      rcases mem_insert.1 (h hx.2) with rfl | h'
      · exact absurd rfl hx.1
      · exact h'
    · by_cases hv : v ∈ s
      · exact .inr (insert_erase hv).symm
      · exact .inl (erase_eq_of_notMem hv).symm
  · rintro ⟨t, ht, rfl | rfl⟩
    · exact (mem_simplex.1 ht).trans (subset_insert _ _)
    · exact insert_subset_insert _ (mem_simplex.1 ht)

/-- The boundary of `Δ_{A ∪ v}` is `Δ_A` together with the cone on `∂Δ_A`. -/
lemma boundary_insert_eq {v : V} {A : Finset V} (hv : v ∉ A) :
    boundary (insert v A) = (simplex A).union (cone v (boundary A)) := by
  refine ext_mem fun s => ?_
  rw [mem_boundary, mem_union_iff, mem_simplex, mem_cone]
  constructor
  · intro h
    by_cases hvs : v ∈ s
    · refine .inr ⟨s.erase v, ?_, .inr (insert_erase hvs).symm⟩
      rw [mem_boundary]
      refine Finset.ssubset_iff_subset_ne.2 ⟨fun x hx => ?_, fun e => h.ne ?_⟩
      · rw [mem_erase] at hx
        rcases mem_insert.1 (h.subset hx.2) with rfl | h'
        · exact absurd rfl hx.1
        · exact h'
      · rw [← insert_erase hvs, e]
    · refine .inl fun x hx => ?_
      rcases mem_insert.1 (h.subset hx) with rfl | h'
      · exact absurd hx hvs
      · exact h'
  · rintro (h | ⟨t, ht, rfl | rfl⟩)
    · exact h.trans_ssubset (ssubset_insert hv)
    · exact (mem_boundary.1 ht).trans (ssubset_insert hv)
    · rw [mem_boundary] at ht
      have hvt : v ∉ t := fun h => hv (ht.subset h)
      refine Finset.ssubset_iff_subset_ne.2 ⟨insert_subset_insert v ht.subset, fun e => ht.ne ?_⟩
      calc t = (insert v t).erase v := (erase_insert hvt).symm
        _ = (insert v A).erase v := by rw [e]
        _ = A := erase_insert hv

/-- **A simplex joined to a starrable complex** (iterating Lickorish's Lemma 3.5): if `L` is
starrable relative to `E`, then `Δ_A * L` is starrable relative to `∂Δ_A * L ∪ Δ_A * E`, the
boundary of the join when `E` is the boundary of `L`. -/
theorem starrable_simplex_join [Infinite V] {L E : SComplex V} (hE : E.verts ⊆ L.verts)
    (h : Starrable E L) :
    ∀ A : Finset V, Disjoint A L.verts →
      Starrable (((boundary A).join L).union ((simplex A).join E)) ((simplex A).join L) := by
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro _
    have e : ((boundary (∅ : Finset V)).join L).union ((simplex ∅).join E) = E := by
      refine ext_mem fun s => ?_
      rw [mem_union_iff, simplex_empty_join, mem_join]
      constructor
      · rintro (⟨t, ht, u, hu, rfl⟩ | h)
        · exact absurd (mem_boundary.1 ht) (by simp)
        · exact h
      · exact fun h => .inr h
    rw [e, simplex_empty_join]
    exact h
  | insert v A' hv ih =>
    intro hAL
    have hvL : v ∉ L.verts := fun h' => (disjoint_left.1 hAL) (mem_insert_self v A') h'
    have hA'L : Disjoint A' L.verts := hAL.mono_left (subset_insert v A')
    have hvX : v ∉ ((simplex A').join L).verts := fun h' => by
      rcases mem_union.1 (verts_join_subset _ _ h') with h'' | h''
      · rw [verts_simplex] at h''; exact hv h''
      · exact hvL h''
    have hvE : v ∉ (((boundary A').join L).union ((simplex A').join E)).verts := fun h' => by
      rw [verts_union] at h'
      rcases mem_union.1 h' with h'' | h''
      · rcases mem_union.1 (verts_join_subset _ _ h'') with h3 | h3
        · exact hv (verts_boundary_subset A' h3)
        · exact hvL h3
      · rcases mem_union.1 (verts_join_subset _ _ h'') with h3 | h3
        · rw [verts_simplex] at h3; exact hv h3
        · exact hvL (hE h3)
    have key := (ih hA'L).toCone hvX hvE
    have e1 : (simplex (insert v A')).join L = cone v ((simplex A').join L) := by
      rw [simplex_insert_eq_cone, cone_join]
    have e2 : ((boundary (insert v A')).join L).union ((simplex (insert v A')).join E) =
        ((simplex A').join L).union
          (cone v (((boundary A').join L).union ((simplex A').join E))) := by
      rw [boundary_insert_eq hv, join_union_left, simplex_insert_eq_cone, cone_join, cone_join,
        cone_union]
      refine ext_mem fun s => ?_
      simp only [mem_union_iff, or_assoc]
    rw [e1, e2]
    exact key

/-! ## The link of a boundary face in the boundary -/

/-- The deleted star of `A` is the join of `∂A` with the link of `A`. -/
lemma del_star_eq (K : SComplex V) (A : Finset V) :
    (K.star A).del A = (boundary A).join (K.link A) := by
  refine ext_mem fun s => ?_
  rw [mem_del, mem_star, mem_boundary_join_link]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **The link of a boundary face in the boundary**: for a face `A` of the boundary of a
combinatorial manifold `K` whose link is itself a combinatorial manifold, the link of `A` in
`∂K` is the boundary of the link of `A` in `K`. -/
theorem IsMfdIn.link_bd_eq [Infinite V] {n n' : ℕ} {K : SComplex V} {A : Finset V}
    (hK : IsMfdIn true n K) (hL : IsMfdIn true n' (K.link A)) (hAb : A ∈ K.bd) (hne : A.Nonempty) :
    K.bd.link A = (K.link A).bd := by
  have hA : A ∈ K := bd_subset hAb
  refine ext_mem fun ρ => ?_
  rw [mem_link']
  rcases ρ.eq_empty_or_nonempty with rfl | hρ
  · simp only [disjoint_empty_right, union_empty, true_and]
    exact iff_of_true hAb (mem_bd.2 ⟨mem_link'.2 ⟨disjoint_empty_right A, by simpa using hA⟩,
      .inl rfl⟩)
  · constructor
    · rintro ⟨hd, hAρ⟩
      have hρL : ρ ∈ K.link A := mem_link'.2 ⟨hd, bd_subset hAρ⟩
      rw [hL.mem_bd_iff hρL hρ, link_link K hd]
      exact (hK.mem_bd_iff (bd_subset hAρ) (hne.mono subset_union_left)).1 hAρ
    · intro h
      have hρL : ρ ∈ K.link A := bd_subset h
      obtain ⟨hd, hAρ⟩ := mem_link'.1 hρL
      refine ⟨hd, ?_⟩
      have hb := (hL.mem_bd_iff hρL hρ).1 h
      rw [link_link K hd] at hb
      exact (hK.mem_bd_iff hAρ (hne.mono subset_union_left)).2 hb

/-! ## The hard case of starrability of balls -/

set_option maxHeartbeats 1000000 in
/-- **Starrability across a boundary face** (the core of Lickorish's Theorem 3.6). Let `E ⊆ K`,
`A ∈ E`, with the link of `A` in `E` equal to the boundary of the link of `A` in `K`. If the link
of `A` in `K` is starrable relative to its boundary and `(A, a) K` is starrable relative to
`(A, a) E`, then `K` is starrable relative to `E`. -/
theorem starrable_of_starAt_of_link [Infinite V] {E K : SComplex V} {A : Finset V} {a : V}
    (hEK : ∀ s ∈ E, s ∈ K) (hAE : A ∈ E) (hne : A.Nonempty) (ha : a ∉ K.verts)
    (hlink : E.link A = (K.link A).bd) (hL0 : Starrable (K.link A).bd (K.link A))
    (hh : Starrable (E.starAt A a) (K.starAt A a)) : Starrable E K := by
  intro S hS w hwS hwK hwE
  have hAK : A ∈ K := hEK A hAE
  have hEv : E.verts ⊆ K.verts := fun x hx => mem_verts.2 (hEK _ (mem_verts.1 hx))
  have hAV : A ⊆ K.verts := subset_verts hAK
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (K.verts ∪ S ∪ {w})
  simp only [Finset.mem_union, mem_singleton, not_or] at hc
  obtain ⟨⟨hcK, hcS⟩, hcw⟩ := hc
  have hcE : c ∉ E.verts := fun h => hcK (hEv h)
  have hwA : w ∉ A := fun h => hwK (hAV h)
  -- the pieces
  have hdisj : Disjoint A (K.link A).verts := by
    rw [Finset.disjoint_left]
    intro x hxA hxL
    have := (mem_link'.1 (mem_verts.1 hxL)).1
    exact (Finset.disjoint_singleton_right.1 this) hxA
  have hFj : (simplex A).join (K.link A).bd = E.star A := by rw [star_eq_join, hlink]
  have hQ : Starrable (((boundary A).join (K.link A)).union (E.star A)) (K.star A) := by
    have := starrable_simplex_join (fun x hx => mem_verts.2 (bd_subset (mem_verts.1 hx)))
      hL0 A hdisj
    rwa [hFj, ← star_eq_join] at this
  -- facts about the pieces
  have mF : ∀ s, s ∈ E.star A ↔ A ∪ s ∈ E := fun s => mem_star
  have mM : ∀ s, s ∈ (boundary A).join (K.link A) ↔ ¬ A ⊆ s ∧ A ∪ s ∈ K := fun s =>
    mem_boundary_join_link
  have m1 : ∀ s ∈ E, s ∈ ((boundary A).join (K.link A)).union (E.star A) ∨ s ∈ K.del A := by
    intro s hs
    by_cases hAs : A ⊆ s
    · exact .inl (mem_union_iff.2 (.inr ((mF s).2 (by rwa [union_eq_right.2 hAs]))))
    · exact .inr (mem_del.2 ⟨hEK s hs, hAs⟩)
  have hDQ : ∀ s, s ∈ K.del A → s ∈ K.star A →
      s ∈ ((boundary A).join (K.link A)).union (E.star A) := by
    intro s hD hQ'
    refine mem_union_iff.2 (.inl ((mM s).2 ⟨(mem_del.1 hD).2, mem_star.1 hQ'⟩))
  have hEQQ : ∀ s, s ∈ ((boundary A).join (K.link A)).union (E.star A) → s ∈ K.star A := by
    intro s hs
    rcases mem_union_iff.1 hs with h | h
    · exact mem_star.2 ((mM s).1 h).2
    · exact mem_star.2 (hEK _ ((mF s).1 h))
  -- segment 1: `K = Q ∪ D` to `cone c EQ ∪ D`
  have hS1 : ∀ x ∈ S ∪ (K.del A).verts, x ∈ (K.star A).verts →
      x ∈ (((boundary A).join (K.link A)).union (E.star A)).verts := by
    intro x hx hxQ
    rw [mem_verts] at hxQ ⊢
    rcases mem_union.1 hx with hxS | hxD
    · have hxE : {x} ∈ E := mem_verts.1 (hS x hxS (mem_verts.2 (down_mem (mem_star.1 hxQ) subset_union_right)))
      rcases m1 _ hxE with h | h
      · exact h
      · exact hDQ _ h hxQ
    · exact hDQ _ (mem_verts.1 hxD) hxQ
  have hcD : c ∉ (K.del A).verts := fun h =>
    hcK (mem_verts.2 (mem_del.1 (mem_verts.1 h)).1)
  have hcQ : c ∉ (K.star A).verts := fun h => hcK (verts_star_subset K A h)
  have hcEQ : c ∉ (((boundary A).join (K.link A)).union (E.star A)).verts := fun h =>
    hcQ (mem_verts.2 (hEQQ _ (mem_verts.1 h)))
  have ch1 := hQ (S ∪ (K.del A).verts) hS1 c
    (by simp only [Finset.mem_union, not_or]; exact ⟨hcS, hcD⟩) hcQ hcEQ
  have ch1' := ch1.glue (R := K.del A) (E' := E) (S' := S) subset_union_right
    (fun x hx hxQ => hS1 x (mem_union_right _ hx) hxQ)
    (fun s hsQ hsD => hDQ s hsD hsQ)
    (fun x hx => by
      rcases m1 _ (mem_verts.1 hx) with h | h
      · exact mem_union_left _ (mem_verts.2 h)
      · exact mem_union_right _ (mem_verts.2 h))
    (fun s hs => m1 s hs) subset_union_left
  have eK : (K.star A).union (K.del A) = K := by rw [union_comm, ← del_union_star]
  rw [eK] at ch1'
  -- segment 2: `K1' ∪ cone c F` to `cone w E1' ∪ cone c F`
  have hAEv : A ∈ E := hAE
  have hh' : Starrable (E.starAt A c) (K.starAt A c) :=
    starrable_rename_pair hEv ha hcK hh hAV
  have hvK1 : ∀ x, x ∈ (K.starAt A c).verts ↔ x = c ∨ (x ∈ K.verts ∧ ¬ A ⊆ {x}) :=
    fun x => mem_verts_starAt hAK hne hcK
  have hvE1 : ∀ x, x ∈ (E.starAt A c).verts ↔ x = c ∨ (x ∈ E.verts ∧ ¬ A ⊆ {x}) :=
    fun x => mem_verts_starAt hAE hne hcE
  have hcF : c ∉ (E.star A).verts := fun h =>
    hcE (mem_verts.2 (down_mem ((mF _).1 (mem_verts.1 h)) subset_union_right))
  have hFv : ∀ x ∈ (cone c (E.star A)).verts, x = c ∨ {x} ∈ E := by
    intro x hx
    rcases mem_insert.1 (verts_cone_subset _ _ hx) with h | h
    · exact .inl h
    · exact .inr (down_mem ((mF _).1 (mem_verts.1 h)) subset_union_right)
  have hS2 : ∀ x ∈ S ∪ (cone c (E.star A)).verts, x ∈ (K.starAt A c).verts →
      x ∈ (E.starAt A c).verts := by
    intro x hx hxK1
    rcases (hvK1 x).1 hxK1 with rfl | ⟨hxK, hxA⟩
    · exact (hvE1 x).2 (.inl rfl)
    · refine (hvE1 x).2 (.inr ⟨?_, hxA⟩)
      rcases mem_union.1 hx with hxS | hxF
      · exact hS x hxS hxK
      · rcases hFv x hxF with rfl | h
        · exact absurd hxK hcK
        · exact mem_verts.2 h
  have hwF : w ∉ (cone c (E.star A)).verts := fun h => by
    rcases mem_insert.1 (verts_cone_subset _ _ h) with h' | h'
    · exact hcw h'.symm
    · exact hwK (mem_verts.2 (down_mem (hEK _ ((mF _).1 (mem_verts.1 h'))) subset_union_right))
  have hS2w : w ∉ S ∪ (cone c (E.star A)).verts := by
    simp only [Finset.mem_union, not_or]; exact ⟨hwS, hwF⟩
  have hwK1 : w ∉ (K.starAt A c).verts := notMem_verts_starAt (Ne.symm hcw |> fun h => h) hwK
  have hwE1 : w ∉ (E.starAt A c).verts := notMem_verts_starAt (fun h => hcw h.symm) hwE
  have ch2 := hh' _ hS2 w hS2w hwK1 hwE1
  have hfs : ∀ s ∈ K.starAt A c, s ∈ cone c (E.star A) → s ∈ E.starAt A c := by
    intro s hs hsF
    by_cases hcs : c ∈ s
    · obtain ⟨t, hct, rfl⟩ : ∃ t, c ∉ t ∧ s = insert c t :=
        ⟨s.erase c, notMem_erase c s, (insert_erase hcs).symm⟩
      obtain ⟨-, h2, h3⟩ := (insert_mem_starAt hcK hct).1 hs
      have h4 := (insert_mem_cone hcF hct).1 hsF
      exact (insert_mem_starAt hcE hct).2 ⟨down_mem ((mF _).1 h4) subset_union_right, h2,
        (mF _).1 h4⟩
    · rw [mem_starAt_of_notMem hcs] at hs ⊢
      refine ⟨?_, hs.2⟩
      have := (mem_cone_of_notMem hcF hcs).1 hsF
      exact down_mem ((mF _).1 this) subset_union_right
  have hEf : ∀ s ∈ E, s ∈ E.starAt A c ∨ s ∈ cone c (E.star A) := by
    intro s hs
    by_cases hAs : A ⊆ s
    · exact .inr (mem_cone.2 ⟨s, (mF s).2 (by rwa [union_eq_right.2 hAs]), .inl rfl⟩)
    · have hcs : c ∉ s := fun h => hcK (mem_verts.2 (down_mem (hEK s hs)
        (singleton_subset_iff.2 h)))
      exact .inl ((mem_starAt_of_notMem hcs).2 ⟨hs, hAs⟩)
  have ch2' := ch2.glue (R := cone c (E.star A)) (E' := E) (S' := S) subset_union_right
    (fun x hx hxK1 => hS2 x (mem_union_right _ hx) hxK1) hfs
    (fun x hx => by
      rcases hEf _ (mem_verts.1 hx) with h | h
      · exact mem_union_left _ (mem_verts.2 h)
      · exact mem_union_right _ (mem_verts.2 h))
    hEf subset_union_left
  -- identify the middle complexes
  have e2 : (cone c (((boundary A).join (K.link A)).union (E.star A))).union (K.del A) =
      (K.starAt A c).union (cone c (E.star A)) := by
    rw [starAt_eq_del_cone, del_star_eq, cone_union]
    refine ext_mem fun s => ?_
    simp only [mem_union_iff, or_assoc, or_comm]
  have e3 : (cone w (E.starAt A c)).union (cone c (E.star A)) =
      (cone w E).starAt (insert w A) c :=
    (cone_starAt_insert hwE hcE hcw hwA).symm
  -- segment 3: the weld
  have hsub : IsSub E S (cone w E) (insert w A) c := by
    refine ⟨mem_cone.2 ⟨A, hAE, .inr rfl⟩, insert_nonempty _ _, fun h => hwE
      (mem_verts_of_mem h (mem_insert_self w A)), notMem_verts_cone hcw hcE, hcS, hcE,
      fun x hx hBx => ?_⟩
    have hwx : w = x := by
      have : w ∈ ({x} : Finset V) := hBx ▸ mem_insert_self w A
      exact mem_singleton.1 this
    obtain ⟨y, hy⟩ := hne
    have : y ∈ ({x} : Finset V) := hBx ▸ mem_insert_of_mem hy
    exact hwK (hwx ▸ mem_singleton.1 this ▸ hAV hy)
  have ch3 : TChain E S ((cone w (E.starAt A c)).union (cone c (E.star A))) (cone w E) := by
    rw [e3]
    exact Relation.ReflTransGen.single (.inr ⟨insert w A, c, hsub,
      fun h => hwE (h (mem_insert_self w A)), rfl⟩)
  rw [e2] at ch1'
  exact ch1'.trans (ch2'.trans ch3)


/-- A PL ball is stellar equivalent to a simplex on a nonempty vertex set. -/
lemma exists_simplex_of_ball [Infinite V] {m : ℕ} {K : SComplex V} (h : IsSB true m K)
    (hb : IsBallIn K) : ∃ B : Finset V, B.Nonempty ∧ StellarEquivIn K (simplex B) := by
  rcases h with ⟨A, hA, hKA⟩ | ⟨-, A, hA, hKA⟩
  · exact absurd hb (IsSB.not_isBallIn hA hKA)
  · rcases A.eq_empty_or_nonempty with rfl | hne
    · exact absurd ((isBallIn_iff_of_stellarEquivIn hKA).1 hb) not_isBallIn_simplex_empty
    · exact ⟨A, hne, hKA⟩

/-- A PL ball has at least one model vertex. -/
lemma IsSB.one_le_of_ball [Infinite V] {m : ℕ} {K : SComplex V} (h : IsSB true m K)
    (hb : IsBallIn K) : 1 ≤ m := by
  rcases h with ⟨A, hA, hKA⟩ | ⟨-, A, hA, hKA⟩
  · exact absurd hb (IsSB.not_isBallIn hA hKA)
  · rcases A.eq_empty_or_nonempty with rfl | hne
    · exact absurd ((isBallIn_iff_of_stellarEquivIn hKA).1 hb) not_isBallIn_simplex_empty
    · have := hne.card_pos; omega

/-- The hard case of Lickorish's Theorem 3.6: if the subdivision of a PL ball `K` at a boundary
face `A` is starrable relative to its boundary, so is `K`, given the theorem in lower dimensions. -/
theorem hard_step [Infinite V] (m : ℕ)
    (IH : ∀ m' < m, ∀ L : SComplex V, IsSB true m' L → IsBallIn L → Starrable L.bd L)
    {K : SComplex V} (hK : IsSB true m K) (hb : IsBallIn K) {A : Finset V} {a : V} (hA : A ∈ K)
    (hne : A.Nonempty) (ha : a ∉ K.verts) (hAb : A ∈ K.bd)
    (h : Starrable (K.starAt A a).bd (K.starAt A a)) : Starrable K.bd K := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := hK.one_le_of_ball hb; omega⟩
  have mfd := (isMfdIn_main (V := V) true n).2 K hK
  obtain ⟨m', hm', hSB⟩ := (isMfdIn_main (V := V) true n).1 K mfd A hA hne
  have hball : IsBallIn (K.link A) := (mfd.mem_bd_iff hA hne).1 hAb
  have hlt : m' < n + 1 := by have := hne.card_pos; omega
  have hL0 := IH m' hlt _ hSB hball
  obtain ⟨k, rfl⟩ : ∃ k, m' = k + 1 := ⟨m' - 1, by have := hSB.one_le_of_ball hball; omega⟩
  have hL : IsMfdIn true k (K.link A) := (isMfdIn_main (V := V) true k).2 _ hSB
  refine starrable_of_starAt_of_link (fun s hs => bd_subset hs) hAb hne ha
    (mfd.link_bd_eq hL hAb hne) hL0 ?_
  rwa [mfd.bd_starAt_of_mem hA hne ha] at h

/-- **Lickorish's Theorem 3.6**: a PL ball (a complex stellar equivalent to a simplex that is a
combinatorial manifold) is starrable relative to its boundary. -/
theorem starrable_ball [Infinite V] (m : ℕ) :
    ∀ K : SComplex V, IsSB true m K → IsBallIn K → Starrable K.bd K := by
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  have key : ∀ K L : SComplex V, Relation.EqvGen StellarStep K L → IsSB true m K → IsBallIn K →
      (Starrable K.bd K ↔ Starrable L.bd L) := by
    intro K L hKL
    induction hKL with
    | rel K L hs =>
      intro hK hb
      cases hs with
      | @starAt A a hA hne ha =>
        obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := hK.one_le_of_ball hb; omega⟩
        have mfd := (isMfdIn_main (V := V) true n).2 K hK
        refine ⟨mfd.starrable_starAt hA hne ha, fun h => ?_⟩
        by_cases hAb : A ∈ K.bd
        · exact hard_step (n + 1) IH hK hb hA hne ha hAb h
        · exact starrable_of_starAt_of_notMem_bd hA hne ha hAb
            (by rwa [mfd.bd_starAt_of_notMem hA hne ha hAb] at h)
    | refl K => exact fun _ _ => Iff.rfl
    | symm K L hKL ih =>
      intro hK hb
      have hKL' : StellarEquivIn K L := hKL
      exact (ih (hK.of_stellarEquivIn hKL'.symm)
        ((isBallIn_iff_of_stellarEquivIn hKL'.symm).1 hb)).symm
    | trans K L M h1 h2 ih1 ih2 =>
      intro hK hb
      have h1' : StellarEquivIn K L := h1
      exact (ih1 hK hb).trans (ih2 (hK.of_stellarEquivIn h1')
        ((isBallIn_iff_of_stellarEquivIn h1').1 hb))
  intro K hK hb
  obtain ⟨B, hB, hKB⟩ := exists_simplex_of_ball hK hb
  refine (key K (simplex B) hKB hK hb).2 ?_
  rw [bd_simplex hB]
  exact starrable_simplex hB


end SComplex
end Lightlike.PL
