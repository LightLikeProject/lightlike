import Lightlike.PL.Stellar
import Mathlib.Data.Fintype.EquivFin

/-!
# Bistellar moves

Let `A` be a face of a complex `K` whose link is the boundary `∂B` of a simplex `B` that is not a
face of `K` (Pachner; Lickorish 1999, §1). The **bistellar move** `κ(A, B)` replaces the closed
star `A * ∂B` of `A` by `∂A * B`. In a closed combinatorial `n`-manifold `#A + #B = n + 2`; in
dimension 3 the moves with `(#A, #B) = (3, 2), (4, 1), (2, 3), (1, 4)` are the 2-3, 1-4, 3-2 and
4-1 Pachner moves (`Lightlike/PL/Complex3.lean`).

## Definitions

* `IsBistellar K A B`: `A`, `B` nonempty and disjoint, `lk(A, K) = ∂B`, and `B ∉ K`. There is no
  dimension condition: on a closed combinatorial `n`-manifold `#A + #B = n + 2` is derived
  (`IsMfdIn.card_add_card_of_isBistellar`, `Lightlike/PL/PachnerMoves.lean`).
* `bistellar K A B h`: the faces of `K` not containing `A`, and the sets `t ∪ B` with `t ⊂ A`.

## Main results

* `isBistellar_bistellar`, `bistellar_bistellar`: `κ(B, A)` is defined on the result and undoes
  `κ(A, B)`.
* `starAt_bistellar`: subdividing `A` before the move and `B` after it gives the same complex;
  hence `bistellar_eq_weld` (`κ(A, B)` is a stellar subdivision followed by a weld) and
  `StellarEquiv.bistellar` (bistellar moves are stellar equivalences, with no condition - the
  easy half of Pachner's theorem).
* `map_bistellar`: bistellar moves commute with injective maps of the vertices.
* `bistellar_closure`: the move on a complex given by its facets, in terms of facets.
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V : Type*} [DecidableEq V]

/-- The join is commutative. -/
lemma join_comm (K L : SComplex V) : K.join L = L.join K := ext_mem fun s => by
  simp only [mem_join]
  constructor <;> rintro ⟨t, ht, u, hu, rfl⟩ <;> exact ⟨u, hu, t, ht, union_comm _ _⟩

/-- Faces of a stellar subdivision, with the cone part written as `∂A * lk(A, K)`. -/
lemma mem_starAt' {K : SComplex V} {A : Finset V} {a : V} {s : Finset V} :
    s ∈ K.starAt A a ↔
      (s ∈ K ∧ ¬ A ⊆ s) ∨ ∃ t ∈ (boundary A).join (K.link A), insert a t = s := by
  rw [mem_starAt]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨t, -, h₁, h₂, rfl⟩
    exact ⟨t, mem_boundary_join_link.2 ⟨h₁, h₂⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨h₁, h₂⟩ := mem_boundary_join_link.1 ht
    exact ⟨t, down_mem h₂ subset_union_right, h₁, h₂, rfl⟩

/-! ## The bistellar move -/

/-- Preconditions of the **bistellar move** `κ(A, B)` on `K`: `A` and `B` are nonempty and
disjoint, the link of `A` is the boundary of the simplex `B`, and `B` is not a face of `K`. -/
structure IsBistellar (K : SComplex V) (A B : Finset V) : Prop where
  /-- The face being removed is nonempty. -/
  nonempty_left : A.Nonempty
  /-- The face being added is nonempty. -/
  nonempty_right : B.Nonempty
  /-- The two faces are disjoint. -/
  disjoint : Disjoint A B
  /-- The link of `A` is `∂B`. -/
  link_eq : K.link A = boundary B
  /-- `B` is not yet a face. -/
  notMem : B ∉ K

namespace IsBistellar

variable {K : SComplex V} {A B : Finset V}

/-- Under the bistellar conditions `A` is a face. -/
lemma mem (h : IsBistellar K A B) : A ∈ K := by
  have : ∅ ∈ K.link A := by
    rw [h.link_eq, mem_boundary]
    exact Finset.ssubset_iff_subset_ne.2 ⟨empty_subset _, h.nonempty_right.ne_empty.symm⟩
  simpa using (mem_link.1 this).2.2

/-- The faces of `K` containing `A` are the sets `A ∪ u` with `u ⊂ B`. -/
lemma subset_iff (h : IsBistellar K A B) {s : Finset V} :
    s ∈ K ∧ A ⊆ s ↔ ∃ u ⊂ B, A ∪ u = s := by
  constructor
  · rintro ⟨hs, hA⟩
    refine ⟨s \ A, ?_, union_sdiff_of_subset hA⟩
    rw [← mem_boundary, ← h.link_eq, mem_link']
    exact ⟨disjoint_sdiff, by rwa [union_sdiff_of_subset hA]⟩
  · rintro ⟨u, hu, rfl⟩
    rw [← mem_boundary, ← h.link_eq, mem_link'] at hu
    exact ⟨hu.2, subset_union_left⟩

/-- No face of `K` contains `B`. -/
lemma not_subset (h : IsBistellar K A B) {s : Finset V} (hs : s ∈ K) : ¬ B ⊆ s :=
  fun hB => h.notMem (down_mem hs hB)

end IsBistellar

/-- The **bistellar move** `κ(A, B)`: remove the faces containing `A` (the star `A * ∂B`) and add
the faces `t ∪ B` with `t ⊂ A` (the star `∂A * B`). -/
def bistellar (K : SComplex V) (A B : Finset V) (h : IsBistellar K A B) : SComplex V where
  faces := K.faces.filter (fun s => ¬ A ⊆ s) ∪ (boundary A).faces.image (· ∪ B)
  down s hs r hr := by
    simp only [mem_union, mem_filter, mem_image, mem_faces, mem_boundary] at hs ⊢
    rcases hs with ⟨hs, hA⟩ | ⟨t, ht, rfl⟩
    · exact .inl ⟨down_mem hs hr, fun h' => hA (h'.trans hr)⟩
    · by_cases hB : B ⊆ r
      · have hsub : r \ B ⊆ t := fun y hy => by
          rw [mem_sdiff] at hy
          rcases mem_union.1 (hr hy.1) with h' | h'
          · exact h'
          · exact absurd h' hy.2
        exact .inr ⟨r \ B, hsub.trans_ssubset ht, sdiff_union_of_subset hB⟩
      · have hrB : r ∩ B ∈ K.link A := by
          rw [h.link_eq, mem_boundary]
          exact Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_right,
            fun e => hB (e ▸ inter_subset_left)⟩
        rw [mem_link] at hrB
        have hsub : r ⊆ A ∪ r ∩ B := by
          intro y hy
          rcases mem_union.1 (hr hy) with h' | h'
          · exact mem_union_left _ (ht.subset h')
          · exact mem_union_right _ (mem_inter.2 ⟨hy, h'⟩)
        obtain ⟨x, hxA, hxt⟩ := not_subset.1 ht.not_subset
        refine .inl ⟨down_mem hrB.2.2 hsub, fun h' => ?_⟩
        rcases mem_union.1 (hr (h' hxA)) with h'' | h''
        · exact hxt h''
        · exact disjoint_left.1 h.disjoint hxA h''

lemma mem_bistellar {K : SComplex V} {A B : Finset V} {h : IsBistellar K A B} {s : Finset V} :
    s ∈ K.bistellar A B h ↔ (s ∈ K ∧ ¬ A ⊆ s) ∨ ∃ t ⊂ A, t ∪ B = s := by
  change s ∈ K.faces.filter (fun s => ¬ A ⊆ s) ∪ (boundary A).faces.image (· ∪ B) ↔ _
  simp only [mem_union, mem_filter, mem_image, mem_faces, mem_boundary]

/-- After the move, no face of the old complex containing `B`: a face of `κ(A, B) K` without `B`
is a face of `K` without `A`. -/
lemma mem_bistellar_of_not_subset {K : SComplex V} {A B : Finset V} {h : IsBistellar K A B}
    {s : Finset V} (hB : ¬ B ⊆ s) : s ∈ K.bistellar A B h ↔ s ∈ K ∧ ¬ A ⊆ s := by
  rw [mem_bistellar]
  refine ⟨fun h' => h'.elim id ?_, .inl⟩
  rintro ⟨t, -, rfl⟩
  exact absurd subset_union_right hB

/-- The link of `B` after the move is `∂A`. -/
theorem link_bistellar {K : SComplex V} {A B : Finset V} (h : IsBistellar K A B) :
    (K.bistellar A B h).link B = boundary A := by
  refine ext_mem fun u => ?_
  rw [mem_link', mem_boundary]
  constructor
  · rintro ⟨hd, hu⟩
    rw [mem_bistellar] at hu
    rcases hu with ⟨hu, -⟩ | ⟨t, ht, he⟩
    · exact absurd subset_union_left (h.not_subset hu)
    · have : u = t := by
        have e1 : (B ∪ u) \ B = u := by
          rw [union_sdiff_left, sdiff_eq_self_of_disjoint hd.symm]
        have e2 : (t ∪ B) \ B = t := by
          rw [union_sdiff_self, sdiff_eq_self_of_disjoint
            (disjoint_of_subset_left ht.subset h.disjoint)]
        rw [← e1, ← he, e2]
      exact this ▸ ht
  · intro hu
    refine ⟨disjoint_of_subset_right hu.subset h.disjoint.symm, mem_bistellar.2 (.inr ⟨u, hu,
      union_comm _ _⟩)⟩

/-- **The inverse move is defined**: after `κ(A, B)`, the move `κ(B, A)` is possible. -/
theorem isBistellar_bistellar {K : SComplex V} {A B : Finset V} (h : IsBistellar K A B) :
    IsBistellar (K.bistellar A B h) B A where
  nonempty_left := h.nonempty_right
  nonempty_right := h.nonempty_left
  disjoint := h.disjoint.symm
  link_eq := link_bistellar h
  notMem := by
    rw [mem_bistellar]
    rintro (⟨-, h'⟩ | ⟨t, -, he⟩)
    · exact h' subset_rfl
    · obtain ⟨b, hb⟩ := h.nonempty_right
      exact disjoint_left.1 h.disjoint (he ▸ mem_union_right t hb) hb

/-- **`κ(B, A)` undoes `κ(A, B)`.** -/
theorem bistellar_bistellar {K : SComplex V} {A B : Finset V} (h : IsBistellar K A B) :
    (K.bistellar A B h).bistellar B A (isBistellar_bistellar h) = K := by
  refine ext_mem fun s => ?_
  rw [mem_bistellar]
  constructor
  · rintro (⟨hs, hB⟩ | ⟨t, ht, rfl⟩)
    · exact ((mem_bistellar_of_not_subset hB).1 hs).1
    · exact (h.subset_iff.2 ⟨t, ht, union_comm _ _⟩).1
  · intro hs
    by_cases hA : A ⊆ s
    · obtain ⟨u, hu, rfl⟩ := h.subset_iff.1 ⟨hs, hA⟩
      exact .inr ⟨u, hu, union_comm _ _⟩
    · exact .inl ⟨(mem_bistellar_of_not_subset (h.not_subset hs)).2 ⟨hs, hA⟩, h.not_subset hs⟩

/-- **Both sides of a bistellar move have a common stellar subdivision**: subdividing `B` in
`κ(A, B) K` gives the same complex as subdividing `A` in `K`, namely
`(K − A * ∂B) ∪ a * ∂A * ∂B`. -/
theorem starAt_bistellar {K : SComplex V} {A B : Finset V} (h : IsBistellar K A B) (a : V) :
    (K.bistellar A B h).starAt B a = K.starAt A a := by
  refine ext_mem fun s => ?_
  rw [mem_starAt', mem_starAt', link_bistellar h, h.link_eq, join_comm]
  refine or_congr ⟨?_, ?_⟩ Iff.rfl
  · rintro ⟨hs, hB⟩
    exact (mem_bistellar_of_not_subset hB).1 hs
  · rintro ⟨hs, hA⟩
    exact ⟨(mem_bistellar_of_not_subset (h.not_subset hs)).2 ⟨hs, hA⟩, h.not_subset hs⟩

/-- The vertices of `κ(A, B) K` are vertices of `K` or of `B`. -/
lemma verts_bistellar_subset {K : SComplex V} {A B : Finset V} (h : IsBistellar K A B) :
    (K.bistellar A B h).verts ⊆ K.verts ∪ B := by
  intro x hx
  rw [mem_verts, mem_bistellar] at hx
  rcases hx with ⟨hx, -⟩ | ⟨t, ht, he⟩
  · exact mem_union_left _ (mem_verts.2 hx)
  · have : x ∈ t ∪ B := he ▸ mem_singleton_self x
    rcases mem_union.1 this with h' | h'
    · exact mem_union_left _ (subset_verts h.mem (ht.subset h'))
    · exact mem_union_right _ h'

/-- **A bistellar move is a stellar subdivision followed by a weld**:
`κ(A, B) K = (B, a)⁻¹ (A, a) K` for a vertex `a` not in `K` and not in `B`. -/
theorem bistellar_eq_weld {K : SComplex V} {A B : Finset V} (h : IsBistellar K A B) {a : V}
    (ha : a ∉ K.verts) (haB : a ∉ B) : K.bistellar A B h = (K.starAt A a).weld a B := by
  have ha' : a ∉ (K.bistellar A B h).verts := fun hx => by
    rcases mem_union.1 (verts_bistellar_subset h hx) with h' | h'
    · exact ha h'
    · exact haB h'
  rw [← starAt_bistellar h a, weld_starAt (isBistellar_bistellar h).mem h.nonempty_right ha']

/-- **Bistellar moves are stellar equivalences inside `V`**, given a vertex of `V` outside `K` and
`B` to subdivide with. -/
theorem StellarEquivIn.bistellar {K : SComplex V} {A B : Finset V} (h : IsBistellar K A B) {a : V}
    (ha : a ∉ K.verts) (haB : a ∉ B) : StellarEquivIn K (K.bistellar A B h) := by
  have ha' : a ∉ (K.bistellar A B h).verts := fun hx => by
    rcases mem_union.1 (verts_bistellar_subset h hx) with h' | h'
    · exact ha h'
    · exact haB h'
  have h₁ := StellarEquivIn.starAt h.mem h.nonempty_left ha
  have h₂ := StellarEquivIn.starAt (isBistellar_bistellar h).mem h.nonempty_right ha'
  rw [starAt_bistellar h a] at h₂
  exact h₁.trans h₂.symm

/-- Over an infinite vertex type, bistellar moves are stellar equivalences inside the type. -/
theorem StellarEquivIn.bistellar' [Infinite V] {K : SComplex V} {A B : Finset V}
    (h : IsBistellar K A B) : StellarEquivIn K (K.bistellar A B h) := by
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset (K.verts ∪ B)
  rw [mem_union, not_or] at ha
  exact StellarEquivIn.bistellar h ha.1 ha.2

/-- The bistellar conditions are transported by injective maps of the vertices. -/
lemma IsBistellar.map {W : Type*} [DecidableEq W] {K : SComplex V} {A B : Finset V}
    (h : IsBistellar K A B) (f : V ↪ W) : IsBistellar (K.map f) (A.map f) (B.map f) where
  nonempty_left := h.nonempty_left.map
  nonempty_right := h.nonempty_right.map
  disjoint := (Finset.disjoint_map f).2 h.disjoint
  link_eq := by rw [← map_link, h.link_eq, map_boundary]
  notMem := by rw [map_mem_map]; exact h.notMem

/-- **Bistellar moves commute with injective maps of the vertices.** -/
theorem map_bistellar {W : Type*} [DecidableEq W] {K : SComplex V} {A B : Finset V}
    (h : IsBistellar K A B) (f : V ↪ W) :
    (K.bistellar A B h).map f = (K.map f).bistellar (A.map f) (B.map f) (h.map f) := by
  refine (eq_map_of ?_ ?_).symm
  · intro s hs
    rcases mem_bistellar.1 hs with ⟨hs, -⟩ | ⟨t, ht, rfl⟩
    · exact exists_eq_map_of_mem_map hs
    · obtain ⟨u, -, rfl⟩ := Finset.subset_map_iff.1 ht.subset
      exact ⟨u ∪ B, Finset.map_union u B⟩
  · intro t
    rw [mem_bistellar, mem_bistellar, map_mem_map, Finset.map_subset_map]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨u, hu, he⟩
      obtain ⟨u', -, rfl⟩ := Finset.subset_map_iff.1 hu.subset
      rw [← Finset.map_union, Finset.map_inj] at he
      exact ⟨u', Finset.map_ssubset_map.1 hu, he⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.map f, Finset.map_ssubset_map.2 hu, (Finset.map_union u B).symm⟩

/-- **Bistellar moves are stellar equivalences** (the easy half of Pachner's theorem), with no
condition: the new vertex of the intermediate subdivision is taken from the unlimited supply. -/
theorem StellarEquiv.bistellar {K : SComplex V} {A B : Finset V} (h : IsBistellar K A B) :
    StellarEquiv K (K.bistellar A B h) := by
  change StellarEquivIn (K.map _) ((K.bistellar A B h).map _)
  rw [map_bistellar h]
  exact StellarEquivIn.bistellar' (h.map _)

/-! ## Bistellar moves on complexes given by facets -/

/-- **A bistellar move in terms of generating faces.** Let `K` be generated by `T`. Suppose that
`A`, `B` are nonempty and disjoint, the sets `A ∪ (B ∖ {x})` (`x ∈ B`) belong to `T`, every member
of `T` containing `A` lies in one of them, and no member of `T` contains `B`. Then `κ(A, B)` is
defined, and the result is generated by the members of `T` not containing `A` together with the
sets `(A ∖ {y}) ∪ B` for `y ∈ A`. -/
theorem isBistellar_closure {T : Finset (Finset V)} {A B : Finset V} (hA : A.Nonempty)
    (hB : B.Nonempty) (hAB : Disjoint A B) (hmem : ∀ x ∈ B, A ∪ B.erase x ∈ T)
    (hstar : ∀ t ∈ T, A ⊆ t → ∃ x ∈ B, t ⊆ A ∪ B.erase x) (hnew : ∀ t ∈ T, ¬ B ⊆ t) :
    IsBistellar (closure T) A B where
  nonempty_left := hA
  nonempty_right := hB
  disjoint := hAB
  link_eq := by
    refine ext_mem fun u => ?_
    rw [mem_link', mem_closure, mem_boundary]
    constructor
    · rintro ⟨hd, t, ht, hut⟩
      obtain ⟨x, hx, hsub⟩ := hstar t ht (subset_union_left.trans hut)
      have : u ⊆ B.erase x := fun y hy => by
        rcases mem_union.1 (hsub (hut (mem_union_right _ hy))) with h' | h'
        · exact absurd hy (disjoint_left.1 hd h')
        · exact h'
      exact this.trans_ssubset (erase_ssubset hx)
    · intro hu
      obtain ⟨x, hxB, hxu⟩ := not_subset.1 hu.not_subset
      refine ⟨disjoint_of_subset_right hu.subset hAB, _, hmem x hxB,
        union_subset_union_right fun y hy => mem_erase.2 ⟨fun e => hxu (e ▸ hy), hu.subset hy⟩⟩
  notMem := by
    rw [mem_closure]
    rintro ⟨t, ht, hBt⟩
    exact hnew t ht hBt

/-- The result of the move of `isBistellar_closure`, in terms of generating faces. -/
theorem bistellar_closure {T : Finset (Finset V)} {A B : Finset V} (hA : A.Nonempty)
    (hB : B.Nonempty) (hAB : Disjoint A B) (hmem : ∀ x ∈ B, A ∪ B.erase x ∈ T)
    (hstar : ∀ t ∈ T, A ⊆ t → ∃ x ∈ B, t ⊆ A ∪ B.erase x) (hnew : ∀ t ∈ T, ¬ B ⊆ t) :
    (closure T).bistellar A B (isBistellar_closure hA hB hAB hmem hstar hnew) =
      closure (T.filter (fun t => ¬ A ⊆ t) ∪ A.image fun y => A.erase y ∪ B) := by
  refine ext_mem fun s => ?_
  rw [mem_bistellar, mem_closure, mem_closure]
  simp only [mem_union, mem_filter, mem_image]
  constructor
  · rintro (⟨⟨t, ht, hst⟩, hAs⟩ | ⟨t, ht, rfl⟩)
    · by_cases hAt : A ⊆ t
      · obtain ⟨x, -, hsub⟩ := hstar t ht hAt
        obtain ⟨y, hyA, hys⟩ := not_subset.1 hAs
        refine ⟨_, .inr ⟨y, hyA, rfl⟩, fun z hz => ?_⟩
        rcases mem_union.1 (hsub (hst hz)) with h' | h'
        · exact mem_union_left _ (mem_erase.2 ⟨fun e => hys (e ▸ hz), h'⟩)
        · exact mem_union_right _ (mem_of_mem_erase h')
      · exact ⟨t, .inl ⟨ht, hAt⟩, hst⟩
    · obtain ⟨y, hyA, hyt⟩ := not_subset.1 ht.not_subset
      exact ⟨_, .inr ⟨y, hyA, rfl⟩, union_subset_union
        (fun z hz => mem_erase.2 ⟨fun e => hyt (e ▸ hz), ht.subset hz⟩) subset_rfl⟩
  · rintro ⟨t, ⟨ht, hAt⟩ | ⟨y, hyA, rfl⟩, hst⟩
    · exact .inl ⟨⟨t, ht, hst⟩, fun h' => hAt (h'.trans hst)⟩
    · by_cases hBs : B ⊆ s
      · have hsub : s \ B ⊆ A.erase y := fun z hz => by
          rw [mem_sdiff] at hz
          rcases mem_union.1 (hst hz.1) with h' | h'
          · exact h'
          · exact absurd h' hz.2
        exact .inr ⟨s \ B, hsub.trans_ssubset (erase_ssubset hyA), sdiff_union_of_subset hBs⟩
      · obtain ⟨x, hxB, hxs⟩ := not_subset.1 hBs
        have hy : y ∉ s := fun hys => by
          rcases mem_union.1 (hst hys) with h' | h'
          · exact (mem_erase.1 h').1 rfl
          · exact disjoint_left.1 hAB hyA h'
        refine .inl ⟨⟨_, hmem x hxB, fun z hz => ?_⟩, fun h' => hy (h' hyA)⟩
        rcases mem_union.1 (hst hz) with h' | h'
        · exact mem_union_left _ (mem_of_mem_erase h')
        · exact mem_union_right _ (mem_erase.2 ⟨fun e => hxs (e ▸ hz), h'⟩)

end SComplex

end Lightlike.PL
