import Lightlike.FourD.Boundary

/-!
# The 4-dimensional Pachner moves

All Pachner (bistellar) moves in dimension 4 are instances of one operation. Take two disjoint
nonempty vertex sets `σ` and `τ` with `#σ + #τ = 6`, and write `S = σ ∪ τ` (the vertex set of a
5-simplex). If the 4-simplices of `K` containing `σ` are exactly the `#τ` simplices `S \ {v}` for
`v ∈ τ` (the star of `σ` is the join of `σ` with the boundary of `τ`), and `τ` is not yet a face
of `K`, the move replaces them by the `#σ` simplices `S \ {u}` for `u ∈ σ` (the join of the
boundary of `σ` with `τ`). It is the **(#τ)-(#σ) move**:

| `#σ` | `#τ` | move | removed: simplices sharing | added: simplices sharing |
|---|---|---|---|---|
| 5 | 1 | 1-5 | a 4-simplex | a new vertex |
| 4 | 2 | 2-4 | a tetrahedron | a new edge |
| 3 | 3 | 3-3 | a triangle | a new triangle |
| 2 | 4 | 4-2 | an edge | a new tetrahedron |
| 1 | 5 | 5-1 | a vertex | a new 4-simplex |

(Pachner, *European J. Combin.* 12 (1991) 129; Lickorish, *Geom. Topol. Monogr.* 2 (1999) 299.)
The same description with `#σ + #τ = 5` gives the moves on `Lightlike.PR.Complex3`; for example
`σ = ABC, τ = DE` is `Lightlike.PR.move23`.

## Definitions

* `IsMove K σ τ`: the preconditions above.
* `move K h`: the complex after the move.

## Main results

* `card_simps_move`: the move removes `#τ` and adds `#σ` 4-simplices.
* `IsMove.symm`, `move_move`: after the move, the move with `σ` and `τ` exchanged applies and
  undoes it. So each pair of moves (1-5 and 5-1, 2-4 and 4-2, 3-3 with itself) are inverse.
* `filter_allFaces_move`: the faces not containing `σ` before the move are the faces not
  containing `τ` after it. The faces containing `σ` before are `σ ∪ τ'` for `τ' ⊊ τ`
  (`filter_allFaces_eq_image`).
* `euler4_move`: **the Euler characteristic is invariant under all Pachner moves.**
* `bdryTets_move`: the boundary tetrahedra do not change. `isPseudo4_move_iff`,
  `isClosed4_move_iff`: the move preserves pseudo-manifolds and closed pseudo-manifolds, and
  reflects them.
-/

open Finset

namespace Lightlike.FourD

variable {V : Type*} [DecidableEq V]

namespace Complex4

/-- Preconditions of a Pachner move on `K` given by disjoint nonempty vertex sets `σ`, `τ` with
`#σ + #τ = 6`: the 4-simplices containing `σ` are exactly `(σ ∪ τ) \ {v}` for `v ∈ τ`, and no
4-simplex contains `τ`. -/
structure IsMove (K : Complex4 V) (σ τ : Finset V) : Prop where
  disj : Disjoint σ τ
  card : #σ + #τ = 6
  nonempty_left : σ.Nonempty
  nonempty_right : τ.Nonempty
  mem : ∀ v ∈ τ, (σ ∪ τ).erase v ∈ K.simps
  star : ∀ s ∈ K.simps, σ ⊆ s → ∃ v ∈ τ, s = (σ ∪ τ).erase v
  fresh : ∀ s ∈ K.simps, ¬ τ ⊆ s

variable {K : Complex4 V} {σ τ : Finset V}

lemma IsMove.card_union (h : IsMove K σ τ) : #(σ ∪ τ) = 6 := by
  rw [card_union_of_disjoint h.disj, h.card]

/-- **The Pachner move** given by `σ` and `τ`: the 4-simplices `(σ ∪ τ) \ {v}`, `v ∈ τ`, are
replaced by `(σ ∪ τ) \ {u}`, `u ∈ σ`. -/
def move (K : Complex4 V) {σ τ : Finset V} (h : IsMove K σ τ) : Complex4 V where
  simps := K.simps.filter (fun s => ¬ σ ⊆ s) ∪ σ.image fun u => (σ ∪ τ).erase u
  card_eq s hs := by
    rcases mem_union.mp hs with hs | hs
    · exact K.card_eq s (mem_filter.mp hs).1
    · obtain ⟨u, hu, rfl⟩ := mem_image.mp hs
      rw [card_erase_of_mem (mem_union_left τ hu), h.card_union]

lemma mem_move {h : IsMove K σ τ} {s : Finset V} :
    s ∈ (move K h).simps ↔ (s ∈ K.simps ∧ ¬ σ ⊆ s) ∨ ∃ u ∈ σ, s = (σ ∪ τ).erase u := by
  simp only [move, mem_union, mem_filter, mem_image]
  aesop

/-- `(σ ∪ τ) \ {x}` contains a set `X ∌ x` contained in `σ ∪ τ`. -/
lemma subset_erase_of_notMem {X : Finset V} {x : V} (hX : X ⊆ σ ∪ τ) (hx : x ∉ X) :
    X ⊆ (σ ∪ τ).erase x := fun _ hy => mem_erase.mpr ⟨fun h => hx (h ▸ hy), hX hy⟩

/-- For `x ∈ X`, the set `X` is not contained in `S \ {x}`. -/
lemma not_subset_erase {X S : Finset V} {x : V} (hx : x ∈ X) : ¬ X ⊆ S.erase x :=
  fun h => (mem_erase.mp (h hx)).1 rfl

/-- The 4-simplices containing `σ` are the `(σ ∪ τ) \ {v}` for `v ∈ τ`. -/
lemma IsMove.filter_simps (h : IsMove K σ τ) :
    K.simps.filter (σ ⊆ ·) = τ.image fun v => (σ ∪ τ).erase v := by
  ext s
  simp only [mem_filter, mem_image]
  constructor
  · rintro ⟨hs, hσs⟩
    obtain ⟨v, hv, rfl⟩ := h.star s hs hσs
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨h.mem v hv, subset_erase_of_notMem subset_union_left (disjoint_right.mp h.disj hv)⟩

/-- After the move, the 4-simplices not containing `τ` are those of `K` not containing `σ`. -/
lemma IsMove.filter_move (h : IsMove K σ τ) :
    (move K h).simps.filter (¬ τ ⊆ ·) = K.simps.filter (¬ σ ⊆ ·) := by
  ext s
  simp only [mem_filter, mem_move]
  constructor
  · rintro ⟨hs | ⟨u, hu, rfl⟩, hτ⟩
    · exact hs
    · exact absurd (subset_erase_of_notMem subset_union_right (disjoint_left.mp h.disj hu)) hτ
  · rintro ⟨hs, hσ⟩
    exact ⟨Or.inl ⟨hs, hσ⟩, h.fresh s hs⟩

/-- **After a move, the move with `σ` and `τ` exchanged applies.** -/
theorem IsMove.symm (h : IsMove K σ τ) : IsMove (move K h) τ σ where
  disj := h.disj.symm
  card := by rw [add_comm, h.card]
  nonempty_left := h.nonempty_right
  nonempty_right := h.nonempty_left
  mem u hu := by
    rw [union_comm]
    exact mem_move.mpr (Or.inr ⟨u, hu, rfl⟩)
  star s hs hτs := by
    rw [union_comm]
    rcases mem_move.mp hs with ⟨hs, -⟩ | ⟨u, hu, rfl⟩
    · exact absurd hτs (h.fresh s hs)
    · exact ⟨u, hu, rfl⟩
  fresh s hs := by
    rcases mem_move.mp hs with ⟨-, hσ⟩ | ⟨u, hu, rfl⟩
    · exact hσ
    · exact not_subset_erase hu

/-- **The inverse move undoes the move.** -/
theorem move_move (h : IsMove K σ τ) : move (move K h) h.symm = K := by
  ext s
  rw [mem_move, mem_move, union_comm τ σ]
  constructor
  · rintro (⟨(⟨hs, -⟩ | ⟨u, hu, rfl⟩), hτ⟩ | ⟨v, hv, rfl⟩)
    · exact hs
    · exact absurd (subset_erase_of_notMem subset_union_right (disjoint_left.mp h.disj hu)) hτ
    · exact h.mem v hv
  · intro hs
    by_cases hσ : σ ⊆ s
    · obtain ⟨v, hv, rfl⟩ := h.star s hs hσ
      exact Or.inr ⟨v, hv, rfl⟩
    · exact Or.inl ⟨Or.inl ⟨hs, hσ⟩, h.fresh s hs⟩

/-- `S \ {x}` for `x ∈ S` determines `x`. -/
lemma erase_injOn_union : Set.InjOn (fun x => (σ ∪ τ).erase x) ↑(σ ∪ τ) :=
  erase_injOn _

/-- **The move removes `#τ` and adds `#σ` 4-simplices.** -/
theorem card_simps_move (h : IsMove K σ τ) :
    #(move K h).simps + #τ = #K.simps + #σ := by
  have hK := card_filter_add_card_filter_not (s := K.simps) (σ ⊆ ·)
  rw [h.filter_simps, card_image_of_injOn (fun x hx y hy => erase_injOn_union
    (mem_union_right σ hx) (mem_union_right σ hy))] at hK
  have hK' := card_filter_add_card_filter_not (s := (move K h).simps) (τ ⊆ ·)
  rw [h.symm.filter_simps, card_image_of_injOn (fun x hx y hy => erase_injOn_union
    (by rw [union_comm]; exact mem_union_left τ hx) (by rw [union_comm]; exact mem_union_left τ hy)),
    h.filter_move] at hK'
  omega

/-! ## Faces before and after a move -/

/-- **The faces of `K` not containing `σ` are the faces after the move not containing `τ`.** -/
theorem filter_allFaces_move (h : IsMove K σ τ) :
    (move K h).allFaces.filter (¬ τ ⊆ ·) = K.allFaces.filter (¬ σ ⊆ ·) := by
  -- one inclusion for every move; the other one is the same for the inverse move
  have key : ∀ {K : Complex4 V} {σ τ : Finset V} (h : IsMove K σ τ),
      K.allFaces.filter (¬ σ ⊆ ·) ⊆ (move K h).allFaces.filter (¬ τ ⊆ ·) := by
    intro K σ τ h f hf
    obtain ⟨hf, hσf⟩ := mem_filter.mp hf
    obtain ⟨hne, s, hs, hfs⟩ := mem_allFaces.mp hf
    refine mem_filter.mpr ⟨mem_allFaces.mpr ⟨hne, ?_⟩, fun hτf => h.fresh s hs (hτf.trans hfs)⟩
    by_cases hσs : σ ⊆ s
    · obtain ⟨v, -, rfl⟩ := h.star s hs hσs
      obtain ⟨u, hu, huf⟩ := not_subset.mp hσf
      exact ⟨_, mem_move.mpr (Or.inr ⟨u, hu, rfl⟩),
        subset_erase_of_notMem (hfs.trans (erase_subset _ _)) huf⟩
    · exact ⟨s, mem_move.mpr (Or.inl ⟨hs, hσs⟩), hfs⟩
  refine Subset.antisymm ?_ (key h)
  have := key h.symm
  rwa [move_move] at this

/-- The faces of `K` containing `σ` are the sets `σ ∪ τ'` with `τ'` a proper subset of `τ`. -/
theorem IsMove.filter_allFaces_eq_image (h : IsMove K σ τ) :
    K.allFaces.filter (σ ⊆ ·) = (τ.powerset.erase τ).image (σ ∪ ·) := by
  ext f
  simp only [mem_filter, mem_allFaces, mem_image, mem_erase, mem_powerset]
  constructor
  · rintro ⟨⟨-, s, hs, hfs⟩, hσf⟩
    obtain ⟨v, hv, rfl⟩ := h.star s hs (hσf.trans hfs)
    refine ⟨f ∩ τ, ⟨fun he => ?_, inter_subset_right⟩, ?_⟩
    · have : v ∈ f ∩ τ := by rw [he]; exact hv
      exact (mem_erase.mp (hfs (mem_inter.mp this).1)).1 rfl
    · ext x
      simp only [mem_union, mem_inter]
      constructor
      · rintro (hx | ⟨hx, -⟩)
        exacts [hσf hx, hx]
      · intro hx
        rcases mem_union.mp (erase_subset _ _ (hfs hx)) with hxσ | hxτ
        exacts [Or.inl hxσ, Or.inr ⟨hx, hxτ⟩]
  · rintro ⟨τ', ⟨hne, hτ'⟩, rfl⟩
    obtain ⟨v, hvτ, hvτ'⟩ := not_subset.mp fun h' => hne (Subset.antisymm hτ' h')
    refine ⟨⟨h.nonempty_left.mono subset_union_left, _, h.mem v hvτ, ?_⟩, subset_union_left⟩
    refine subset_erase_of_notMem (union_subset_union (subset_refl σ) hτ') ?_
    rw [mem_union, not_or]
    exact ⟨disjoint_right.mp h.disj hvτ, hvτ'⟩

/-- The faces containing `σ` contribute `1` to the alternating sum of the Euler characteristic:
`Σ_{τ' ⊊ τ} (-1)^(#σ + #τ' + 1) = (-1)^(#σ + #τ) = 1`. -/
lemma IsMove.sum_filter_allFaces (h : IsMove K σ τ) :
    ∑ f ∈ K.allFaces.filter (σ ⊆ ·), (-1 : ℤ) ^ (#f + 1) = 1 := by
  rw [h.filter_allFaces_eq_image, sum_image]
  · have hc : ∀ τ' ∈ τ.powerset.erase τ, (-1 : ℤ) ^ (#(σ ∪ τ') + 1) =
        (-1) ^ (#σ + 1) * (-1) ^ #τ' := by
      intro τ' hτ'
      rw [card_union_of_disjoint (h.disj.mono_right (mem_powerset.mp (mem_of_mem_erase hτ'))),
        ← pow_add]
      ring_nf
    rw [sum_congr rfl hc, ← mul_sum]
    have hs := add_sum_erase τ.powerset (fun τ' => (-1 : ℤ) ^ #τ') (mem_powerset_self τ)
    rw [sum_powerset_neg_one_pow_card_of_nonempty h.nonempty_right] at hs
    have hc6 := h.card
    rw [show ∑ x ∈ τ.powerset.erase τ, (-1 : ℤ) ^ #x = -(-1) ^ #τ by linarith, mul_neg,
      ← pow_add, show #σ + 1 + #τ = 7 by omega]
    norm_num
  · intro a ha b hb hab
    have ha' := mem_powerset.mp (mem_of_mem_erase ha)
    have hb' := mem_powerset.mp (mem_of_mem_erase hb)
    have hab : σ ∪ a = σ ∪ b := hab
    ext x
    constructor
    · intro hx
      have : x ∈ σ ∪ b := hab ▸ mem_union_right σ hx
      rcases mem_union.mp this with hxσ | hxb
      · exact absurd (ha' hx) (disjoint_left.mp h.disj hxσ)
      · exact hxb
    · intro hx
      have : x ∈ σ ∪ a := hab ▸ mem_union_right σ hx
      rcases mem_union.mp this with hxσ | hxa
      · exact absurd (hb' hx) (disjoint_left.mp h.disj hxσ)
      · exact hxa

/-- **The Euler characteristic is invariant under every Pachner move.** -/
theorem euler4_move (h : IsMove K σ τ) : (move K h).euler4 = K.euler4 := by
  rw [euler4_eq_sum, euler4_eq_sum,
    ← sum_filter_add_sum_filter_not (move K h).allFaces (τ ⊆ ·),
    ← sum_filter_add_sum_filter_not K.allFaces (σ ⊆ ·), h.sum_filter_allFaces,
    filter_allFaces_move h]
  have := h.symm.sum_filter_allFaces
  rw [this]

/-! ## Stars of tetrahedra, boundary and closedness -/

/-- For `t ⊆ σ ∪ τ`, the `x ∈ X` with `t ⊆ (σ ∪ τ) \ {x}` are the `x ∈ X \ t`. -/
lemma filter_subset_erase {X t : Finset V} (ht : t ⊆ σ ∪ τ) :
    X.filter (fun x => t ⊆ (σ ∪ τ).erase x) = X \ t := by
  ext x
  simp only [mem_filter, mem_sdiff]
  exact ⟨fun ⟨hx, h⟩ => ⟨hx, fun hxt => not_subset_erase hxt h⟩,
    fun ⟨hx, hxt⟩ => ⟨hx, subset_erase_of_notMem ht hxt⟩⟩

/-- The star of `t` splits into the 4-simplices not containing `σ` and those of the form
`(σ ∪ τ) \ {v}`, `v ∈ τ`. -/
lemma IsMove.card_star (h : IsMove K σ τ) (t : Finset V) :
    #(K.star t) = #((K.simps.filter (¬ σ ⊆ ·)).filter (t ⊆ ·)) +
      #(τ.filter fun v => t ⊆ (σ ∪ τ).erase v) := by
  rw [Complex4.star, ← card_filter_add_card_filter_not (s := K.simps.filter (t ⊆ ·)) (σ ⊆ ·),
    add_comm, filter_filter, filter_filter]
  congr 1
  · congr 1
    ext s
    simp only [mem_filter]
    tauto
  · rw [show K.simps.filter (fun s => t ⊆ s ∧ σ ⊆ s) = (K.simps.filter (σ ⊆ ·)).filter (t ⊆ ·) by
      ext s; simp only [mem_filter]; tauto, h.filter_simps, filter_image, card_image_of_injOn]
    intro x hx y hy hxy
    exact erase_injOn_union (mem_union_right σ (mem_filter.mp hx).1)
      (mem_union_right σ (mem_filter.mp hy).1) hxy

/-- A tetrahedron containing neither `σ` nor `τ` has as many 4-simplices around it before as
after the move. -/
lemma IsMove.card_star_move_eq (h : IsMove K σ τ) {t : Finset V} (ht : #t = 4) (hσ : ¬ σ ⊆ t)
    (hτ : ¬ τ ⊆ t) : #((move K h).star t) = #(K.star t) := by
  rw [h.card_star, h.symm.card_star, h.filter_move, union_comm τ σ]
  congr 1
  by_cases htS : t ⊆ σ ∪ τ
  · rw [filter_subset_erase htS, filter_subset_erase htS]
    -- `(σ ∪ τ) \ t` has two elements, at least one in `σ` and one in `τ`
    have h2 : #((σ ∪ τ) \ t) = 2 := by rw [card_sdiff_of_subset htS, h.card_union, ht]
    have hsplit : #(σ \ t) + #(τ \ t) = 2 := by
      rw [← h2, union_sdiff_distrib, card_union_of_disjoint
        (h.disj.mono sdiff_subset sdiff_subset)]
    have h1 : 0 < #(σ \ t) := card_pos.mpr (sdiff_nonempty.mpr hσ)
    have h1' : 0 < #(τ \ t) := card_pos.mpr (sdiff_nonempty.mpr hτ)
    omega
  · have h0 : ∀ X : Finset V, X.filter (fun x => t ⊆ (σ ∪ τ).erase x) = ∅ := fun X =>
      filter_eq_empty_iff.mpr fun x _ hx => htS (hx.trans (erase_subset _ _))
    rw [h0, h0]

/-- A tetrahedron of `K` containing `σ` lies in exactly two 4-simplices of `K`. -/
lemma IsMove.card_star_of_subset (h : IsMove K σ τ) {t : Finset V} (ht : t ∈ K.tets)
    (hσ : σ ⊆ t) : #(K.star t) = 2 := by
  obtain ⟨s, hs, hts, ht4⟩ := mem_faces.mp ht
  obtain ⟨w, -, rfl⟩ := h.star s hs (hσ.trans hts)
  have htS : t ⊆ σ ∪ τ := hts.trans (erase_subset _ _)
  have h0 : (K.simps.filter (¬ σ ⊆ ·)).filter (t ⊆ ·) = ∅ :=
    filter_eq_empty_iff.mpr fun s hs hts' => (mem_filter.mp hs).2 (hσ.trans hts')
  rw [h.card_star, h0, card_empty, zero_add, filter_subset_erase htS]
  have h2 : #((σ ∪ τ) \ t) = 2 := by rw [card_sdiff_of_subset htS, h.card_union, ht4]
  rwa [union_sdiff_distrib, sdiff_eq_empty_iff_subset.mpr hσ, empty_union] at h2

/-- A tetrahedron of `K` containing `σ` is not a face after the move. -/
lemma IsMove.notMem_tets_move (h : IsMove K σ τ) {t : Finset V} (hσ : σ ⊆ t) :
    t ∉ (move K h).tets := by
  intro ht
  obtain ⟨s, hs, hts, -⟩ := mem_faces.mp ht
  exact h.symm.fresh s hs (hσ.trans hts)

/-- A tetrahedron containing neither `σ` nor `τ` is a face before the move exactly when it is
one after the move. -/
lemma IsMove.mem_tets_move_iff (h : IsMove K σ τ) {t : Finset V} (hσ : ¬ σ ⊆ t)
    (hτ : ¬ τ ⊆ t) : t ∈ (move K h).tets ↔ t ∈ K.tets := by
  have hA := filter_allFaces_move h
  have hmem : ∀ {L : Complex4 V}, t ∈ L.tets ↔ t ∈ L.allFaces ∧ #t = 4 := by
    intro L
    rw [allFaces_eq, mem_biUnion]
    constructor
    · intro ht
      exact ⟨⟨3, by simp, ht⟩, card_of_mem_faces ht⟩
    · rintro ⟨⟨k, -, hk⟩, ht⟩
      have := card_of_mem_faces hk
      rw [show k = 3 by omega] at hk
      exact hk
  rw [hmem, hmem]
  have h1 : t ∈ (move K h).allFaces.filter (¬ τ ⊆ ·) ↔ t ∈ K.allFaces.filter (¬ σ ⊆ ·) := by
    rw [hA]
  simp only [mem_filter] at h1
  tauto

/-- **The boundary does not change under a Pachner move.** -/
theorem bdryTets_move (h : IsMove K σ τ) : (move K h).bdryTets = K.bdryTets := by
  -- one inclusion for every move; the other one is the same for the inverse move
  have key : ∀ {K : Complex4 V} {σ τ : Finset V} (h : IsMove K σ τ),
      (move K h).bdryTets ⊆ K.bdryTets := by
    intro K σ τ h t ht
    obtain ⟨ht, h1⟩ := mem_bdryTets.mp ht
    have hτ : ¬ τ ⊆ t := fun hτ => by
      rw [h.symm.card_star_of_subset ht hτ] at h1
      exact absurd h1 (by norm_num)
    have hσ : ¬ σ ⊆ t := fun hσ => h.notMem_tets_move hσ ht
    exact mem_bdryTets.mpr ⟨(h.mem_tets_move_iff hσ hτ).mp ht,
      h.card_star_move_eq (card_of_mem_faces ht) hσ hτ ▸ h1⟩
  refine Subset.antisymm (key h) ?_
  have := key h.symm
  rwa [move_move] at this

/-- One inclusion of `isPseudo4_move_iff` and `isClosed4_move_iff`: if every tetrahedron of `K`
has a star of size satisfying `P`, so does every tetrahedron after the move. -/
lemma IsMove.star_move_of {P : ℕ → Prop} (hP2 : P 2) (h : IsMove K σ τ)
    (hK : ∀ t ∈ K.tets, P #(K.star t)) : ∀ t ∈ (move K h).tets, P #((move K h).star t) := by
  intro t ht
  by_cases hτ : τ ⊆ t
  · rw [h.symm.card_star_of_subset ht hτ]
    exact hP2
  · have hσ : ¬ σ ⊆ t := fun hσ => h.notMem_tets_move hσ ht
    rw [h.card_star_move_eq (card_of_mem_faces ht) hσ hτ]
    exact hK t ((h.mem_tets_move_iff hσ hτ).mp ht)

/-- **Pachner moves preserve pseudo-manifolds** (every tetrahedron in at most two 4-simplices),
in both directions. -/
theorem isPseudo4_move_iff (h : IsMove K σ τ) : (move K h).IsPseudo4 ↔ K.IsPseudo4 := by
  constructor
  · intro hK'
    have := h.symm.star_move_of (P := (· ≤ 2)) le_rfl hK'
    rwa [move_move] at this
  · exact h.star_move_of (P := (· ≤ 2)) le_rfl

/-- **Pachner moves preserve closed pseudo-manifolds** (every tetrahedron in exactly two
4-simplices), in both directions. -/
theorem isClosed4_move_iff (h : IsMove K σ τ) : (move K h).IsClosed4 ↔ K.IsClosed4 := by
  constructor
  · intro hK'
    have := h.symm.star_move_of (P := (· = 2)) rfl hK'
    rwa [move_move] at this
  · exact h.star_move_of (P := (· = 2)) rfl

end Complex4

end Lightlike.FourD
