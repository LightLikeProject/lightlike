import Lightlike.GFT.Dual
import Mathlib.Data.Finset.Sort

/-!
# The link of a simplex of the dual is the dual of a bubble (Gurau's Theorem 1)

For a colored graph `G` and a simplex `σ = (S, B)` of its dual `Δ_G`, the simplices that contain `σ` form the
link of `σ`. Gurau (*Lost in translation: topological singularities in group field theory*, Class. Quantum
Grav. 27 (2010) 235023, arXiv:1006.0714, Section 5, Theorem 1) states that the `p`-bubbles of a colored
graph are the link graphs of the `(n - p)`-simplices of the gluing. Here the bubble `B` of the colors outside
`S`, as a colored graph (`ColoredGraph.restrict`, the lines of the colors outside `S` restricted to `B`), has a
dual `Δ_{G'}`, and `linkIso` is an order isomorphism from the simplices containing `σ` to the simplices of
`Δ_{G'}`, which lowers the rank by the rank of `σ` (`linkIso_rk`). `link_isDual` is the form for every
simplex that does not have all colors, with the colors outside `S` enumerated in increasing order.

* `mem_bubble_restrict`: the bubbles of the restricted graph are the bubbles of `G`.
* `linkTo`, `linkOf`: the two maps, inverse to each other (`linkOf_linkTo`, `linkTo_linkOf`).
* `linkIso`, `linkIso_rk`, `link_isDual`: the isomorphism, the rank, and the statement.

## References

* R. Gurau, *Lost in translation: topological singularities in group field theory*, Class. Quantum
  Grav. 27 (2010) 235023, arXiv:1006.0714, Section 5, Theorem 1.
-/

open Finset

namespace Lightlike.GFT

variable {D E : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

namespace ColoredGraph

variable {G : ColoredGraph D V}

/-- **The bubbles of the restricted graph are the bubbles of `G`**: in the graph `G.restrict e v0` of the
colors `e c` restricted to the bubble of `v0`, `x` lies in the `S''`-bubble of `w` exactly when
`x` lies in the `e '' S''`-bubble of `w` in `G`. -/
theorem mem_bubble_restrict (e : Fin (E + 1) ↪ Fin (D + 1)) (v0 : V) (S'' : Finset (Fin (E + 1)))
    (w x : {w // w ∈ G.bubble (univ.image e) v0}) :
    x ∈ (G.restrict e v0).bubble S'' w ↔ x.1 ∈ G.bubble (S''.image e) w.1 := by
  rw [mem_bubble_iff, mem_bubble_iff]
  constructor
  · intro h
    refine Relation.ReflTransGen.lift Subtype.val (fun a b hab => ?_) _ _ h
    obtain ⟨c, hc, rfl⟩ := hab
    exact ⟨e c, mem_image_of_mem e hc, rfl⟩
  · intro h
    have key : ∀ y, Relation.ReflTransGen (G.Adj (S''.image e)) w.1 y →
        ∃ hy : y ∈ G.bubble (univ.image e) v0,
          Relation.ReflTransGen ((G.restrict e v0).Adj S'') w ⟨y, hy⟩ := by
      intro y hy
      induction hy with
      | refl => exact ⟨w.2, Relation.ReflTransGen.refl⟩
      | tail _ hadj ih =>
        obtain ⟨hb, hr⟩ := ih
        obtain ⟨col, hcol, rfl⟩ := hadj
        obtain ⟨c, hc, rfl⟩ := mem_image.1 hcol
        exact ⟨inv_mem_bubble_of_mem G (mem_image_of_mem e (mem_univ c)) hb,
          hr.tail ⟨c, hc, rfl⟩⟩
    obtain ⟨hy, hr⟩ := key x.1 h
    exact hr

/-- A simplex has the bubble of its colors at each of its vertices. -/
lemma DualSimplex.bub_eq_of_mem (τ : DualSimplex G) {v : V} (hv : v ∈ τ.bub) :
    τ.bub = G.bubble (univ \ τ.colors) v := by
  obtain ⟨w, hw⟩ := τ.bub_eq
  rw [hw] at hv ⊢
  exact (bubble_eq_of_mem G _ hv).symm

section Link

variable (σ : DualSimplex G) (e : Fin (E + 1) ↪ Fin (D + 1)) (v0 : V)
  (hT : univ.image e = univ \ σ.colors) (hv0 : σ.bub = G.bubble (univ.image e) v0)

include hT in
lemma image_compl_filter {C : Finset (Fin (D + 1))} (hC : σ.colors ⊆ C) :
    (univ \ univ.filter (fun i => e i ∈ C)).image e = univ \ C := by
  ext y
  simp only [mem_image, mem_sdiff, mem_univ, mem_filter, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hy
    have hy' : y ∈ univ.image e := by
      rw [hT]
      simpa using fun h => hy (hC h)
    obtain ⟨i, -, rfl⟩ := mem_image.1 hy'
    exact ⟨i, hy, rfl⟩

include hv0 in
lemma mem_bubble_of_ge {τ : DualSimplex G} (h : σ ≤ τ) {x : V} (hx : x ∈ τ.bub) :
    x ∈ G.bubble (univ.image e) v0 := by
  rw [← hv0]
  exact h.2 hx

include hT hv0 in
/-- The simplex of the restricted graph that a simplex above `σ` gives: the colors `e i` it contains and
its bubble. -/
noncomputable def linkTo (τ : Set.Ici σ) : DualSimplex (G.restrict e v0) :=
  ⟨(univ.filter (fun i => e i ∈ τ.1.colors),
    univ.filter (fun w : {w // w ∈ G.bubble (univ.image e) v0} => w.1 ∈ τ.1.bub)), by
    obtain ⟨v, hv⟩ := DualSimplex.exists_mem_bub τ.1
    refine ⟨⟨v, mem_bubble_of_ge σ e v0 hv0 τ.2 hv⟩, ?_⟩
    ext x
    rw [mem_bubble_restrict, image_compl_filter σ e hT τ.2.1]
    simp only [mem_filter, mem_univ, true_and]
    rw [DualSimplex.bub_eq_of_mem τ.1 hv]⟩

include hT in
lemma image_compl_restrict (C : Finset (Fin (E + 1))) :
    (univ \ C).image e = univ \ (σ.colors ∪ C.image e) := by
  ext y
  simp only [mem_image, mem_sdiff, mem_univ, true_and, mem_union, not_or]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨?_, ?_⟩
    · intro h
      have : e i ∈ univ.image e := mem_image_of_mem e (mem_univ i)
      rw [hT] at this
      simp at this
      exact this h
    · rintro ⟨j, hj, hji⟩
      exact hi (e.injective hji ▸ hj)
  · rintro ⟨h1, h2⟩
    have hy : y ∈ univ.image e := by
      rw [hT]; simpa using h1
    obtain ⟨i, -, rfl⟩ := mem_image.1 hy
    exact ⟨i, fun hi => h2 ⟨i, hi, rfl⟩, rfl⟩

include hT hv0 in
/-- The simplex above `σ` that a simplex of the restricted graph gives: the colors of `σ` and the `e i`, and
the bubble of the same vertices. -/
noncomputable def linkOf (ρ : DualSimplex (G.restrict e v0)) : Set.Ici σ :=
  ⟨⟨(σ.colors ∪ ρ.colors.image e, ρ.bub.image Subtype.val), by
    obtain ⟨v', hv'⟩ := ρ.bub_eq
    refine ⟨v'.1, ?_⟩
    rw [← image_compl_restrict σ e hT ρ.colors]
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
      rw [hv', mem_bubble_restrict] at hx
      exact hx
    · intro hy
      have hv'1 : v'.1 ∈ G.bubble (univ.image e) v0 := v'.2
      have hyV : y ∈ G.bubble (univ.image e) v0 := by
        have h1 : y ∈ G.bubble (univ.image e) v'.1 :=
          bubble_mono G (image_subset_image (subset_univ _)) _ hy
        rwa [bubble_eq_of_mem G _ hv'1] at h1
      refine mem_image.2 ⟨⟨y, hyV⟩, ?_, rfl⟩
      rw [hv', mem_bubble_restrict]
      exact hy⟩, by
    refine ⟨subset_union_left, ?_⟩
    intro x hx
    obtain ⟨w, -, rfl⟩ := mem_image.1 hx
    rw [hv0]
    exact w.2⟩

include hT hv0 in
lemma linkOf_linkTo (τ : Set.Ici σ) :
    linkOf σ e v0 hT hv0 (linkTo σ e v0 hT hv0 τ) = τ := by
  apply Subtype.ext
  refine DualSimplex.ext' ?_ ?_
  · show σ.colors ∪ (univ.filter (fun i => e i ∈ τ.1.colors)).image e = τ.1.colors
    ext y
    simp only [mem_union, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro (h | ⟨i, hi, rfl⟩)
      · exact τ.2.1 h
      · exact hi
    · intro hy
      by_cases h : y ∈ σ.colors
      · exact Or.inl h
      · have : y ∈ univ.image e := by rw [hT]; simpa using h
        obtain ⟨i, -, rfl⟩ := mem_image.1 this
        exact Or.inr ⟨i, hy, rfl⟩
  · ext y
    simp only [DualSimplex.bub, linkOf, linkTo, mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Finset.mem_filter.1 hx).2
    · intro hy
      exact ⟨⟨y, mem_bubble_of_ge σ e v0 hv0 τ.2 hy⟩, Finset.mem_filter.2 ⟨mem_univ _, hy⟩, rfl⟩

include hT hv0 in
lemma linkTo_linkOf (ρ : DualSimplex (G.restrict e v0)) :
    linkTo σ e v0 hT hv0 (linkOf σ e v0 hT hv0 ρ) = ρ := by
  refine DualSimplex.ext' ?_ ?_
  · show univ.filter (fun i => e i ∈ σ.colors ∪ ρ.colors.image e) = ρ.colors
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_image]
    constructor
    · rintro (h | ⟨j, hj, hji⟩)
      · have : e i ∈ univ.image e := mem_image_of_mem e (mem_univ i)
        rw [hT] at this
        simp at this
        exact absurd h this
      · exact e.injective hji ▸ hj
    · intro hi
      exact Or.inr ⟨i, hi, rfl⟩
  · ext x
    simp only [DualSimplex.bub, linkOf, linkTo, mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨z, hz, hzx⟩
      have : z = x := Subtype.ext hzx
      exact this ▸ hz
    · intro hx
      exact ⟨x, hx, rfl⟩

include hT hv0 in
/-- **Gurau's Theorem 1: the link of a simplex of `Δ_G` is the dual of a bubble.** For a simplex `σ`
with the colors `S` and the bubble `B ∋ v0`, and an enumeration `e` of the colors outside `S`, the
simplices that contain `σ` are in order-preserving bijection with the simplices of the dual of the colored
graph `G.restrict e v0` of the lines of the colors outside `S`, restricted to `B`. -/
noncomputable def linkIso : Set.Ici σ ≃o DualSimplex (G.restrict e v0) where
  toFun := linkTo σ e v0 hT hv0
  invFun := linkOf σ e v0 hT hv0
  left_inv := linkOf_linkTo σ e v0 hT hv0
  right_inv := linkTo_linkOf σ e v0 hT hv0
  map_rel_iff' := by
    intro a b
    show linkTo σ e v0 hT hv0 a ≤ linkTo σ e v0 hT hv0 b ↔ a.1 ≤ b.1
    rw [DualSimplex.le_def, DualSimplex.le_def]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun y hy => ?_, fun x hx => ?_⟩
      · by_cases hyσ : y ∈ σ.colors
        · exact b.2.1 hyσ
        · have : y ∈ univ.image e := by rw [hT]; simpa using hyσ
          obtain ⟨i, -, rfl⟩ := mem_image.1 this
          have hi : i ∈ (linkTo σ e v0 hT hv0 a).colors :=
            Finset.mem_filter.2 ⟨mem_univ _, hy⟩
          have := Finset.mem_filter.1 (h1 hi)
          exact this.2
      · have hxV := mem_bubble_of_ge σ e v0 hv0 b.2 hx
        have hxb : (⟨x, hxV⟩ : {w // w ∈ G.bubble (univ.image e) v0}) ∈
            (linkTo σ e v0 hT hv0 b).bub := Finset.mem_filter.2 ⟨mem_univ _, hx⟩
        exact (Finset.mem_filter.1 (h2 hxb)).2
    · rintro ⟨h1, h2⟩
      refine ⟨fun i hi => ?_, fun x hx => ?_⟩
      · exact Finset.mem_filter.2 ⟨mem_univ _, h1 (Finset.mem_filter.1 hi).2⟩
      · exact Finset.mem_filter.2 ⟨mem_univ _, h2 (Finset.mem_filter.1 hx).2⟩

include hT hv0 in
/-- The isomorphism lowers the rank by the rank of `σ`: the rank in the link of `σ` of a simplex `τ ⊇ σ`
is the rank of its image in the dual of the restricted graph. -/
theorem linkIso_rk (τ : Set.Ici σ) :
    ((dual G).link σ).rk τ = (dual (G.restrict e v0)).rk (linkIso σ e v0 hT hv0 τ) := by
  have hcol : σ.colors ∪ (univ.filter (fun i => e i ∈ τ.1.colors)).image e = τ.1.colors :=
    congrArg (fun ρ : Set.Ici σ => ρ.1.colors) (linkOf_linkTo σ e v0 hT hv0 τ)
  have hdis : Disjoint σ.colors ((univ.filter (fun i => e i ∈ τ.1.colors)).image e) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨i, -, rfl⟩ := mem_image.1 hy'
    have : e i ∈ univ.image e := mem_image_of_mem e (mem_univ i)
    rw [hT] at this
    simp at this
    exact this hy
  have hc := congrArg card hcol
  rw [card_union_of_disjoint hdis, card_image_of_injective _ e.injective] at hc
  show τ.1.colors.card - σ.colors.card = _
  show _ = (univ.filter (fun i => e i ∈ τ.1.colors)).card
  omega

end Link

/-- **Supporting lemma for Gurau's Theorem 1, for every `p ≥ 1`**: the link of every simplex `σ` of `Δ_G` that
does not have all colors is the dual of a colored graph, the graph of the lines of the colors outside `σ`
restricted to the bubble of `σ`: there is an order-preserving bijection from the simplices containing `σ` to
the simplices of that dual, which lowers the rank by the rank of `σ`. The colors outside `σ` are enumerated in
increasing order. The statement of the source's range `p ≥ 2` is `link_isDual_of_two_le`. -/
theorem link_isDual (σ : DualSimplex G) (hσ : σ.colors ≠ univ) :
    ∃ (E : ℕ) (e : Fin (E + 1) ↪ Fin (D + 1)) (v0 : V),
      ∃ (_ : univ.image e = univ \ σ.colors) (_ : σ.bub = G.bubble (univ.image e) v0),
        ∃ iso : Set.Ici σ ≃o DualSimplex (G.restrict e v0),
          ∀ τ, ((dual G).link σ).rk τ = (dual (G.restrict e v0)).rk (iso τ) := by
  have hne : (univ \ σ.colors).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at h
    exact hσ (eq_univ_of_forall fun x => h (mem_univ x))
  obtain ⟨k, hk⟩ : ∃ k, (univ \ σ.colors).card = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (card_pos.2 hne).ne'
  let e : Fin (k + 1) ↪ Fin (D + 1) := ((univ \ σ.colors).orderEmbOfFin hk).toEmbedding
  have hT : univ.image e = univ \ σ.colors := by
    ext y
    have hr := congrArg (fun S : Set (Fin (D + 1)) => y ∈ S)
      ((univ \ σ.colors).range_orderEmbOfFin hk)
    simp only [Set.mem_range, Finset.mem_coe] at hr
    simp only [mem_image, mem_univ, true_and, e]
    exact hr.to_iff
  obtain ⟨v0, hv0'⟩ := DualSimplex.exists_mem_bub σ
  have hv0 : σ.bub = G.bubble (univ.image e) v0 := by
    rw [hT]; exact DualSimplex.bub_eq_of_mem σ hv0'
  exact ⟨k, e, v0, hT, hv0, linkIso σ e v0 hT hv0, linkIso_rk σ e v0 hT hv0⟩

/-- **Gurau's Theorem 1** (arXiv:1006.0714, Section 5), in the range the source states, `p ≥ 2`: if the
colors outside `σ` number at least two, the link of `σ` is the dual of the colored graph of the lines of those
colors restricted to the bubble of `σ` (an order-preserving bijection that lowers the rank by the rank of `σ`).
**Differences from the source** (the statement of Theorem 1 was read at the cited location; the proof was not
compared): Gurau states that the `p`-bubbles, as colored (stranded) graphs, *are* the link graphs of the
`(n - p)`-simplices, where the link graph is the stranded graph of his Section 3.1; here the link is the poset of
simplices containing `σ`, identified with the dual of the colored graph of the bubble by an order isomorphism, not
an equality of graphs, and the stranded graph is not defined. The maintainers approved this form on 17 November
2026, as a difference of representation; if stranded graphs are defined in the library, their equivalence with
this form becomes a task. -/
theorem link_isDual_of_two_le (σ : DualSimplex G) (h : 2 ≤ (univ \ σ.colors).card) :
    ∃ (E : ℕ) (e : Fin (E + 1) ↪ Fin (D + 1)) (v0 : V),
      ∃ (_ : univ.image e = univ \ σ.colors) (_ : σ.bub = G.bubble (univ.image e) v0),
        ∃ iso : Set.Ici σ ≃o DualSimplex (G.restrict e v0),
          ∀ τ, ((dual G).link σ).rk τ = (dual (G.restrict e v0)).rk (iso τ) := by
  refine link_isDual σ fun hu => ?_
  rw [hu] at h
  simp at h

end ColoredGraph

end Lightlike.GFT
