import Lightlike.GFT.Dual

/-!
# The vertex sets of the simplices of `Δ_G`

The dual `dual G` of a colored graph is a graded poset with *indexed* simplices (`DualSimplex G`), so two
simplices may have the same vertices. Gurau (*Lost in translation: topological singularities in group field
theory*, Class. Quantum Grav. 27 (2010) 235023, arXiv:1006.0714, Section 2 and Theorem 2) states Theorem 2
for a collection of vertex sets. This file gives the bridge between the two readings: each simplex `(S, B)`
has the vertex set `{(i, B_i) | i ∈ S}` (`vertexSet`), and when no two simplices have the same vertex set
(`Injective (vertexSet G)`) the face order of `dual G` is the inclusion of vertex sets
(`le_iff_vertexSet_subset_of_injective`), so the poset of simplices is the poset of the sets of vertices
ordered by inclusion (`vertexSetOrderIso`). The example of two vertices and three lines, where both top
simplices have the same vertex set, is `not_injective_vertexSet_example`.

## Main results

* `vertexSet`, `card_vertexSet`: a simplex of rank `r` has `r` vertices.
* `vertexSet_mono`: a face has a subset of the vertices (always).
* `le_iff_vertexSet_subset_of_injective`, `vertexSetOrderIso`: the converse, when no simplices repeat.
* `injective_vertexSet_example`, `not_injective_vertexSet_example`: both cases occur.
-/

open Finset

namespace Lightlike.GFT

variable {D : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

namespace ColoredGraph

namespace DualSimplex

variable {G : ColoredGraph D V}

/-- The vertex `(i, B_i)` of a simplex `σ` for a color `i ∈ σ.colors`: `B_i` is the bubble of the colors
other than `i` that contains the bubble of `σ`. -/
noncomputable def vertexBubble (σ : DualSimplex G) (c : Fin (D + 1)) : Finset V :=
  G.bubble (univ \ {c}) (Classical.choose σ.exists_mem_bub)

/-- **The vertex set of a simplex**: the pairs `(i, B_i)`, `i ∈ S`. -/
noncomputable def vertexSet (σ : DualSimplex G) : Finset (Fin (D + 1) × Finset V) :=
  σ.colors.image fun c => (c, σ.vertexBubble c)

/-- Membership in the vertex set. -/
lemma mem_vertexSet {σ : DualSimplex G} {c : Fin (D + 1)} {B : Finset V} :
    (c, B) ∈ σ.vertexSet ↔ c ∈ σ.colors ∧ σ.vertexBubble c = B := by
  unfold vertexSet
  simp only [mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨c', hc, rfl, h⟩
    exact ⟨hc, h⟩
  · rintro ⟨hc, h⟩
    exact ⟨c, hc, rfl, h⟩

/-- The bubble of a simplex is the bubble of each of its vertices. -/
lemma bub_eq_of_mem' (σ : DualSimplex G) {v : V} (hv : v ∈ σ.bub) :
    σ.bub = G.bubble (univ \ σ.colors) v := by
  obtain ⟨w, hw⟩ := σ.bub_eq
  rw [hw] at hv ⊢
  exact (bubble_eq_of_mem G _ hv).symm

/-- The bubble `B_i` of a simplex is the bubble of the colors other than `i` of any vertex of the bubble
of the simplex. -/
lemma vertexBubble_eq (σ : DualSimplex G) (c : Fin (D + 1)) (hc : c ∈ σ.colors) {v : V}
    (hv : v ∈ σ.bub) : σ.vertexBubble c = G.bubble (univ \ {c}) v := by
  have hw := Classical.choose_spec σ.exists_mem_bub
  set w := Classical.choose σ.exists_mem_bub
  have hb : σ.bub = G.bubble (univ \ σ.colors) w := bub_eq_of_mem' σ hw
  have hvw : v ∈ G.bubble (univ \ σ.colors) w := hb ▸ hv
  have hsub : univ \ σ.colors ⊆ univ \ {c} := by
    intro x hx
    simp only [mem_sdiff, mem_univ, true_and, mem_singleton] at hx ⊢
    rintro rfl
    exact hx hc
  have hv' : v ∈ G.bubble (univ \ {c}) w := bubble_mono G hsub w hvw
  exact (bubble_eq_of_mem G _ hv').symm

/-- **The number of vertices of a simplex is its rank.** -/
theorem card_vertexSet (σ : DualSimplex G) : σ.vertexSet.card = σ.colors.card := by
  unfold vertexSet
  exact card_image_of_injective _ fun a b h => (Prod.ext_iff.1 h).1

/-- Simplices with the same vertex set have the same colors. -/
lemma colors_eq_of_vertexSet_eq {σ τ : DualSimplex G} (h : σ.vertexSet = τ.vertexSet) :
    σ.colors = τ.colors := by
  ext c
  constructor
  · intro hc
    have : (c, σ.vertexBubble c) ∈ τ.vertexSet := h ▸ mem_vertexSet.2 ⟨hc, rfl⟩
    exact (mem_vertexSet.1 this).1
  · intro hc
    have : (c, τ.vertexBubble c) ∈ σ.vertexSet := h ▸ mem_vertexSet.2 ⟨hc, rfl⟩
    exact (mem_vertexSet.1 this).1

/-- Simplices with the same vertex set have the same bubbles `B_i`. -/
lemma vertexBubble_eq_of_vertexSet_eq {σ τ : DualSimplex G} (h : σ.vertexSet = τ.vertexSet)
    {c : Fin (D + 1)} (hc : c ∈ σ.colors) : σ.vertexBubble c = τ.vertexBubble c := by
  have : (c, σ.vertexBubble c) ∈ τ.vertexSet := h ▸ mem_vertexSet.2 ⟨hc, rfl⟩
  exact (mem_vertexSet.1 this).2.symm

/-- **A face has a subset of the vertices** (no hypothesis). -/
theorem vertexSet_mono {σ τ : DualSimplex G} (h : σ ≤ τ) : σ.vertexSet ⊆ τ.vertexSet := by
  rintro ⟨c, B⟩ hp
  rw [mem_vertexSet] at hp ⊢
  obtain ⟨hc, rfl⟩ := hp
  obtain ⟨v, hv⟩ := τ.exists_mem_bub
  exact ⟨h.1 hc, by
    rw [vertexBubble_eq σ _ hc (h.2 hv), vertexBubble_eq τ _ (h.1 hc) hv]⟩

/-- **The face order is the inclusion of vertex sets when no two simplices have the same vertex set.** -/
theorem le_iff_vertexSet_subset_of_injective
    (hinj : Function.Injective (vertexSet : DualSimplex G → _)) (σ τ : DualSimplex G) :
    σ ≤ τ ↔ σ.vertexSet ⊆ τ.vertexSet := by
  refine ⟨vertexSet_mono, fun h => ?_⟩
  obtain ⟨v, hv⟩ := τ.exists_mem_bub
  have hcol : σ.colors ⊆ τ.colors := fun c hc => by
    have := h (mem_vertexSet.2 ⟨hc, rfl⟩)
    exact (mem_vertexSet.1 this).1
  have hbub : ∀ c ∈ σ.colors, σ.vertexBubble c = τ.vertexBubble c := fun c hc =>
    ((mem_vertexSet.1 (h (mem_vertexSet.2 ⟨hc, rfl⟩))).2).symm
  -- the face of `τ` with the colors of `σ` and the bubble of `v`
  let σ' : DualSimplex G := ⟨(σ.colors, G.bubble (univ \ σ.colors) v), ⟨v, rfl⟩⟩
  have hv' : v ∈ σ'.bub := mem_bubble_self G _ v
  have hσ' : σ'.vertexSet = σ.vertexSet := by
    ext ⟨c, B⟩
    rw [mem_vertexSet, mem_vertexSet]
    constructor
    · rintro ⟨hc, rfl⟩
      refine ⟨hc, ?_⟩
      rw [hbub _ hc, vertexBubble_eq σ' _ hc hv', vertexBubble_eq τ _ (hcol hc) hv]
    · rintro ⟨hc, rfl⟩
      refine ⟨hc, ?_⟩
      rw [hbub _ hc, vertexBubble_eq σ' _ hc hv', vertexBubble_eq τ _ (hcol hc) hv]
  have hσ'σ : σ' = σ := hinj hσ'
  rw [← hσ'σ]
  refine ⟨hcol, ?_⟩
  show τ.bub ⊆ G.bubble (univ \ σ.colors) v
  rw [bub_eq_of_mem' τ hv]
  exact bubble_mono G (sdiff_subset_sdiff subset_rfl hcol) v

end DualSimplex

variable {G : ColoredGraph D V}

/-- **The poset of simplices as a poset of vertex sets** (Gurau 2010, Theorem 2 in the reading of a
collection of vertex sets): when no two simplices of `Δ_G` have the same vertex set, `dual G` is
order-isomorphic to its vertex sets ordered by inclusion. -/
noncomputable def vertexSetOrderIso
    (hinj : Function.Injective (DualSimplex.vertexSet : DualSimplex G → _)) :
    DualSimplex G ≃o Set.range (DualSimplex.vertexSet : DualSimplex G → _) where
  toEquiv := Equiv.ofInjective _ hinj
  map_rel_iff' := by
    intro a b
    exact (DualSimplex.le_iff_vertexSet_subset_of_injective hinj a b).symm

/-! ### Both cases occur -/

/-- The colored graph of dimension `D` with two vertices joined by all `D + 1` lines. -/
def twoVertexGraph (D : ℕ) : ColoredGraph D Bool where
  inv _ v := !v
  sign v := v
  inv_inv _ v := by simp
  sign_inv _ v := by cases v <;> decide

/-- In the two-vertex graph with a line of some color in `S`, the `S`-bubble of every vertex is everything. -/
lemma twoVertexGraph_bubble_eq_univ {D : ℕ} {S : Finset (Fin (D + 1))} (hS : S.Nonempty) (v : Bool) :
    (twoVertexGraph D).bubble S v = univ := by
  obtain ⟨c, hc⟩ := hS
  have h1 := mem_bubble_self (twoVertexGraph D) S v
  have h2 := inv_mem_bubble_of_mem (twoVertexGraph D) hc h1
  ext w
  simp only [mem_univ, iff_true]
  have : w = v ∨ w = (twoVertexGraph D).inv c v := by
    cases w <;> cases v <;> simp [twoVertexGraph]
  rcases this with rfl | rfl
  · exact h1
  · exact h2

/-- **Repeated simplices** (the graph with two vertices and three lines, Gurau 2010): the two top simplices
have the same vertex set, so the vertex-set map is not injective and the bridge does not apply. -/
theorem not_injective_vertexSet_example :
    ¬ Function.Injective (DualSimplex.vertexSet : DualSimplex (twoVertexGraph 2) → _) := by
  intro hinj
  have hne : ∀ c : Fin 3, (univ \ {c} : Finset (Fin 3)).Nonempty := by decide
  have hT : ∀ c : Fin 3, (DualSimplex.top (twoVertexGraph 2) true).vertexBubble c =
      (DualSimplex.top (twoVertexGraph 2) false).vertexBubble c := fun c => by
    rw [DualSimplex.vertexBubble_eq _ c (by simp : c ∈ (DualSimplex.top (twoVertexGraph 2) true).colors) (by simp : true ∈ (DualSimplex.top _ true).bub),
      DualSimplex.vertexBubble_eq _ c (by simp : c ∈ (DualSimplex.top (twoVertexGraph 2) false).colors) (by simp : false ∈ (DualSimplex.top _ false).bub),
      twoVertexGraph_bubble_eq_univ (hne c), twoVertexGraph_bubble_eq_univ (hne c)]
  have key : DualSimplex.vertexSet (DualSimplex.top (twoVertexGraph 2) true) =
      DualSimplex.vertexSet (DualSimplex.top (twoVertexGraph 2) false) := by
    ext ⟨c, B⟩
    rw [DualSimplex.mem_vertexSet, DualSimplex.mem_vertexSet, hT c]
    simp
  have h2 := congrArg DualSimplex.bub (hinj key)
  simp at h2

/-- **No repeated simplices** (non-vacuity): for the graph of dimension `0` with two vertices and one line
the vertex-set map is injective, so `vertexSetOrderIso` applies. -/
theorem injective_vertexSet_example :
    Function.Injective (DualSimplex.vertexSet : DualSimplex (twoVertexGraph 0) → _) := by
  intro σ τ h
  have hcol := DualSimplex.colors_eq_of_vertexSet_eq h
  obtain ⟨v, hv⟩ := σ.exists_mem_bub
  obtain ⟨w, hw⟩ := τ.exists_mem_bub
  rcases (σ.colors).eq_empty_or_nonempty with he | hne
  · have h0 : (univ \ σ.colors).Nonempty := by
      rw [he]; exact ⟨0, by simp⟩
    refine DualSimplex.ext' hcol ?_
    rw [DualSimplex.bub_eq_of_mem' σ hv, DualSimplex.bub_eq_of_mem' τ hw, ← hcol,
      twoVertexGraph_bubble_eq_univ h0, twoVertexGraph_bubble_eq_univ h0]
  · obtain ⟨c, hc⟩ := hne
    have hnil : ∀ x : Fin 1, (univ \ ({x} : Finset (Fin 1))) = ∅ := by decide
    have e1 := DualSimplex.vertexBubble_eq σ c hc hv
    have e2 := DualSimplex.vertexBubble_eq τ c (hcol ▸ hc) hw
    have e3 := DualSimplex.vertexBubble_eq_of_vertexSet_eq h hc
    rw [e1, e2, hnil c, bubble_empty, bubble_empty] at e3
    have hvw : v = w := by simpa using e3
    subst hvw
    have hallσ : σ.colors = univ := eq_univ_of_forall fun x => by
      have hx : x = c := Fin.ext (by have := x.2; have := c.2; omega)
      rwa [hx]
    refine DualSimplex.ext' hcol ?_
    rw [DualSimplex.bub_eq_of_mem' σ hv, DualSimplex.bub_eq_of_mem' τ hw, ← hcol, hallσ]

end ColoredGraph

end Lightlike.GFT
