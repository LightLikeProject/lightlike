import Lightlike.PL.Complex3

/-!
# Cycles are PL 1-spheres

A closed polygon in the combinatorial sense, a connected graph in which every vertex lies in two
edges, is obtained from the boundary of a triangle by subdividing edges. Subdividing an edge by a
new vertex is a bistellar move, hence a stellar equivalence, so such a graph generates a PL
1-sphere. This is the one-dimensional case of `isPLSphere_closure_of_isSphere2`; it identifies the
vertex links of the closed surfaces of `Lightlike/Surfaces/` as PL 1-spheres.

## Main results

* `Move1`, `IsSphere1`: subdividing an edge, and the graphs reached from a triangle boundary.
* `isPLSphere_closure_of_isSphere1`: such a graph generates a PL 1-sphere.
* `CycleGraph`, `CycleGraph.isSphere1`: a connected graph with two edges at every vertex is one
  of them.
-/

open Finset Lightlike.PR

namespace Lightlike.PL

open SComplex

variable {V : Type*} [DecidableEq V]

/-- The three edges of the triangle `abc`. -/
def bdry1 (a b c : V) : Finset (Finset V) := {{a, b}, {a, c}, {b, c}}

lemma closure_bdry1 {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    SComplex.closure (bdry1 a b c) = SComplex.boundary {a, b, c} := by
  refine SComplex.ext_mem fun s => ?_
  rw [SComplex.mem_closure, SComplex.mem_boundary]
  constructor
  · rintro ⟨t, ht, hst⟩
    refine hst.trans_ssubset (Finset.ssubset_iff_subset_ne.2 ⟨?_, ?_⟩)
    · simp only [bdry1, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> intro x <;> simp only [mem_insert, mem_singleton] <;> tauto
    · intro he
      have h3 := card_three hab hac hbc
      simp only [bdry1, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> rw [← he] at h3
      · rw [card_pair hab] at h3; omega
      · rw [card_pair hac] at h3; omega
      · rw [card_pair hbc] at h3; omega
  · intro hs
    obtain ⟨y, hy, hys⟩ := not_subset.1 hs.not_subset
    have hsub : ∀ z ∈ s, z ∈ ({a, b, c} : Finset V) := fun z hz => hs.subset hz
    simp only [mem_insert, mem_singleton] at hsub hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨{b, c}, by simp [bdry1], fun z hz => by
        rcases hsub z hz with rfl | rfl | rfl <;> simp_all⟩
    · exact ⟨{a, c}, by simp [bdry1], fun z hz => by
        rcases hsub z hz with rfl | rfl | rfl <;> simp_all⟩
    · exact ⟨{a, b}, by simp [bdry1], fun z hz => by
        rcases hsub z hz with rfl | rfl | rfl <;> simp_all⟩

/-- **Subdividing an edge `cd` of a graph by a new vertex `x`.** -/
inductive Move1 : Finset (Finset V) → Finset (Finset V) → Prop
  | sub12 {G : Finset (Finset V)} {c d x : V} (hcd : c ≠ d) (h : ({c, d} : Finset V) ∈ G)
      (hx : x ∉ verts2 G) :
      Move1 G (insert {c, x} (insert {d, x} (G.erase {c, d})))

/-- Every member of the family is an edge. -/
def IsTri1 (G : Finset (Finset V)) : Prop := ∀ e ∈ G, #e = 2

lemma Move1.tri_iff {G G' : Finset (Finset V)} (h : Move1 G G') : IsTri1 G ↔ IsTri1 G' := by
  cases h with
  | @sub12 c d x hcd h hx =>
    have hxc : x ≠ c := fun e => hx (mem_verts2.2 ⟨_, h, by simp [e]⟩)
    have hxd : x ≠ d := fun e => hx (mem_verts2.2 ⟨_, h, by simp [e]⟩)
    constructor
    · intro H e he
      simp only [mem_insert, mem_erase] at he
      rcases he with rfl | rfl | ⟨-, he⟩
      · exact card_pair hxc.symm
      · exact card_pair hxd.symm
      · exact H e he
    · intro H e he
      by_cases hed : e = {c, d}
      · rw [hed]; exact card_pair hcd
      · exact H e (by simp [he, hed])

/-- **Subdividing an edge is a stellar equivalence.** -/
theorem stellarEquiv_of_move1 {G G' : Finset (Finset V)} (h : Move1 G G') (hG : IsTri1 G) :
    StellarEquiv (SComplex.closure G) (SComplex.closure G') := by
  cases h with
  | @sub12 c d x hcd h hx =>
    have hxc : x ≠ c := fun e => hx (mem_verts2.2 ⟨_, h, by simp [e]⟩)
    have hxd : x ≠ d := fun e => hx (mem_verts2.2 ⟨_, h, by simp [e]⟩)
    have hmem : ∀ y ∈ ({x} : Finset V), {c, d} ∪ ({x} : Finset V).erase y ∈ G := by
      intro y hy
      rw [mem_singleton.1 hy, erase_singleton, union_empty]; exact h
    have hstar : ∀ t ∈ G, {c, d} ⊆ t →
        ∃ y ∈ ({x} : Finset V), t ⊆ {c, d} ∪ ({x} : Finset V).erase y := by
      intro t ht hsub
      refine ⟨x, mem_singleton_self x, ?_⟩
      rw [erase_singleton, union_empty]
      exact (eq_of_subset_of_card_le hsub (by rw [hG t ht, card_pair hcd])).ge
    have hnew : ∀ t ∈ G, ¬ ({x} : Finset V) ⊆ t := fun t ht hsub =>
      hx (mem_verts2.2 ⟨t, ht, singleton_subset_iff.1 hsub⟩)
    have hdis : Disjoint ({c, d} : Finset V) {x} := by vdisj
    have hb := SComplex.isBistellar_closure (by simp) (by simp) hdis hmem hstar hnew
    have key := SComplex.bistellar_closure (by simp) (by simp) hdis hmem hstar hnew
    have hres : SComplex.closure (insert {c, x} (insert {d, x} (G.erase {c, d})))
        = (SComplex.closure G).bistellar _ _ hb := by
      rw [key]
      congr 1
      have hf : G.filter (fun t => ¬ ({c, d} : Finset V) ⊆ t) = G.erase {c, d} := by
        ext t
        simp only [mem_filter, mem_erase]
        constructor
        · rintro ⟨ht, hn⟩
          exact ⟨by rintro rfl; exact hn subset_rfl, ht⟩
        · rintro ⟨h₁, ht⟩
          exact ⟨ht, fun hs => h₁ (eq_of_subset_of_card_le hs (by rw [hG t ht, card_pair hcd])).symm⟩
      have e₁ : ({c, d} : Finset V).erase c ∪ {x} = {d, x} := by vset_eq
      have e₂ : ({c, d} : Finset V).erase d ∪ {x} = {c, x} := by vset_eq
      rw [hf, image_insert, image_singleton, e₁, e₂]
      ext t
      simp only [mem_union, mem_insert, mem_singleton]
      tauto
    rw [hres]
    exact StellarEquiv.bistellar hb

/-- Chains of edge subdivisions and their inverses keep edge families and give stellar equivalent
complexes. -/
lemma stellarEquiv_of_eqvGen_move1 {G G' : Finset (Finset V)}
    (h : Relation.EqvGen Move1 G G') :
    (IsTri1 G ↔ IsTri1 G') ∧
      (IsTri1 G → StellarEquiv (SComplex.closure G) (SComplex.closure G')) := by
  induction h with
  | rel G G' h => exact ⟨h.tri_iff, fun hG => stellarEquiv_of_move1 h hG⟩
  | refl G => exact ⟨Iff.rfl, fun _ => .refl _⟩
  | symm G G' _ ih =>
    exact ⟨ih.1.symm, fun hG => (ih.2 (ih.1.2 hG)).symm⟩
  | trans G G' G'' _ _ ih₁ ih₂ =>
    exact ⟨ih₁.1.trans ih₂.1, fun hG => (ih₁.2 hG).trans (ih₂.2 (ih₁.1.1 hG))⟩

/-- A graph is a **combinatorial 1-sphere**: it is reached from the boundary of a triangle by
subdividing edges and their inverses. -/
def IsSphere1 (G : Finset (Finset V)) : Prop :=
  ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Relation.EqvGen Move1 (bdry1 a b c) G

/-- **A combinatorial 1-sphere generates a PL 1-sphere.** -/
theorem isPLSphere_closure_of_isSphere1 {G : Finset (Finset V)} (h : IsSphere1 G) :
    IsPLSphere 1 (SComplex.closure G) := by
  obtain ⟨a, b, c, hab, hac, hbc, hG⟩ := h
  have hT : IsTri1 (bdry1 a b c) := by
    intro e he
    simp only [bdry1, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact card_pair hab
    · exact card_pair hac
    · exact card_pair hbc
  have h₀ := isPLSphere_boundary (n := 1) (card_three hab hac hbc)
  rw [← closure_bdry1 hab hac hbc] at h₀
  exact h₀.of_stellarEquiv ((stellarEquiv_of_eqvGen_move1 hG).2 hT)

/-! ## Cycle graphs are combinatorial 1-spheres -/

/-- A **cycle graph**: a nonempty set of edges, in which every vertex lies in exactly two edges and
any two vertices are joined by a path. -/
structure CycleGraph (G : Finset (Finset V)) : Prop where
  nonempty : G.Nonempty
  tri : IsTri1 G
  deg : ∀ x ∈ verts2 G, #(G.filter (x ∈ ·)) = 2
  conn : IsConnEdges G

lemma exists_other_end {e : Finset V} {v : V} (he : #e = 2) (hv : v ∈ e) :
    ∃ u, u ≠ v ∧ e = {v, u} := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 he
  simp only [mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact ⟨y, hxy.symm, rfl⟩
  · exact ⟨x, hxy, pair_comm _ _⟩

/-- A vertex of a cycle graph and its two neighbours. -/
lemma CycleGraph.exists_nbrs {G : Finset (Finset V)} (hG : CycleGraph G) {v : V}
    (hv : v ∈ verts2 G) : ∃ u w : V, u ≠ w ∧ u ≠ v ∧ w ≠ v ∧ ({v, u} : Finset V) ∈ G ∧
      ({v, w} : Finset V) ∈ G ∧ ∀ e ∈ G, v ∈ e → e = {v, u} ∨ e = {v, w} := by
  obtain ⟨e₁, e₂, hne, hf⟩ := card_eq_two.1 (hG.deg v hv)
  have h₁ : e₁ ∈ G.filter (v ∈ ·) := by rw [hf]; simp
  have h₂ : e₂ ∈ G.filter (v ∈ ·) := by rw [hf]; simp
  obtain ⟨he₁, hv₁⟩ := mem_filter.1 h₁
  obtain ⟨he₂, hv₂⟩ := mem_filter.1 h₂
  obtain ⟨u, hu, rfl⟩ := exists_other_end (hG.tri e₁ he₁) hv₁
  obtain ⟨w, hw, rfl⟩ := exists_other_end (hG.tri e₂ he₂) hv₂
  refine ⟨u, w, fun h => hne (by rw [h]), hu, hw, he₁, he₂, fun e he hve => ?_⟩
  have : e ∈ G.filter (v ∈ ·) := mem_filter.2 ⟨he, hve⟩
  rw [hf] at this
  simpa using this

/-- If two neighbours of a vertex are adjacent, the cycle graph is a triangle. -/
lemma CycleGraph.eq_bdry1 {G : Finset (Finset V)} (hG : CycleGraph G) {v u w : V}
    (huw : u ≠ w) (huv : u ≠ v) (hwv : w ≠ v) (h₁ : ({v, u} : Finset V) ∈ G)
    (h₂ : ({v, w} : Finset V) ∈ G) (h₃ : ({u, w} : Finset V) ∈ G)
    (hall : ∀ e ∈ G, v ∈ e → e = {v, u} ∨ e = {v, w}) : G = bdry1 v u w := by
  set S : Finset V := {v, u, w} with hS
  -- every edge through a vertex of `S` lies in `S`
  have hcl : ∀ x ∈ S, ∀ e ∈ G, x ∈ e → e ⊆ S := by
    intro x hx e he hxe
    simp only [hS, mem_insert, mem_singleton] at hx
    have hdeg := hG.deg x (mem_verts2.2 ⟨e, he, hxe⟩)
    rcases hx with rfl | rfl | rfl
    · rcases hall e he hxe with rfl | rfl <;> intro z hz <;> simp only [hS, mem_insert, mem_singleton] at hz ⊢ <;> tauto
    · -- edges at `u`: `{u, v}` and `{u, w}`
      have hne : ({x, v} : Finset V) ≠ {x, w} := fun h => by
        have : v ∈ ({x, w} : Finset V) := h ▸ (by simp)
        simp only [mem_insert, mem_singleton] at this
        rcases this with h' | h'
        · exact huv h'.symm
        · exact hwv h'.symm
      have hsub : ({{x, v}, {x, w}} : Finset (Finset V)) ⊆ G.filter (x ∈ ·) := by
        intro f hf
        simp only [mem_insert, mem_singleton] at hf
        rcases hf with rfl | rfl
        · exact mem_filter.2 ⟨by rw [pair_comm]; exact h₁, by simp⟩
        · exact mem_filter.2 ⟨h₃, by simp⟩
      have heq := eq_of_subset_of_card_le hsub (by rw [hdeg, card_pair hne])
      have : e ∈ G.filter (x ∈ ·) := mem_filter.2 ⟨he, hxe⟩
      rw [← heq] at this
      simp only [mem_insert, mem_singleton] at this
      rcases this with rfl | rfl <;> intro z hz <;> simp only [hS, mem_insert, mem_singleton] at hz ⊢ <;> tauto
    · have hne : ({x, v} : Finset V) ≠ {x, u} := fun h => by
        have : v ∈ ({x, u} : Finset V) := h ▸ (by simp)
        simp only [mem_insert, mem_singleton] at this
        rcases this with h' | h'
        · exact hwv h'.symm
        · exact huv h'.symm
      have hsub : ({{x, v}, {x, u}} : Finset (Finset V)) ⊆ G.filter (x ∈ ·) := by
        intro f hf
        simp only [mem_insert, mem_singleton] at hf
        rcases hf with rfl | rfl
        · exact mem_filter.2 ⟨by rw [pair_comm]; exact h₂, by simp⟩
        · exact mem_filter.2 ⟨by rw [pair_comm]; exact h₃, by simp⟩
      have heq := eq_of_subset_of_card_le hsub (by rw [hdeg, card_pair hne])
      have : e ∈ G.filter (x ∈ ·) := mem_filter.2 ⟨he, hxe⟩
      rw [← heq] at this
      simp only [mem_insert, mem_singleton] at this
      rcases this with rfl | rfl <;> intro z hz <;> simp only [hS, mem_insert, mem_singleton] at hz ⊢ <;> tauto
  have hvS : v ∈ verts2 G := mem_verts2.2 ⟨_, h₁, by simp⟩
  have hreach : ∀ y, Relation.ReflTransGen (fun p q => ({p, q} : Finset V) ∈ G) v y → y ∈ S := by
    intro y hy
    induction hy with
    | refl => simp [hS]
    | tail _ hxy ih => exact (hcl _ ih _ hxy (by simp)) (by simp)
  have hverts : ∀ z ∈ verts2 G, z ∈ S := fun z hz => hreach z (hG.conn v hvS z hz)
  ext e
  constructor
  · intro he
    have hsub : e ⊆ S := fun z hz => hverts z (mem_verts2.2 ⟨e, he, hz⟩)
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 (hG.tri e he)
    have hx := hsub (by simp : x ∈ ({x, y} : Finset V))
    have hy := hsub (by simp : y ∈ ({x, y} : Finset V))
    simp only [hS, mem_insert, mem_singleton] at hx hy
    simp only [bdry1, mem_insert, mem_singleton]
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact absurd rfl hxy | simp [pair_comm]
  · intro he
    simp only [bdry1, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃

/-- The vertices after subdividing an edge by a new vertex. -/
lemma verts2_sub12 {S : Finset (Finset V)} {c d x : V} (h : ({c, d} : Finset V) ∈ S) :
    verts2 (insert {c, x} (insert {d, x} (S.erase {c, d}))) = insert x (verts2 S) := by
  ext y
  simp only [mem_verts2, mem_insert, mem_erase]
  constructor
  · rintro ⟨e, he, hy⟩
    rcases he with rfl | rfl | ⟨-, he⟩
    · simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Or.inr ⟨_, h, by simp⟩
      · exact Or.inl rfl
    · simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Or.inr ⟨_, h, by simp⟩
      · exact Or.inl rfl
    · exact Or.inr ⟨e, he, hy⟩
  · rintro (rfl | ⟨e, he, hy⟩)
    · exact ⟨{c, y}, Or.inl rfl, by simp⟩
    · by_cases hed : e = {c, d}
      · subst hed
        simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact ⟨{y, x}, Or.inl rfl, by simp⟩
        · exact ⟨{y, x}, Or.inr (Or.inl rfl), by simp⟩
      · exact ⟨e, Or.inr (Or.inr ⟨hed, he⟩), hy⟩

/-- **Subdividing an edge does not change the degrees of the old vertices.** -/
lemma card_filter_sub12 {S : Finset (Finset V)} {c d x : V} (hcd : c ≠ d)
    (h : ({c, d} : Finset V) ∈ S) (hx : x ∉ verts2 S) {y : V} (hy : y ≠ x) :
    #((insert ({c, x} : Finset V) (insert {d, x} (S.erase {c, d}))).filter (y ∈ ·)) =
      #(S.filter (y ∈ ·)) := by
  have hxS : ∀ e ∈ S, x ∉ e := fun e he hxe => hx (mem_verts2.2 ⟨e, he, hxe⟩)
  by_cases hyc : y = c
  · subst hyc
    have hf : (insert ({y, x} : Finset V) (insert {d, x} (S.erase {y, d}))).filter (y ∈ ·) =
        insert {y, x} ((S.filter (y ∈ ·)).erase {y, d}) := by
      ext e
      simp only [mem_filter, mem_insert, mem_erase]
      constructor
      · rintro ⟨rfl | rfl | ⟨hne, he⟩, hye⟩
        · exact Or.inl rfl
        · simp only [mem_insert, mem_singleton] at hye
          rcases hye with h' | h'
          · exact absurd h' hcd
          · exact absurd h' hy
        · exact Or.inr ⟨hne, he, hye⟩
      · rintro (rfl | ⟨hne, he, hye⟩)
        · exact ⟨Or.inl rfl, by simp⟩
        · exact ⟨Or.inr (Or.inr ⟨hne, he⟩), hye⟩
    rw [hf, card_insert_of_notMem (fun hm => hxS _ (mem_filter.1 (mem_of_mem_erase hm)).1 (by simp)),
      card_erase_of_mem (mem_filter.2 ⟨h, by simp⟩)]
    have : 0 < #(S.filter (y ∈ ·)) := card_pos.2 ⟨_, mem_filter.2 ⟨h, by simp⟩⟩
    omega
  by_cases hyd : y = d
  · subst hyd
    have hf : (insert ({c, x} : Finset V) (insert {y, x} (S.erase {c, y}))).filter (y ∈ ·) =
        insert {y, x} ((S.filter (y ∈ ·)).erase {c, y}) := by
      ext e
      simp only [mem_filter, mem_insert, mem_erase]
      constructor
      · rintro ⟨rfl | rfl | ⟨hne, he⟩, hye⟩
        · simp only [mem_insert, mem_singleton] at hye
          rcases hye with h' | h'
          · exact absurd h'.symm hcd
          · exact absurd h' hy
        · exact Or.inl rfl
        · exact Or.inr ⟨hne, he, hye⟩
      · rintro (rfl | ⟨hne, he, hye⟩)
        · exact ⟨Or.inr (Or.inl rfl), by simp⟩
        · exact ⟨Or.inr (Or.inr ⟨hne, he⟩), hye⟩
    rw [hf, card_insert_of_notMem (fun hm => hxS _ (mem_filter.1 (mem_of_mem_erase hm)).1 (by simp)),
      card_erase_of_mem (mem_filter.2 ⟨h, by simp⟩)]
    have : 0 < #(S.filter (y ∈ ·)) := card_pos.2 ⟨_, mem_filter.2 ⟨h, by simp⟩⟩
    omega
  · congr 1
    ext e
    simp only [mem_filter, mem_insert, mem_erase]
    constructor
    · rintro ⟨rfl | rfl | ⟨hne, he⟩, hye⟩
      · simp only [mem_insert, mem_singleton] at hye
        rcases hye with h' | h'
        · exact absurd h' hyc
        · exact absurd h' hy
      · simp only [mem_insert, mem_singleton] at hye
        rcases hye with h' | h'
        · exact absurd h' hyd
        · exact absurd h' hy
      · exact ⟨he, hye⟩
    · rintro ⟨he, hye⟩
      refine ⟨Or.inr (Or.inr ⟨fun hed => ?_, he⟩), hye⟩
      subst hed
      simp only [mem_insert, mem_singleton] at hye
      rcases hye with h' | h'
      · exact hyc h'
      · exact hyd h'

/-- Removing a vertex of a cycle graph and joining its two neighbours. -/
lemma CycleGraph.reduce {G : Finset (Finset V)} (hG : CycleGraph G) {v u w : V} (huw : u ≠ w)
    (huv : u ≠ v) (hwv : w ≠ v) (h₁ : ({v, u} : Finset V) ∈ G) (h₂ : ({v, w} : Finset V) ∈ G)
    (hall : ∀ e ∈ G, v ∈ e → e = {v, u} ∨ e = {v, w}) (h₃ : ({u, w} : Finset V) ∉ G) :
    ∃ G₀ : Finset (Finset V), CycleGraph G₀ ∧ Move1 G₀ G ∧ #(verts2 G₀) + 1 = #(verts2 G) := by
  set G₀ : Finset (Finset V) := insert {u, w} ((G.erase {v, u}).erase {v, w}) with hG₀
  have hne₁ : ({v, u} : Finset V) ≠ {v, w} := fun h => by
    have : u ∈ ({v, w} : Finset V) := h ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h'
    · exact huv h'
    · exact huw h'
  have hG₀v : v ∉ verts2 G₀ := by
    rw [mem_verts2]
    rintro ⟨e, he, hve⟩
    rw [hG₀, mem_insert, mem_erase, mem_erase] at he
    rcases he with rfl | ⟨hne2, hne1, he⟩
    · simp only [mem_insert, mem_singleton] at hve
      rcases hve with h | h
      · exact huv h.symm
      · exact hwv h.symm
    · rcases hall e he hve with rfl | rfl
      · exact hne1 rfl
      · exact hne2 rfl
  have hmem : ({u, w} : Finset V) ∈ G₀ := mem_insert_self _ _
  have hEq : insert ({u, v} : Finset V) (insert {w, v} (G₀.erase {u, w})) = G := by
    have e0 : G₀.erase {u, w} = (G.erase {v, u}).erase {v, w} := by
      rw [hG₀, erase_insert_eq_erase]
      refine erase_eq_of_notMem fun hm => h₃ ?_
      exact mem_of_mem_erase (mem_of_mem_erase hm)
    rw [e0, pair_comm u v, pair_comm w v]
    ext z
    simp only [mem_insert, mem_erase]
    constructor
    · rintro (rfl | rfl | ⟨-, -, hz⟩)
      · exact h₁
      · exact h₂
      · exact hz
    · intro hz
      by_cases h1 : z = {v, u}
      · exact Or.inl h1
      · by_cases h2 : z = {v, w}
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨h2, h1, hz⟩)
  have hmv : Move1 G₀ G := by
    have := Move1.sub12 (G := G₀) (c := u) (d := w) (x := v) huw hmem hG₀v
    rwa [hEq] at this
  have hverts : verts2 G = insert v (verts2 G₀) := by
    rw [← hEq]; exact verts2_sub12 hmem
  refine ⟨G₀, ⟨⟨_, hmem⟩, ?_, ?_, ?_⟩, hmv, ?_⟩
  · intro e he
    rw [hG₀, mem_insert, mem_erase, mem_erase] at he
    rcases he with rfl | ⟨-, -, he⟩
    · exact card_pair huw
    · exact hG.tri e he
  · intro y hy
    have hyv : y ≠ v := fun e => hG₀v (e ▸ hy)
    have := card_filter_sub12 (S := G₀) huw hmem hG₀v hyv
    rw [hEq] at this
    rw [← this]
    refine hG.deg y ?_
    rw [hverts]
    exact mem_insert_of_mem hy
  · exact (connEdges_subdivide huw hmem hG₀v).2 (hEq ▸ hG.conn)
  · rw [hverts, card_insert_of_notMem hG₀v]

/-- **A cycle graph is a combinatorial 1-sphere**: it is reached from the boundary of a triangle by
subdividing edges. -/
theorem CycleGraph.isSphere1 {G : Finset (Finset V)} (hG : CycleGraph G) : IsSphere1 G := by
  induction hn : #(verts2 G) using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    obtain ⟨e, he⟩ := hG.nonempty
    obtain ⟨x, hx⟩ : e.Nonempty := card_pos.1 (by rw [hG.tri e he]; norm_num)
    have hv : x ∈ verts2 G := mem_verts2.2 ⟨e, he, hx⟩
    obtain ⟨u, w, huw, huv, hwv, h₁, h₂, hall⟩ := hG.exists_nbrs hv
    by_cases h₃ : ({u, w} : Finset V) ∈ G
    · exact ⟨x, u, w, huv.symm, hwv.symm, huw,
        (hG.eq_bdry1 huw huv hwv h₁ h₂ h₃ hall) ▸ Relation.EqvGen.refl _⟩
    · obtain ⟨G₀, hG₀, hmv, hcard⟩ := hG.reduce huw huv hwv h₁ h₂ hall h₃
      obtain ⟨a, b, c, hab, hac, hbc, hchain⟩ := ih (#(verts2 G₀)) (by omega) hG₀ rfl
      exact ⟨a, b, c, hab, hac, hbc, hchain.trans _ _ _ (Relation.EqvGen.rel _ _ hmv)⟩

/-- **A cycle graph generates a PL 1-sphere.** -/
theorem CycleGraph.isPLSphere {G : Finset (Finset V)} (hG : CycleGraph G) :
    IsPLSphere 1 (SComplex.closure G) :=
  isPLSphere_closure_of_isSphere1 hG.isSphere1

end Lightlike.PL
