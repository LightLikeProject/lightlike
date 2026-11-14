import Lightlike.Surfaces.Local
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Arcs in vertex links

The link of a vertex of a closed surface is a connected edge set in which every vertex lies in
exactly two edges, a cycle. This file proves the facts about such edge sets used to cut a surface
along a curve:

* `even_sum_edeg`: the handshake lemma on a set of vertices closed under adjacency;
* `connEdges_erase_edge`: a connected 2-regular edge set minus one edge is still connected;
* `connEdges_filter_notMem`: a connected 2-regular edge set minus one vertex is still
  connected;
* `IsSurface.edeg_lk2`: vertex links of closed surfaces are 2-regular;
* `IsSurface.exists_arc`: in the link of `u`, from a vertex `p` through its neighbour `s` there
  is an arc of distinct vertices to any other vertex `q` of the link.
-/

open Finset

namespace Lightlike.Surfaces

open Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-! ## Degrees in edge sets -/

/-- The number of edges of the edge set `S` containing the vertex `x`. -/
def edeg (S : Finset (Finset V)) (x : V) : ℕ := #(S.filter (x ∈ ·))

/-- **Handshake on a closed vertex set.** If every edge of `S` has two vertices and the vertex set
`C` contains, with one vertex of an edge, the whole edge, then the degrees over `C` add up to an
even number. -/
lemma even_sum_edeg {S : Finset (Finset V)} (hS : ∀ e ∈ S, #e = 2) {C : Finset V}
    (hC : ∀ e ∈ S, ∀ x ∈ e, x ∈ C → e ⊆ C) : Even (∑ x ∈ C, edeg S x) := by
  have hsum : ∑ x ∈ C, edeg S x = ∑ e ∈ S, #(C.filter (· ∈ e)) := by
    simp only [edeg, card_filter]
    exact Finset.sum_comm
  rw [hsum]
  apply Finset.even_sum
  intro e he
  by_cases h : ∃ x ∈ e, x ∈ C
  · obtain ⟨x, hx, hxC⟩ := h
    have : C.filter (· ∈ e) = e := by
      ext y
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun hy => ⟨hC e he x hx hxC hy, hy⟩⟩
    rw [this, hS e he]
    exact even_two
  · have : C.filter (· ∈ e) = ∅ := filter_eq_empty_iff.mpr (fun y hyC hye => h ⟨y, hye, hyC⟩)
    rw [this, card_empty]
    exact ⟨0, rfl⟩

/-- Two equal two-element sets: the elements match in one of the two orders. -/
lemma pair_cases {a b x y : V} (h : ({x, y} : Finset V) = {a, b}) (hxy : x ≠ y) :
    (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  have hx : x ∈ ({a, b} : Finset V) := h ▸ by simp
  have hy : y ∈ ({a, b} : Finset V) := h ▸ by simp
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl hxy

omit [DecidableEq V] in
/-- The reflexive-transitive closure of a symmetric relation is symmetric. -/
lemma rtg_symm {R : V → V → Prop} (hs : ∀ a b, R a b → R b a) {a b : V}
    (h : Relation.ReflTransGen R a b) : Relation.ReflTransGen R b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (hs _ _ hbc) ih

/-- A pair with two elements consists of distinct elements. -/
lemma ne_of_pair_card {x y : V} (h : #({x, y} : Finset V) = 2) : x ≠ y := by
  rintro rfl
  simp at h

/-- **A connected 2-regular edge set minus one edge is connected.** Removing the edge `ab` of a
connected edge set in which every vertex lies in two edges leaves `b` reachable from `a`: the
vertices reachable from `a` would otherwise have an odd degree sum. -/
lemma connEdges_erase_edge {S : Finset (Finset V)} (hc : IsConnEdges S)
    (h2 : ∀ e ∈ S, #e = 2) (hreg : ∀ x ∈ verts2 S, edeg S x = 2) {a b : V}
    (hab : ({a, b} : Finset V) ∈ S) : IsConnEdges (S.erase {a, b}) := by
  have hne : a ≠ b := ne_of_pair_card (h2 _ hab)
  set R : V → V → Prop := fun p q => ({p, q} : Finset V) ∈ S.erase {a, b} with hR
  have hsymm : ∀ p q, R p q → R q p := fun p q h => by simpa only [hR, pair_comm] using h
  have key : Relation.ReflTransGen R a b := by
    classical
    by_contra hnb
    let C := (verts2 S).filter (fun x => Relation.ReflTransGen R a x)
    have haC : a ∈ C := mem_filter.mpr ⟨mem_verts2.mpr ⟨_, hab, by simp⟩, Relation.ReflTransGen.refl⟩
    have hbC : ∀ x ∈ C, x ≠ b := fun x hx h => hnb (h ▸ (mem_filter.mp hx).2)
    have hC : ∀ e ∈ S.erase {a, b}, ∀ x ∈ e, x ∈ C → e ⊆ C := by
      intro e he x hx hxC y hy
      have heS := mem_of_mem_erase he
      have hxa := (mem_filter.mp hxC).2
      refine mem_filter.mpr ⟨mem_verts2.mpr ⟨e, heS, hy⟩, ?_⟩
      by_cases hxy : x = y
      · exact hxy ▸ hxa
      · have : e = {x, y} := by
          symm
          apply eq_of_subset_of_card_le
          · intro z hz
            simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl <;> assumption
          · rw [h2 e heS, card_pair hxy]
        exact hxa.tail (by rw [hR]; simp only; rw [← this]; exact he)
    have heven := even_sum_edeg (S := S.erase {a, b}) (fun e he => h2 e (mem_of_mem_erase he)) hC
    have hdeg : ∀ x ∈ C.erase a, edeg (S.erase {a, b}) x = 2 := by
      intro x hx
      obtain ⟨hxa, hxC⟩ := mem_erase.mp hx
      have hxb := hbC x hxC
      have : (S.erase {a, b}).filter (x ∈ ·) = S.filter (x ∈ ·) := by
        rw [filter_erase]
        apply erase_eq_of_notMem
        simp [hxa, hxb]
      rw [edeg, this]
      exact hreg x (mem_filter.mp hxC).1
    have hdega : edeg (S.erase {a, b}) a = 1 := by
      rw [edeg, filter_erase, card_erase_of_mem (mem_filter.mpr ⟨hab, by simp⟩)]
      rw [← edeg, hreg a (mem_verts2.mpr ⟨_, hab, by simp⟩)]
    rw [← add_sum_erase _ _ haC, hdega, sum_congr rfl hdeg, sum_const, smul_eq_mul] at heven
    obtain ⟨r, hr⟩ := heven
    omega
  intro x hx y hy
  have hx' : x ∈ verts2 S := by
    obtain ⟨e, he, hxe⟩ := mem_verts2.mp hx
    exact mem_verts2.mpr ⟨e, mem_of_mem_erase he, hxe⟩
  have hy' : y ∈ verts2 S := by
    obtain ⟨e, he, hye⟩ := mem_verts2.mp hy
    exact mem_verts2.mpr ⟨e, mem_of_mem_erase he, hye⟩
  have hstep : ∀ p q, ({p, q} : Finset V) ∈ S → Relation.ReflTransGen R p q := by
    intro p q hpq
    by_cases h : ({p, q} : Finset V) = {a, b}
    · rcases pair_cases h (ne_of_pair_card (h2 _ hpq)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact key
      · exact rtg_symm hsymm key
    · exact .single (mem_erase.mpr ⟨h, hpq⟩)
  have hxy := hc x hx' y hy'
  clear hy hy'
  induction hxy with
  | refl => exact .refl
  | tail _ hpq ih => exact ih.trans (hstep _ _ hpq)

/-- In an edge set where `x` lies in two edges, an edge `xy` has a partner `xz` with `z ≠ y`. -/
lemma other_edge {S : Finset (Finset V)} (h2 : ∀ e ∈ S, #e = 2) {x y : V}
    (hreg : edeg S x = 2) (hxy : ({x, y} : Finset V) ∈ S) :
    ∃ z, z ≠ y ∧ z ≠ x ∧ ({x, z} : Finset V) ∈ S ∧
      ∀ e ∈ S, x ∈ e → e = {x, y} ∨ e = {x, z} := by
  have hxy' : x ≠ y := ne_of_pair_card (h2 _ hxy)
  obtain ⟨e₁, e₂, hne, hf⟩ := card_eq_two.mp hreg
  have hmem : ({x, y} : Finset V) ∈ S.filter (x ∈ ·) := mem_filter.mpr ⟨hxy, by simp⟩
  obtain ⟨f, hf', hfne⟩ : ∃ f ∈ S.filter (x ∈ ·), f ≠ {x, y} := by
    rw [hf] at hmem ⊢
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with h | h
    · exact ⟨e₂, by simp, fun h' => hne (h'.trans h).symm⟩
    · exact ⟨e₁, by simp, fun h' => hne (h'.trans h)⟩
  obtain ⟨hfS, hxf⟩ := mem_filter.mp hf'
  obtain ⟨z, hz⟩ : ∃ z ∈ f, z ≠ x := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have : f ⊆ {x} := fun w hw => mem_singleton.mpr (hcon w hw)
    have := card_le_card this
    rw [h2 f hfS, card_singleton] at this
    omega
  have hfeq : f = {x, z} := by
    symm
    apply eq_of_subset_of_card_le
    · intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      exacts [hxf, hz.1]
    · rw [h2 f hfS, card_pair hz.2.symm]
  subst hfeq
  have hzy : z ≠ y := fun h => hfne (by rw [h])
  refine ⟨z, hzy, hz.2, hfS, fun e he hxe => ?_⟩
  have h2' : S.filter (x ∈ ·) = {{x, y}, {x, z}} := by
    symm
    apply eq_of_subset_of_card_le
    · intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      exacts [hmem, hf']
    · change edeg S x ≤ _
      rw [hreg, card_pair hfne.symm]
  have : e ∈ S.filter (x ∈ ·) := mem_filter.mpr ⟨he, hxe⟩
  rw [h2'] at this
  simpa using this

/-- **A connected 2-regular edge set minus one vertex is connected.** The edges avoiding a
vertex `p` of a connected edge set in which every vertex lies in two edges still form a
connected edge set: remove one edge `ps` at `p` (`connEdges_erase_edge`), then contract the
remaining edge `pt` at `p` onto `t`. -/
lemma connEdges_filter_notMem {S : Finset (Finset V)} (hc : IsConnEdges S)
    (h2 : ∀ e ∈ S, #e = 2) (hreg : ∀ x ∈ verts2 S, edeg S x = 2) {p : V} (hp : p ∈ verts2 S) :
    IsConnEdges (S.filter (p ∉ ·)) := by
  obtain ⟨e, heS, hpe⟩ := mem_verts2.mp hp
  obtain ⟨s, hs⟩ : ∃ s ∈ e, s ≠ p := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have : e ⊆ {p} := fun w hw => mem_singleton.mpr (hcon w hw)
    have := card_le_card this
    rw [h2 e heS, card_singleton] at this
    omega
  have hes : e = {p, s} := by
    symm
    apply eq_of_subset_of_card_le
    · intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      exacts [hpe, hs.1]
    · rw [h2 e heS, card_pair hs.2.symm]
  subst hes
  obtain ⟨t, hts, htp, hpt, huniq⟩ := other_edge h2 (hreg p hp) heS
  have hc' := connEdges_erase_edge hc h2 hreg heS
  set R : V → V → Prop := fun a b => ({a, b} : Finset V) ∈ S.filter (p ∉ ·) with hR
  let f : V → V := fun z => if z = p then t else z
  have hstep : ∀ a b, ({a, b} : Finset V) ∈ S.erase {p, s} →
      Relation.ReflTransGen R (f a) (f b) := by
    intro a b hab
    obtain ⟨hne, habS⟩ := mem_erase.mp hab
    by_cases hpab : p ∈ ({a, b} : Finset V)
    · rcases huniq _ habS hpab with h | h
      · exact absurd h hne
      · rcases pair_cases h (ne_of_pair_card (h2 _ habS)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [f, ↓reduceIte, htp]
          exact .refl
        · simp only [f, ↓reduceIte, htp]
          exact .refl
    · have hap : a ≠ p := fun h => hpab (by simp [h])
      have hbp : b ≠ p := fun h => hpab (by simp [h])
      simp only [f, hap, hbp, ite_false]
      exact .single (mem_filter.mpr ⟨habS, hpab⟩)
  intro x hx y hy
  obtain ⟨ex, hex, hxe⟩ := mem_verts2.mp hx
  obtain ⟨ey, hey, hye⟩ := mem_verts2.mp hy
  have hxp : x ≠ p := fun h => (mem_filter.mp hex).2 (h ▸ hxe)
  have hyp : y ≠ p := fun h => (mem_filter.mp hey).2 (h ▸ hye)
  have hmem : ∀ e ∈ S.filter (p ∉ ·), e ∈ S.erase {p, s} := fun e he =>
    mem_erase.mpr ⟨fun h => (mem_filter.mp he).2 (h ▸ by simp), (mem_filter.mp he).1⟩
  have hxy := hc' x (mem_verts2.mpr ⟨ex, hmem _ hex, hxe⟩) y (mem_verts2.mpr ⟨ey, hmem _ hey, hye⟩)
  have : Relation.ReflTransGen R (f x) (f y) := by
    clear hy hey hye hyp
    induction hxy with
    | refl => exact .refl
    | tail _ hbc ih => exact ih.trans (hstep _ _ hbc)
  have hfx : f x = x := by simp [f, hxp]
  have hfy : f y = y := by simp [f, hyp]
  rw [hfx, hfy] at this
  exact this

/-! ## Links of closed surfaces -/

/-- The edges of a vertex link of a closed surface have two vertices. -/
lemma IsSurface.card_lk2 {L : Finset (Finset V)} (hS : IsSurface L) {u : V} :
    ∀ e ∈ lk2 L u, #e = 2 := by
  intro e he
  obtain ⟨hue, hins⟩ := mem_lk2.mp he
  have := hS.card _ hins
  rw [card_insert_of_notMem hue] at this
  omega

/-- **Vertex links of closed surfaces are 2-regular**: every vertex of the link of `u` lies in
exactly two of its edges. -/
lemma IsSurface.edeg_lk2 {L : Finset (Finset V)} (hS : IsSurface L) {u x : V}
    (hx : x ∈ verts2 (lk2 L u)) : edeg (lk2 L u) x = 2 := by
  obtain ⟨e, he, hxe⟩ := mem_verts2.mp hx
  obtain ⟨hue, hins⟩ := mem_lk2.mp he
  have hc := hS.card_lk2 e he
  obtain ⟨y, hy⟩ : ∃ y ∈ e, y ≠ x := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have : e ⊆ {x} := fun w hw => mem_singleton.mpr (hcon w hw)
    have := card_le_card this
    rw [hc, card_singleton] at this
    omega
  have hexy : e = {x, y} := by
    symm
    apply eq_of_subset_of_card_le
    · intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      exacts [hxe, hy.1]
    · rw [hc, card_pair hy.2.symm]
  subst hexy
  obtain ⟨z, hzy, hzu, hzx, hz, hstar⟩ := hS.other_tri hins
  have hux : u ≠ x := fun h => hue (h ▸ by simp)
  have hmemz : ({x, z} : Finset V) ∈ lk2 L u := by
    refine mem_lk2.mpr ⟨?_, ?_⟩
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hux, hzu.symm⟩
    · exact hz
  have hne : ({x, y} : Finset V) ≠ {x, z} :=
    ne_of_mem_notMem (y := y) (by simp) (by simp [hy.2, hzy.symm])
  have : (lk2 L u).filter (x ∈ ·) = {{x, y}, {x, z}} := by
    ext f
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hf, hxf⟩
      obtain ⟨huf, hfins⟩ := mem_lk2.mp hf
      rcases hstar _ hfins (by
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact mem_insert_self _ _
        · exact mem_insert_of_mem hxf) with h | h
      · left
        rw [← erase_insert huf, h]
        ext w; simp only [mem_erase, mem_insert, mem_singleton]
        constructor
        · rintro ⟨hw, rfl | rfl | rfl⟩ <;> simp_all
        · rintro (rfl | rfl)
          · exact ⟨Ne.symm hux, Or.inr (Or.inl rfl)⟩
          · exact ⟨fun h => hue (h ▸ by simp), Or.inr (Or.inr rfl)⟩
      · right
        rw [← erase_insert huf, h]
        ext w; simp only [mem_erase, mem_insert, mem_singleton]
        constructor
        · rintro ⟨hw, rfl | rfl | rfl⟩ <;> simp_all
        · rintro (rfl | rfl)
          · exact ⟨Ne.symm hux, Or.inr (Or.inl rfl)⟩
          · exact ⟨hzu, Or.inr (Or.inr rfl)⟩
    · rintro (rfl | rfl)
      · exact ⟨he, by simp⟩
      · exact ⟨hmemz, by simp⟩
  rw [edeg, this, card_pair hne]

omit [DecidableEq V] in
/-- A chain of `R`-steps is a chain of adjacencies in the simple graph generated by `R`. -/
lemma rtg_fromRel {R : V → V → Prop} {a b : V} (h : Relation.ReflTransGen R a b) :
    Relation.ReflTransGen (SimpleGraph.fromRel R).Adj a b := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    by_cases h : b = c
    · exact h ▸ ih
    · exact ih.tail ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨h, Or.inl hbc⟩)

omit [DecidableEq V] in
/-- If no edge of `G` ends in the set `X`, a walk starting outside `X` stays outside `X`. -/
lemma walk_support_avoid {G : SimpleGraph V} {X : V → Prop} (hG : ∀ a b, G.Adj a b → ¬ X b) :
    ∀ {a b : V} (w : G.Walk a b), ¬ X a → ∀ x ∈ w.support, ¬ X x
  | _, _, .nil, ha, x, hx => by
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
    exact hx ▸ ha
  | _, _, .cons h w, ha, x, hx => by
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · exact walk_support_avoid hG w (hG _ _ h) x hx

/-- **An arc in a vertex link.** If `{u, p, s}` is a triangle of a closed surface and `q ≠ p` is
another vertex of the link of `u`, there is a list `p, s, …, q` of distinct vertices, all
different from `u`, with `{u, a, b}` a triangle for any two consecutive entries `a, b`. -/
theorem IsSurface.exists_arc {L : Finset (Finset V)} (hS : IsSurface L) {u p s q : V}
    (hτ : ({u, p, s} : Finset V) ∈ L) (hq : q ∈ verts2 (lk2 L u)) (hqp : q ≠ p) :
    ∃ l : List V, (p :: s :: l).Nodup ∧ u ∉ p :: s :: l ∧
      (p :: s :: l).IsChain (fun a b => ({u, a, b} : Finset V) ∈ L) ∧
      (s :: l).getLast? = some q := by
  obtain ⟨hup, hus, hps⟩ := tri_ne (hS.card _ hτ)
  have hu : u ∈ verts2 L := mem_verts2.mpr ⟨_, hτ, by simp⟩
  set S := lk2 L u with hSdef
  have hc : IsConnEdges S := hS.link u hu
  have h2 := hS.card_lk2 (u := u)
  have hreg : ∀ x ∈ verts2 S, edeg S x = 2 := fun x hx => hS.edeg_lk2 hx
  have hpsS : ({p, s} : Finset V) ∈ S := by
    refine mem_lk2.mpr ⟨?_, hτ⟩
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hup, hus⟩
  have hpS : p ∈ verts2 S := mem_verts2.mpr ⟨_, hpsS, by simp⟩
  have hsS : s ∈ verts2 S := mem_verts2.mpr ⟨_, hpsS, by simp⟩
  have hc' := connEdges_filter_notMem hc h2 hreg hpS
  -- `s` and `q` are vertices of the link minus `p`
  have hvert : ∀ x ∈ verts2 S, x ≠ p → x ∈ verts2 (S.filter (p ∉ ·)) := by
    intro x hx hxp
    obtain ⟨e, he, hxe⟩ := mem_verts2.mp hx
    obtain ⟨y, hy⟩ : ∃ y ∈ e, y ≠ x := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      have : e ⊆ {x} := fun w hw => mem_singleton.mpr (hcon w hw)
      have := card_le_card this
      rw [h2 e he, card_singleton] at this
      omega
    have hexy : e = {x, y} := by
      symm
      apply eq_of_subset_of_card_le
      · intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl
        exacts [hxe, hy.1]
      · rw [h2 e he, card_pair hy.2.symm]
    subst hexy
    by_cases hyp : y = p
    · subst hyp
      obtain ⟨z, hzy, hzx, hxz, -⟩ := other_edge h2 (hreg x hx) he
      refine mem_verts2.mpr ⟨{x, z}, mem_filter.mpr ⟨hxz, ?_⟩, by simp⟩
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hxp.symm, hzy.symm⟩
    · refine mem_verts2.mpr ⟨{x, y}, mem_filter.mpr ⟨he, ?_⟩, by simp⟩
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hxp.symm, Ne.symm hyp⟩
  have hreach := hc' s (hvert s hsS hps.symm) q (hvert q hq hqp)
  -- a path in the simple graph of the link minus `p`
  let G : SimpleGraph V := SimpleGraph.fromRel (fun a b => ({a, b} : Finset V) ∈ S.filter (p ∉ ·))
  have hG : Relation.ReflTransGen G.Adj s q := rtg_fromRel hreach
  obtain ⟨w⟩ := (SimpleGraph.reachable_iff_reflTransGen s q).mpr hG
  have hpath := w.bypass_isPath
  set sup := w.bypass.support with hsup
  have hadj : ∀ a b, G.Adj a b → ({a, b} : Finset V) ∈ S.filter (p ∉ ·) := by
    intro a b h
    obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).mp h
    · exact h
    · rwa [pair_comm]
  have havoid : ∀ x ∈ sup, x ≠ p ∧ x ≠ u := by
    have := walk_support_avoid (X := fun x => x = p ∨ x = u) (G := G) (fun a b h hb => by
      have hm := mem_filter.mp (hadj a b h)
      rcases hb with rfl | rfl
      · exact hm.2 (by simp)
      · exact (mem_lk2.mp hm.1).1 (by simp)) w.bypass (by
        rintro (h | h)
        · exact hps h.symm
        · exact hus h.symm)
    intro x hx
    have := this x hx
    simp only [not_or] at this
    exact this
  have hcons : s :: sup.tail = sup := SimpleGraph.Walk.cons_tail_support _
  refine ⟨sup.tail, ?_, ?_, ?_, ?_⟩
  · rw [hcons]
    exact List.nodup_cons.mpr ⟨fun h => (havoid p h).1 rfl, hpath.support_nodup⟩
  · rw [hcons]
    simp only [List.mem_cons, not_or]
    exact ⟨hup, fun h => (havoid u h).2 rfl⟩
  · refine List.isChain_cons_cons.mpr ⟨hτ, ?_⟩
    rw [hcons]
    refine (SimpleGraph.Walk.isChain_adj_support w.bypass).imp (fun a b h => ?_)
    exact (mem_lk2.mp (mem_filter.mp (hadj a b h)).1).2
  · rw [hcons, List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil _)]
    simp

end Lightlike.Surfaces
