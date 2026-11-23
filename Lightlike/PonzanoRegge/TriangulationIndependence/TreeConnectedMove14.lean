module

public import Lightlike.PonzanoRegge.TriangulationIndependence.CompleteSkeleton
public import Lightlike.PonzanoRegge.TriangulationIndependence.TreeEdge
public import Lightlike.PonzanoRegge.Move14

/-!
# Tree-connectedness is preserved by the 1-4 move

Closed-manifold gauge-tree programme (Freidel–Louapre 2004, Section III), positive side.

`treeConnected_move14`: if any two maximal trees of `K` are connected by triangle exchanges, so are
any two maximal trees of `move14 K h`. Proof: in a maximal tree of `move14 K h` the new vertex `E`
has degree at least one and its neighbours lie in `{A, B, C, D}`; two tree edges `xE`, `yE` give a
triangle exchange `(x, E, y)` (the triangle `xyE` exists, and `xy` is not a tree edge because a
spanning tree has no triangle, `IsSpanningTree.not_mem_of_two`), which lowers the degree of `E`.
So every tree is exchange-connected to a tree of `K` with a leaf edge `xE` (`reduce_leaf`, using
`IsSpanningTree.erase_leaf`); such trees are exchange-connected among themselves
(`leafForm_eq`): the exchanges of `K` lift, and the leaf moves from `x` to `x'` along a tree edge
`xx'`, which exists after exchanges because every edge of `K` lies in a maximal tree
(`exists_isMaxTree_mem`).

Consequence (`treeConnected_of_stacked`, `amplitudeGF_stacked_eq`): every complex stacked from the
boundary of the 4-simplex by 1-4 moves has tree-independent gauge-fixed amplitude, for all cut-offs.
This is the first infinite family of closed combinatorial 3-manifolds (stacked 3-spheres) for
which the closed-manifold gauge-tree question is answered affirmatively.
-/

@[expose] public section

namespace Lightlike.PR

open Finset

variable {V : Type*} [DecidableEq V]

/-- A spanning tree has no triangle: if `xz` and `yz` are tree edges, `xy` is not. -/
lemma IsSpanningTree.not_mem_of_two {W : Finset V} {T : Finset (Finset V)}
    (hT : IsSpanningTree W T) {x y z : V} (hx : x ∈ W) (hy : y ∈ W) (hz : z ∈ W)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h1 : ({x, z} : Finset V) ∈ T) (h2 : ({y, z} : Finset V) ∈ T) :
    ({x, y} : Finset V) ∉ T := by
  intro h3
  have hA := hT.isTree.isAcyclic
  rw [SimpleGraph.isAcyclic_iff_forall_isBridge] at hA
  have hb := @hA s((⟨x, hx⟩ : W), (⟨y, hy⟩ : W)) (by
    rw [SimpleGraph.mem_edgeSet, treeGraph_adj]
    exact ⟨fun h => hxy (congrArg Subtype.val h), Or.inl h3⟩)
  rw [SimpleGraph.isBridge_iff] at hb
  refine hb ?_
  have a1 : ((treeGraph W T).deleteEdges {s((⟨x, hx⟩ : W), (⟨y, hy⟩ : W))}).Adj
      ⟨x, hx⟩ ⟨z, hz⟩ := by
    rw [SimpleGraph.deleteEdges_adj, treeGraph_adj]
    refine ⟨⟨fun h => hxz (congrArg Subtype.val h), Or.inl h1⟩, ?_⟩
    intro hs
    rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hs) with ⟨-, h⟩ | ⟨h, -⟩
    · exact hyz (congrArg Subtype.val h).symm
    · exact hxy (congrArg Subtype.val h)
  have a2 : ((treeGraph W T).deleteEdges {s((⟨x, hx⟩ : W), (⟨y, hy⟩ : W))}).Adj
      ⟨z, hz⟩ ⟨y, hy⟩ := by
    rw [SimpleGraph.deleteEdges_adj, treeGraph_adj]
    refine ⟨⟨fun h => hyz (congrArg Subtype.val h).symm, Or.inr h2⟩, ?_⟩
    intro hs
    rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hs) with ⟨h, -⟩ | ⟨h, -⟩
    · exact hxz (congrArg Subtype.val h).symm
    · exact hyz (congrArg Subtype.val h).symm
  exact a1.reachable.trans a2.reachable

lemma exists_other_of_card_two {e : Finset V} {E : V} (h2 : #e = 2) (hE : E ∈ e) :
    ∃ y, y ≠ E ∧ e = {y, E} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
  simp only [mem_insert, mem_singleton] at hE
  rcases hE with rfl | rfl
  · exact ⟨b, hab.symm, pair_comm _ _⟩
  · exact ⟨a, hab, rfl⟩

/-- **Removing a leaf from a spanning tree** gives a spanning tree of the remaining vertices. -/
lemma IsSpanningTree.erase_leaf {W : Finset V} {T : Finset (Finset V)} {E x : V}
    (hT : IsSpanningTree (insert E W) T) (hE : E ∉ W) (hx : x ∈ W)
    (hxE : ({x, E} : Finset V) ∈ T) (hleaf : ∀ y, ({y, E} : Finset V) ∈ T → y = x) :
    IsSpanningTree W (T.erase {x, E}) := by
  have hxE' : x ≠ E := fun h => hE (h ▸ hx)
  have hmemE : ∀ e ∈ T, E ∈ e → e = {x, E} := by
    intro e he hEe
    obtain ⟨y, -, rfl⟩ := exists_other_of_card_two (hT.edge e he).2 hEe
    rw [hleaf y he]
  have hnE : ∀ e ∈ T.erase {x, E}, E ∉ e := fun e he hEe =>
    (mem_erase.mp he).1 (hmemE e (mem_erase.mp he).2 hEe)
  refine ⟨fun e he => ?_, fun u hu v hv => ?_, ?_⟩
  · have h := hT.edge e (mem_of_mem_erase he)
    refine ⟨fun z hz => ?_, h.2⟩
    rcases mem_insert.mp (h.1 hz) with rfl | hz'
    · exact absurd hz (hnE e he)
    · exact hz'
  · have key : ∀ b, Relation.ReflTransGen (fun a b => ({a, b} : Finset V) ∈ T) u b →
        (b ∈ W → Relation.ReflTransGen (fun a b => ({a, b} : Finset V) ∈ T.erase {x, E}) u b) ∧
        (b = E → Relation.ReflTransGen (fun a b => ({a, b} : Finset V) ∈ T.erase {x, E}) u x) := by
      intro b hb
      induction hb with
      | refl =>
        refine ⟨fun _ => .refl, fun h => ?_⟩
        exact absurd (h ▸ hu) hE
      | @tail b' c _ hbc ih =>
        constructor
        · intro hc
          have hcE : c ≠ E := fun h => hE (h ▸ hc)
          by_cases hb' : b' = E
          · subst hb'
            rw [pair_comm] at hbc
            have := hleaf c hbc
            subst this
            exact ih.2 rfl
          · have hb'W : b' ∈ W := by
              rcases mem_insert.mp ((hT.edge _ hbc).1 (by simp : b' ∈ ({b', c} : Finset V)))
                with h | h
              · exact absurd h hb'
              · exact h
            refine (ih.1 hb'W).tail (mem_erase.mpr ⟨?_, hbc⟩)
            intro h
            have : E ∈ ({b', c} : Finset V) := h ▸ (by simp)
            simp only [mem_insert, mem_singleton] at this
            rcases this with h | h
            · exact hb' h.symm
            · exact hcE h.symm
        · rintro rfl
          have := hleaf b' hbc
          subst this
          have hb'W : b' ∈ W := hx
          exact ih.1 hb'W
    exact (key v (hT.conn u (mem_insert_of_mem hu) v (mem_insert_of_mem hv))).1 hv
  · have h1 := hT.card
    rw [card_insert_of_notMem hE] at h1
    rw [card_erase_of_mem hxE]
    have : 0 < #T := card_pos.mpr ⟨_, hxE⟩
    omega

section Move14

variable {K : Complex3 V} {A B C D E : V}

lemma notMem_verts_of_isMove14 (h : IsMove14 K A B C D E) : E ∉ K.verts := fun hm => by
  obtain ⟨t, ht, hEt⟩ := Complex3.mem_verts.mp hm
  exact h.fresh t ht hEt

lemma mem_verts_of_mem_edges' {e : Finset V} (he : e ∈ K.edges) {y : V} (hy : y ∈ e) :
    y ∈ K.verts := by
  obtain ⟨t, ht, hst, -⟩ := Complex3.mem_edges.mp he
  exact Complex3.mem_verts.mpr ⟨t, ht, hst hy⟩

lemma edge_move14_of_mem (h : IsMove14 K A B C D E) {e : Finset V}
    (he : e ∈ (move14 K h).edges) (hE : E ∈ e) :
    ∃ x, x ∈ ({A, B, C, D} : Finset V) ∧ e = {x, E} := by
  rw [edges_move14] at he
  rcases mem_union.mp he with he | he
  · exact absurd (mem_verts_of_mem_edges' he hE) (notMem_verts_of_isMove14 h)
  · simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    exacts [⟨A, by simp, rfl⟩, ⟨B, by simp, rfl⟩, ⟨C, by simp, rfl⟩, ⟨D, by simp, rfl⟩]

lemma edge_move14_of_notMem (h : IsMove14 K A B C D E) {e : Finset V}
    (he : e ∈ (move14 K h).edges) (hE : E ∉ e) : e ∈ K.edges := by
  rw [edges_move14] at he
  rcases mem_union.mp he with he | he
  · exact he
  · simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> exact absurd (by simp) hE

lemma edge_E_mem_move14 (h : IsMove14 K A B C D E) {x : V} (hx : x ∈ ({A, B, C, D} : Finset V)) :
    ({x, E} : Finset V) ∈ (move14 K h).edges := by
  rw [edges_move14]
  apply mem_union_right
  simp only [mem_insert, mem_singleton] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl <;> simp

lemma edge_mem_of_mem_S (h : IsMove14 K A B C D E) {x y : V} (hx : x ∈ ({A, B, C, D} : Finset V))
    (hy : y ∈ ({A, B, C, D} : Finset V)) (hxy : x ≠ y) : ({x, y} : Finset V) ∈ K.edges :=
  Complex3.mem_edges.mpr ⟨_, h.mem, insert_subset hx (singleton_subset_iff.mpr hy), card_pair hxy⟩

lemma tri_E_mem_move14 (h : IsMove14 K A B C D E) {x y : V} (hx : x ∈ ({A, B, C, D} : Finset V))
    (hy : y ∈ ({A, B, C, D} : Finset V)) (hxy : x ≠ y) :
    ({x, y, E} : Finset V) ∈ (move14 K h).tris := by
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hxy
    | (rw [tris_move14]; apply mem_union_right; simp; done)
    | (rw [Finset.insert_comm, tris_move14]; apply mem_union_right; simp)

lemma mem_verts_of_mem_S (h : IsMove14 K A B C D E) {x : V}
    (hx : x ∈ ({A, B, C, D} : Finset V)) : x ∈ K.verts :=
  Complex3.mem_verts.mpr ⟨_, h.mem, hx⟩

/-- A triangle exchange of `K` lifts to `move14 K` with a fixed leaf edge `xE` added. -/
lemma lift_exchange (h : IsMove14 K A B C D E) {x : V} (hx : x ∈ ({A, B, C, D} : Finset V))
    {T T2 : Finset (Finset V)} (hs : TreeExchange K T T2) :
    TreeExchange (move14 K h) (insert {x, E} T) (insert {x, E} T2) := by
  obtain ⟨hT, huv, hvw, huw, hτ, he, hg, hf⟩ := hs
  rename_i u v w
  have hEv := notMem_verts_of_isMove14 h
  have hu : u ∈ K.verts := mem_verts_of_mem_edges' (hT he) (by simp)
  have hw : w ∈ K.verts := mem_verts_of_mem_edges' (hT hg) (by simp)
  have hv : v ∈ K.verts := mem_verts_of_mem_edges' (hT he) (by simp)
  have hne : ({x, E} : Finset V) ≠ {u, v} := fun hh =>
    hEv (mem_verts_of_mem_edges' (hT he) (hh ▸ (by simp : E ∈ ({x, E} : Finset V))))
  have hne' : ({x, E} : Finset V) ≠ {u, w} := fun hh => by
    have : E ∈ ({u, w} : Finset V) := hh ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with rfl | rfl
    · exact hEv hu
    · exact hEv hw
  have hsub : insert ({x, E} : Finset V) T ⊆ (move14 K h).edges := by
    refine insert_subset (edge_E_mem_move14 h hx) (fun e he' => ?_)
    rw [edges_move14]
    exact mem_union_left _ (hT he')
  have hτ' : ({u, v, w} : Finset V) ∈ (move14 K h).tris := by
    rw [tris_move14]; exact mem_union_left _ hτ
  have key := TreeExchange.mk (K := move14 K h) hsub huv hvw huw hτ'
    (mem_insert_of_mem he) (mem_insert_of_mem hg)
    (fun hm => (mem_insert.mp hm).elim (fun hh => hne' hh.symm) hf)
  have e : insert ({u, w} : Finset V) ((insert ({x, E} : Finset V) T).erase {u, v}) =
      insert {x, E} (insert {u, w} (T.erase {u, v})) := by
    rw [erase_insert_of_ne hne, Finset.insert_comm]
  rw [e] at key
  exact key

lemma lift_eqvGen (h : IsMove14 K A B C D E) {x : V} (hx : x ∈ ({A, B, C, D} : Finset V))
    {T T2 : Finset (Finset V)} (hs : Relation.EqvGen (TreeExchange K) T T2) :
    Relation.EqvGen (TreeExchange (move14 K h)) (insert {x, E} T) (insert {x, E} T2) := by
  induction hs with
  | rel _ _ hs => exact Relation.EqvGen.rel _ _ (lift_exchange h hx hs)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Two trees of the form "tree of `K` plus a leaf edge `xE`" are exchange-connected in
`move14 K`, whenever `K` is tree-connected. -/
lemma leafForm_eq (h : IsMove14 K A B C D E) (hK : TreeConnected K)
    {T0 T0' : Finset (Finset V)} (h0 : IsMaxTree K T0) (h0' : IsMaxTree K T0') {x x' : V}
    (hx : x ∈ ({A, B, C, D} : Finset V)) (hx' : x' ∈ ({A, B, C, D} : Finset V)) :
    Relation.EqvGen (TreeExchange (move14 K h)) (insert {x, E} T0) (insert {x', E} T0') := by
  by_cases hxx : x = x'
  · subst hxx
    exact lift_eqvGen h hx (hK h0 h0')
  · obtain ⟨T1, h1, hmem⟩ := exists_isMaxTree_mem h0 (edge_mem_of_mem_S h hx hx' hxx)
    have hEv := notMem_verts_of_isMove14 h
    have hE1 : ({x, E} : Finset V) ∉ T1 := fun hm =>
      hEv ((h1.2.edge _ hm).1 (by simp))
    have hE1' : ({x', E} : Finset V) ∉ T1 := fun hm =>
      hEv ((h1.2.edge _ hm).1 (by simp))
    have hxv := mem_verts_of_mem_S h hx
    have hxv' := mem_verts_of_mem_S h hx'
    have hsub : insert ({x, E} : Finset V) T1 ⊆ (move14 K h).edges := by
      refine insert_subset (edge_E_mem_move14 h hx) (fun e he' => ?_)
      rw [edges_move14]
      exact mem_union_left _ (h1.1 he')
    have htri : ({E, x, x'} : Finset V) ∈ (move14 K h).tris := by
      have := tri_E_mem_move14 h hx hx' hxx
      have e : ({E, x, x'} : Finset V) = {x, x', E} := by
        ext z; simp only [mem_insert, mem_singleton]; tauto
      rwa [e]
    have hf : ({E, x'} : Finset V) ∉ insert ({x, E} : Finset V) T1 := by
      intro hm
      rcases mem_insert.mp hm with hh | hh
      · rcases pair_eq_pair_iff'.mp hh with ⟨h1', -⟩ | ⟨-, h2'⟩
        · exact hEv (h1' ▸ hxv)
        · exact hxx h2'.symm
      · rw [pair_comm] at hh
        exact hE1' hh
    have hEx : E ≠ x := fun hh => hEv (by rw [hh]; exact hxv)
    have hEx' : E ≠ x' := fun hh => hEv (by rw [hh]; exact hxv')
    have key := TreeExchange.mk (K := move14 K h) hsub hEx hxx hEx' htri
      (by rw [pair_comm]; exact mem_insert_self _ _) (mem_insert_of_mem hmem) hf
    have e : insert ({E, x'} : Finset V) ((insert ({x, E} : Finset V) T1).erase {E, x}) =
        insert {x', E} T1 := by
      rw [pair_comm E x, erase_insert hE1, pair_comm E x']
    rw [e] at key
    exact Relation.EqvGen.trans _ _ _ (lift_eqvGen h hx (hK h0 h1))
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ key)
        (lift_eqvGen h hx' (hK h1 h0')))

lemma mem_S_of_edge_E (h : IsMove14 K A B C D E) {b : V} (he : ({b, E} : Finset V) ∈ (move14 K h).edges) :
    b ∈ ({A, B, C, D} : Finset V) := by
  obtain ⟨x, hx, hxe⟩ := edge_move14_of_mem h he (by simp)
  rcases pair_eq_pair_iff'.mp hxe with ⟨h1, -⟩ | ⟨-, h2⟩
  · rw [h1]; exact hx
  · exact absurd (by rw [h2]; exact mem_verts_of_mem_S h hx) (notMem_verts_of_isMove14 h)

/-- **Every maximal tree of `move14 K` is exchange-connected to a tree of `K` plus a leaf edge.** -/
lemma reduce_leaf (h : IsMove14 K A B C D E) :
    ∀ n : ℕ, ∀ T : Finset (Finset V), IsMaxTree (move14 K h) T →
      #(T.filter (fun e => E ∈ e)) = n →
      ∃ T0 x, IsMaxTree K T0 ∧ x ∈ ({A, B, C, D} : Finset V) ∧
        Relation.EqvGen (TreeExchange (move14 K h)) T (insert {x, E} T0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hT hn
  have hEv := notMem_verts_of_isMove14 h
  have hverts : (move14 K h).verts = insert E K.verts := verts_move14 K h
  have hEK' : E ∈ (move14 K h).verts := by rw [hverts]; exact mem_insert_self _ _
  have hAv : A ∈ K.verts := mem_verts_of_mem_S h (by simp)
  have hAK' : A ∈ (move14 K h).verts := by rw [hverts]; exact mem_insert_of_mem hAv
  obtain ⟨b, hbE⟩ : ∃ b, ({b, E} : Finset V) ∈ T := by
    rcases (hT.2.conn E hEK' A hAK').cases_head with hh | ⟨b, hb, -⟩
    · exact absurd (by rw [hh]; exact hAv) hEv
    · exact ⟨b, by rwa [pair_comm] at hb⟩
  have hbS := mem_S_of_edge_E h (hT.1 hbE)
  have hbv := mem_verts_of_mem_S h hbS
  have hEb : E ≠ b := fun hh => hEv (by rw [hh]; exact hbv)
  by_cases hother : ∃ y, ({y, E} : Finset V) ∈ T ∧ y ≠ b
  · obtain ⟨y, hyE, hyb⟩ := hother
    have hyS := mem_S_of_edge_E h (hT.1 hyE)
    have hyv := mem_verts_of_mem_S h hyS
    have hEy : E ≠ y := fun hh => hEv (by rw [hh]; exact hyv)
    have hbv' : b ∈ (move14 K h).verts := by rw [hverts]; exact mem_insert_of_mem hbv
    have hyv' : y ∈ (move14 K h).verts := by rw [hverts]; exact mem_insert_of_mem hyv
    have htri : ({b, E, y} : Finset V) ∈ (move14 K h).tris := by
      have := tri_E_mem_move14 h hbS hyS hyb.symm
      rw [pair_comm E y]; exact this
    have hg : ({E, y} : Finset V) ∈ T := by rw [pair_comm]; exact hyE
    have hf : ({b, y} : Finset V) ∉ T :=
      hT.2.not_mem_of_two hbv' hyv' hEK' hyb.symm hEb.symm hEy.symm hbE hyE
    have hex := TreeExchange.mk hT.1 hEb.symm hEy hyb.symm htri hbE hg hf
    have hT' := hT.exchange hEb.symm hEy hyb.symm htri hbE hg hf
    have hmem : ({b, E} : Finset V) ∈ T.filter (fun e => E ∈ e) :=
      mem_filter.mpr ⟨hbE, by simp⟩
    have hfil : (insert ({b, y} : Finset V) (T.erase {b, E})).filter (fun e => E ∈ e) =
        (T.filter (fun e => E ∈ e)).erase {b, E} := by
      have hc : ¬ (E ∈ ({b, y} : Finset V)) := by
        simp only [mem_insert, mem_singleton, not_or]
        exact ⟨hEb, hEy⟩
      rw [filter_insert]
      simp only [hc, ↓reduceIte]
      rw [filter_erase]
    have hlt : #((insert ({b, y} : Finset V) (T.erase {b, E})).filter (fun e => E ∈ e)) < n := by
      rw [hfil]
      exact lt_of_lt_of_eq (card_erase_lt_of_mem hmem) hn
    obtain ⟨T0, x, h0, hx, hrel⟩ := ih _ hlt _ hT' rfl
    exact ⟨T0, x, h0, hx, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hex) hrel⟩
  · push Not at hother
    have hspan : IsSpanningTree (insert E K.verts) T := by rw [← hverts]; exact hT.2
    have hT0 := hspan.erase_leaf hEv hbv hbE hother
    refine ⟨T.erase {b, E}, b, ⟨?_, hT0⟩, hbS, ?_⟩
    · intro e he
      apply edge_move14_of_notMem h (hT.1 (mem_of_mem_erase he))
      intro hEe
      obtain ⟨y, -, rfl⟩ := exists_other_of_card_two (hT.2.edge e (mem_of_mem_erase he)).2 hEe
      rw [hother y (mem_of_mem_erase he)] at he
      exact (mem_erase.mp he).1 rfl
    · rw [insert_erase hbE]
      exact Relation.EqvGen.refl _

/-- **The 1-4 move preserves tree-connectedness**: if any two maximal trees of `K` are connected by
triangle exchanges, so are any two maximal trees of `move14 K`. -/
theorem treeConnected_move14 (h : IsMove14 K A B C D E) (hK : TreeConnected K) :
    TreeConnected (move14 K h) := by
  intro T T' hT hT'
  obtain ⟨T0, x, h0, hx, hr⟩ := reduce_leaf h _ T hT rfl
  obtain ⟨T0', x', h0', hx', hr'⟩ := reduce_leaf h _ T' hT' rfl
  exact Relation.EqvGen.trans _ _ _ hr
    (Relation.EqvGen.trans _ _ _ (leafForm_eq h hK h0 h0' hx hx')
      (Relation.EqvGen.symm _ _ hr'))

/-- **Gauge-fixed amplitude after a 1-4 move**: if `K` is tree-connected, the gauge-fixed amplitude of
`move14 K` does not depend on the maximal tree, for every cut-off. -/
theorem amplitudeGF_move14_tree_eq (h : IsMove14 K A B C D E) (hK : TreeConnected K)
    {T T' : Finset (Finset V)} (hT : IsMaxTree (move14 K h) T) (hT' : IsMaxTree (move14 K h) T')
    (cut : Finset V → ℕ) : amplitudeGF (move14 K h) T cut = amplitudeGF (move14 K h) T' cut :=
  (treeConnected_move14 h hK).amplitudeGF_eq hT hT' cut

end Move14

/-- Complexes obtained from `K₀` by a finite sequence of 1-4 moves (stacking). Starting from the
boundary of the 4-simplex these are the stacked 3-spheres. -/
inductive Stacked (K₀ : Complex3 V) : Complex3 V → Prop
  | base : Stacked K₀ K₀
  | step {K : Complex3 V} {A B C D E : V} (hK : Stacked K₀ K) (h : IsMove14 K A B C D E) :
      Stacked K₀ (move14 K h)

/-- **Tree-connectedness propagates along chains of 1-4 moves.** -/
theorem treeConnected_of_stacked {K₀ K : Complex3 V} (h₀ : TreeConnected K₀)
    (hs : Stacked K₀ K) : TreeConnected K := by
  induction hs with
  | base => exact h₀
  | step _ h ih => exact treeConnected_move14 h ih

/-- **Tree independence on stacked complexes**: for every cut-off, the gauge-fixed amplitude of a
complex obtained by 1-4 moves from a tree-connected complex does not depend on the maximal tree. -/
theorem amplitudeGF_stacked_eq {K₀ K : Complex3 V} (h₀ : TreeConnected K₀) (hs : Stacked K₀ K)
    {T T' : Finset (Finset V)} (hT : IsMaxTree K T) (hT' : IsMaxTree K T')
    (cut : Finset V → ℕ) : amplitudeGF K T cut = amplitudeGF K T' cut :=
  (treeConnected_of_stacked h₀ hs).amplitudeGF_eq hT hT' cut

end Lightlike.PR
