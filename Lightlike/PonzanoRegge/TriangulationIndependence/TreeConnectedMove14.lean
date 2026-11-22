module

public import Lightlike.PonzanoRegge.TriangulationIndependence.CompleteSkeleton
public import Lightlike.PonzanoRegge.TriangulationIndependence.TreeEdge
public import Lightlike.PonzanoRegge.Move14

/-!
# Tree-connectedness is preserved by the 1-4 move

Closed-manifold gauge-tree programme (Freidel–Louapre 2004, Section III), positive side.
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

end Move14

end Lightlike.PR
