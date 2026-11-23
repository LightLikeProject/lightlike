module

public import Lightlike.PonzanoRegge.TriangulationIndependence.TreeFlat

/-!
# Every edge of `K` lies in a maximal tree

Lemma L6 of the closed-manifold gauge-tree programme (Freidel–Louapre 2004, Section III): if `K` has
a maximal tree (that is, its 1-skeleton is connected), then every edge of `K` lies in some maximal
tree (`exists_isMaxTree_mem`). The proof extends the one-edge graph, which is acyclic, to a spanning
tree with Mathlib's `Connected.exists_isTree_le_of_le_of_isAcyclic`, and converts the Mathlib tree
back to a `IsSpanningTree` (`IsTree.isSpanningTree`), the converse of `IsSpanningTree.isTree`.
-/

@[expose] public section

namespace Lightlike.PR

open Finset

variable {V : Type*} [DecidableEq V]

lemma isAcyclic_fromEdgeSet_singleton {W : Type*} (a b : W) :
    (SimpleGraph.fromEdgeSet {s(a, b)}).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_isBridge]
  intro e he
  induction e using Sym2.ind with | h u v => ?_
  rw [SimpleGraph.mem_edgeSet] at he
  rw [SimpleGraph.isBridge_iff]
  intro hr
  obtain ⟨p⟩ := hr
  cases p with
  | nil => exact he.ne rfl
  | cons h _ =>
    have he' := he
    rw [SimpleGraph.fromEdgeSet_adj] at he'
    rw [SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj] at h
    obtain ⟨⟨h1, _⟩, h2⟩ := h
    exact h2 (Set.mem_singleton_iff.mpr
      ((Set.mem_singleton_iff.mp h1).trans (Set.mem_singleton_iff.mp he'.1).symm))

lemma treeGraph_adj (W : Finset V) (T : Finset (Finset V)) (a b : W) :
    (treeGraph W T).Adj a b ↔ a ≠ b ∧ (({a.1, b.1} : Finset V) ∈ T ∨ ({b.1, a.1} : Finset V) ∈ T) :=
  SimpleGraph.fromRel_adj _ _ _

lemma pairOf_injective (W : Finset V) : Function.Injective (pairOf W) := by
  intro e e'
  induction e using Sym2.ind with | h a b => ?_
  induction e' using Sym2.ind with | h c d => ?_
  intro h
  rw [pairOf_mk, pairOf_mk] at h
  rcases pair_eq_pair_iff'.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [Subtype.ext h1, Subtype.ext h2]
  · rw [Subtype.ext h1, Subtype.ext h2, Sym2.eq_swap]

/-- **A tree in Mathlib's sense is a spanning tree in the sense of `IsSpanningTree`**: the converse
of `IsSpanningTree.isTree`, for trees on the subtype `W` (restricted to the edge set of `T`'s
pairs). -/
theorem IsTree.isSpanningTree (W : Finset V) {F : SimpleGraph W} (hF : F.IsTree) :
    IsSpanningTree W (by classical exact F.edgeFinset.image (pairOf W)) := by
  classical
  have memT : ∀ e, e ∈ F.edgeFinset.image (pairOf W) ↔
      ∃ a b : W, F.Adj a b ∧ e = {a.1, b.1} := by
    intro e
    simp only [Finset.mem_image, SimpleGraph.mem_edgeFinset]
    constructor
    · rintro ⟨s, hs, rfl⟩
      induction s using Sym2.ind with | h a b => ?_
      exact ⟨a, b, hs, rfl⟩
    · rintro ⟨a, b, hab, rfl⟩
      exact ⟨s(a, b), hab, rfl⟩
  refine ⟨fun e he => ?_, fun x hx y hy => ?_, ?_⟩
  · obtain ⟨a, b, hab, rfl⟩ := (memT e).mp he
    refine ⟨?_, card_pair (fun h => hab.ne (Subtype.ext h))⟩
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact a.2
    · exact b.2
  · have hr : F.Reachable ⟨x, hx⟩ ⟨y, hy⟩ := hF.connected.preconnected _ _
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    exact Relation.ReflTransGen.lift (Subtype.val : W → V)
      (r := F.Adj) (p := fun x y => ({x, y} : Finset V) ∈ F.edgeFinset.image (pairOf W))
      (fun a b hab => (memT _).mpr ⟨a, b, hab, rfl⟩) _ _ hr
  · rw [Finset.card_image_of_injective _ (pairOf_injective W)]
    have := hF.card_edgeFinset
    rw [Fintype.card_coe] at this
    exact this

/-- **Every edge of `K` lies in a maximal tree**, as soon as `K` has one. -/
theorem exists_isMaxTree_mem {K : Complex3 V} {T₀ : Finset (Finset V)} (h₀ : IsMaxTree K T₀)
    {e : Finset V} (he : e ∈ K.edges) : ∃ T, IsMaxTree K T ∧ e ∈ T := by
  classical
  obtain ⟨t, ht, het, he2⟩ := Complex3.mem_edges.mp he
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp he2
  have hx : x ∈ K.verts := Complex3.mem_verts.mpr ⟨t, ht, het (by simp)⟩
  have hy : y ∈ K.verts := Complex3.mem_verts.mpr ⟨t, ht, het (by simp)⟩
  have hle : treeGraph K.verts T₀ ≤ treeGraph K.verts K.edges := by
    intro a b hab
    rw [treeGraph_adj] at hab ⊢
    exact ⟨hab.1, hab.2.imp (fun h => h₀.1 h) (fun h => h₀.1 h)⟩
  have hconn : (treeGraph K.verts K.edges).Connected := h₀.2.isTree.connected.mono hle
  have hH : SimpleGraph.fromEdgeSet {s((⟨x, hx⟩ : K.verts), (⟨y, hy⟩ : K.verts))} ≤
      treeGraph K.verts K.edges := by
    intro a b hab
    rw [SimpleGraph.fromEdgeSet_adj] at hab
    obtain ⟨hs, hne⟩ := hab
    rw [treeGraph_adj]
    refine ⟨hne, ?_⟩
    rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hs) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h1, h2]; exact he
    · right; rw [h1, h2]; exact he
  obtain ⟨F, hHF, hFG, hF⟩ :=
    hconn.exists_isTree_le_of_le_of_isAcyclic hH (isAcyclic_fromEdgeSet_singleton _ _)
  refine ⟨_, ⟨?_, IsTree.isSpanningTree K.verts hF⟩, ?_⟩
  · intro e he'
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp he'
    induction s using Sym2.ind with | h a b => ?_
    have hab : (treeGraph K.verts K.edges).Adj a b := hFG (SimpleGraph.mem_edgeFinset.mp hs)
    rw [treeGraph_adj] at hab
    rw [pairOf_mk]
    rcases hab.2 with h | h
    · exact h
    · rw [pair_comm]; exact h
  · refine Finset.mem_image.mpr ⟨s((⟨x, hx⟩ : K.verts), (⟨y, hy⟩ : K.verts)), ?_, rfl⟩
    rw [SimpleGraph.mem_edgeFinset]
    exact hHF (by
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨Set.mem_singleton _, fun h => hxy (congrArg Subtype.val h)⟩)

end Lightlike.PR
