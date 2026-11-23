module

public import Lightlike.PonzanoRegge.TriangulationIndependence.Cocycle

/-!
# Every maximal tree is flat for some potential

Lemma L7 of the closed-manifold gauge-tree programme (Freidel–Louapre 2004, Section III): for a
spanning tree `T` of `W` and any `ZMod 2`-valued function `ω` on pairs, there is a potential
`g : V → ZMod 2` with `g x + g y = ω {x, y}` on every edge `{x, y} ∈ T`
(`IsSpanningTree.exists_flat`). The potential is the sum of `ω` along the unique tree path from a
fixed root.
-/

@[expose] public section

namespace Lightlike.PR

open Finset

variable {V : Type*} [DecidableEq V]

/-- The sum of `ω` over the edges of a walk in a graph on `W`. -/
def walkWt (ω : Finset V → ZMod 2) {W : Finset V} {G : SimpleGraph W} :
    ∀ {a b : W}, G.Walk a b → ZMod 2
  | _, _, .nil => 0
  | a, _, .cons (v := c) _ p => ω {a.1, c.1} + walkWt ω p

lemma walkWt_append (ω : Finset V → ZMod 2) {W : Finset V} {G : SimpleGraph W} {a b c : W}
    (p : G.Walk a b) (q : G.Walk b c) :
    walkWt ω (p.append q) = walkWt ω p + walkWt ω q := by
  induction p with
  | nil => simp [walkWt]
  | cons h p ih => simp [walkWt, ih, add_assoc]

lemma walkWt_single (ω : Finset V → ZMod 2) {W : Finset V} {G : SimpleGraph W} {a b : W}
    (h : G.Adj a b) : walkWt ω (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil) = ω {a.1, b.1} := by
  simp [walkWt]

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

/-- **Every spanning tree is flat for some potential**: for any `ω` there is `g` with
`g x + g y = ω {x, y}` on all edges of the tree. -/
theorem IsSpanningTree.exists_flat {W : Finset V} {T : Finset (Finset V)}
    (hT : IsSpanningTree W T) (ω : Finset V → ZMod 2) :
    ∃ g : V → ZMod 2, ∀ ⦃x y : V⦄, ({x, y} : Finset V) ∈ T → g x + g y = ω {x, y} := by
  classical
  have htree := hT.isTree
  obtain ⟨r⟩ : Nonempty W := htree.1.nonempty
  choose P hP hPu using fun w => htree.existsUnique_path r w
  have key : ∀ a b : W, (treeGraph W T).Adj a b →
      walkWt ω (P a) + walkWt ω (P b) = ω {a.1, b.1} := by
    intro a b hadj
    by_cases hb : b ∈ (P a).support
    · have h1 : (P a).takeUntil b hb = P b := hPu b _ ((hP a).takeUntil hb)
      have h2 : (P a).dropUntil b hb = SimpleGraph.Walk.cons hadj.symm SimpleGraph.Walk.nil :=
        (htree.existsUnique_path b a).unique ((hP a).dropUntil hb)
          (by simpa [SimpleGraph.Walk.cons_isPath_iff] using hadj.ne.symm)
      have h3 := congrArg (walkWt ω) (SimpleGraph.Walk.take_spec (P a) hb)
      rw [walkWt_append, h1, h2, walkWt_single, pair_comm] at h3
      rw [← h3]
      have := zmod2_add_self (walkWt ω (P b))
      linear_combination this
    · have hpath : ((P a).concat hadj).IsPath := (hP a).concat hb hadj
      have h1 : (P a).concat hadj = P b := hPu b _ hpath
      have h3 := congrArg (walkWt ω) h1
      rw [SimpleGraph.Walk.concat_eq_append, walkWt_append, walkWt_single] at h3
      rw [← h3]
      have := zmod2_add_self (walkWt ω (P a))
      linear_combination this
  refine ⟨fun v => if h : v ∈ W then walkWt ω (P ⟨v, h⟩) else 0, fun x y hxy => ?_⟩
  have hx : x ∈ W := (hT.edge _ hxy).1 (by simp)
  have hy : y ∈ W := (hT.edge _ hxy).1 (by simp)
  have hne : x ≠ y := fun h => by
    have := (hT.edge _ hxy).2; subst h; simp at this
  have hadj : (treeGraph W T).Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
    rw [treeGraph, SimpleGraph.fromRel_adj]
    exact ⟨fun h => hne (congrArg Subtype.val h), Or.inl hxy⟩
  simp only [hx, hy, dite_true]
  exact key _ _ hadj

end Lightlike.PR
