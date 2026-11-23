module

public import Lightlike.PonzanoRegge.TriangulationIndependence.TreeEdge

/-!
# `TreeConnected` fails when `H¹(K; ℤ/2)` of the 1-skeleton does not vanish on a cocycle

Lemma L8 of the closed-manifold gauge-tree programme (Freidel–Louapre 2004, Section III), combining
L4–L7: if `K` has a maximal tree and `ω` is a `ZMod 2` 1-cocycle of the 2-skeleton of `K` that is not a
coboundary on the edges of `K` (no potential `g` with `g x + g y = ω {x, y}` on every edge), then `K`
is not `TreeConnected`: triangle exchanges cannot connect all maximal trees.

No manifold hypothesis is used, so the statement applies to every closed combinatorial 3-manifold
`K` (`IsCombManifold`) with `H¹(K; ℤ/2) ≠ 0`. It shows that *exchange-connectedness* of the gauge
trees is the wrong route to tree independence on such manifolds; it does not show that the
amplitude depends on the tree.
-/

@[expose] public section

namespace Lightlike.PR

open Finset

variable {V : Type*} [DecidableEq V]

/-- **A non-exact cocycle prevents tree-connectedness.** -/
theorem not_treeConnected_of_not_coboundary {K : Complex3 V} {ω : Finset V → ZMod 2}
    (hω : Cocycle2 K ω) {T₀ : Finset (Finset V)} (h₀ : IsMaxTree K T₀)
    (hnc : ¬ ∃ g : V → ZMod 2, ∀ ⦃x y : V⦄, ({x, y} : Finset V) ∈ K.edges →
      g x + g y = ω {x, y}) : ¬ TreeConnected K := by
  obtain ⟨g, hg⟩ := h₀.2.exists_flat ω
  have : ∃ x y : V, ({x, y} : Finset V) ∈ K.edges ∧ g x + g y ≠ ω {x, y} := by
    by_contra hcon
    exact hnc ⟨g, fun x y hxy => by_contra fun hne => hcon ⟨x, y, hxy, hne⟩⟩
  obtain ⟨x, y, hxy, hne⟩ := this
  obtain ⟨T', hT', hmem⟩ := exists_isMaxTree_mem h₀ hxy
  exact not_treeConnected_of_cocycle hω h₀ hT' (fun a b hab => hg hab)
    (fun hfl => hne (hfl hmem))

/-- Contrapositive, reading `TreeConnected` as a source of exactness: on a tree-connected complex
with a maximal tree, every `ZMod 2` cocycle of the 2-skeleton is a coboundary on the edges. -/
theorem TreeConnected.exists_potential {K : Complex3 V} (h : TreeConnected K)
    {T₀ : Finset (Finset V)} (h₀ : IsMaxTree K T₀) {ω : Finset V → ZMod 2}
    (hω : Cocycle2 K ω) :
    ∃ g : V → ZMod 2, ∀ ⦃x y : V⦄, ({x, y} : Finset V) ∈ K.edges → g x + g y = ω {x, y} := by
  by_contra hnc
  exact not_treeConnected_of_not_coboundary hω h₀ hnc h

end Lightlike.PR
