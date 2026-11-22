module

public import Lightlike.PonzanoRegge.GaugeChange

/-!
# Tree independence on complexes whose maximal trees are exchange-connected

Part of the closed-manifold gauge-tree question (Freidel–Louapre 2004, Section III). The exact
result available is `amplitudeGF_eqvGen_exchange`: gauge sets connected by triangle exchanges give
the same amplitude. This file packages it as a property of the complex:

* `TreeConnected K`: any two maximal trees of `K` are connected by a chain of triangle exchanges.
* `TreeConnected.amplitudeGF_eq`: on such a `K`, the gauge-fixed amplitude is independent of the
  maximal tree, for every cut-off.
* `not_treeConnected_of_dependent`: a complex with two maximal trees of different amplitude is not
  `TreeConnected`; this is how the ring of three tetrahedra fits (see
  `Lightlike/PonzanoRegge/TriangulationIndependence/Tests/TreeConnected.lean`).

What is open: that every closed combinatorial 3-manifold is `TreeConnected`. Exchanges only add
triangle boundaries to the cycles that the non-tree edges close in the tree, so two maximal trees
are exchange-connected exactly when they differ by a change that is trivial in the fundamental
group of the 2-skeleton; whether this is automatic for a closed manifold (as a graph-theoretic
statement, with no Pachner moves) is not proved here, and no counterexample is known.
-/

@[expose] public section

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- Any two maximal trees of `K` are connected by a chain of triangle exchanges. -/
def TreeConnected (K : Complex3 V) : Prop :=
  ∀ ⦃T T' : Finset (Finset V)⦄, IsMaxTree K T → IsMaxTree K T' →
    Relation.EqvGen (TreeExchange K) T T'

/-- **Tree independence on a tree-connected complex**: for every cut-off, any two maximal trees give
the same gauge-fixed amplitude. -/
theorem TreeConnected.amplitudeGF_eq {K : Complex3 V} (h : TreeConnected K)
    {T T' : Finset (Finset V)} (hT : IsMaxTree K T) (hT' : IsMaxTree K T')
    (cut : Finset V → ℕ) : amplitudeGF K T cut = amplitudeGF K T' cut :=
  amplitudeGF_eqvGen_exchange K (h hT hT') cut

/-- A complex with two maximal trees and a cut-off for which the amplitudes differ is not
`TreeConnected`. -/
theorem not_treeConnected_of_dependent {K : Complex3 V} {T T' : Finset (Finset V)}
    (hT : IsMaxTree K T) (hT' : IsMaxTree K T') (cut : Finset V → ℕ)
    (hne : amplitudeGF K T cut ≠ amplitudeGF K T' cut) : ¬ TreeConnected K :=
  fun h => hne (h.amplitudeGF_eq hT hT' cut)

end Lightlike.PR
