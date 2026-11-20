import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Task T-GF7-P8

Cayley's formula: there are n^{n-2} trees on n labelled vertices.

The statement is `Lightlike.FieldTheory.Forest.card_isTree`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. The Prüfer code: removing the least leaf and recording its neighbour, n - 2 times, is a
bijection from the trees on Fin n to Fin n^(n-2); or count rooted forests by induction (the number
of rooted forests on [n] with k given roots is k n^{n-k-1}).

## What the statement uses

The statement names no definition of Lightlike, only Mathlib and Physlib.

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.FieldTheory.Forest.card_isTree

## References

Milestone GF7 (Borel summability), ROADMAP section "Group field theory and tensor models".
Source: Laurent Freidel and David Louapre, Non-perturbative summation over 3D discrete topologies,
Phys.Rev. D68 (2003) 104004; Thibault Delepouve, Razvan Gurau and Vincent Rivasseau, Universality
and Borel Summability of Arbitrary Quartic Tensor Models, Annales de l'Institut Henri Poincaré -
Probabilités et Statistiques 2016, Vol. 52, No. 2, 821-848; D. Benedetti, R. Gurau, H. Keppler, D.
Lettera, The small-N series in the zero-dimensional O(N) model: constructive expansions and
transseries (2022), Theorem 1; V. Rivasseau, Z. Wang, Loop Vertex Expansion for Phi^2k Theory in
Zero Dimension (2010), Theorem IV.1; R. Gurau, V. Rivasseau, A. Sfondrini, Renormalization: an
advanced overview (2014), Section 2.1.2 (`freidel-louapre-2002`, `delepouve-gurau-rivasseau-2016`,
`benedetti-gurau-keppler-lettera-2022`, `rivasseau-wang-2010`, `gurau-rivasseau-sfondrini-2014` in
docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

namespace Lightlike.FieldTheory.Forest

open Classical in
/-- **Cayley's formula** (Gurau–Rivasseau–Sfondrini, arXiv:1401.5003, Section 2.1.2, p. 11: "There are `n^{n-2}`
distinct trees over `n` labelled vertices"; used for the convergence of the loop vertex expansion in Rivasseau–
Wang, arXiv:1003.1037, p. 11): the number of trees on the vertex set `Fin n`, `n ≥ 1`, is `n^{n-2}`.

For `n = 1` the exponent `n - 2` is `0` in `ℕ`, and the single vertex is the one tree. Non-vacuous: for `n = 3`
the three trees are the three paths. -/
theorem card_isTree (n : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.filter fun G : SimpleGraph (Fin n) => G.IsTree).card = n ^ (n - 2) := by
  sorry

end Lightlike.FieldTheory.Forest
