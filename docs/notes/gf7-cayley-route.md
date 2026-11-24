# GF7, T-GF7-P8: a route to Cayley's formula (`Lightlike.FieldTheory.Forest.card_isTree`)

1. Statement: the number of `G : SimpleGraph (Fin n)` with `G.IsTree` is `n^(n-2)` for `n ≥ 1`. Mathlib has no tree counting (checked at the pinned version, 24 Nov 2026), only the leaf API: `IsTree.exists_vert_degree_one_of_nontrivial`, `Connected.induce_compl_singleton_of_degree_eq_one`, `IsTree.card_edgeFinset`.
2. Route (degree-sequence form): the number of trees on `Fin n` with degrees `d` (`Σ d_i = 2n - 2`, every `d_i ≥ 1`) is `(n-2)! / ∏ (d_i - 1)!`; the multinomial theorem then sums it to `n^(n-2)`.
3. Induction step: pick a vertex `i` with `d_i = 1` (a leaf exists for `n ≥ 2`). Trees with that leaf correspond to pairs (neighbour `j ≠ i`, tree on the other `n - 1` vertices with `d_j` lowered by 1); this is the leaf-removal bijection, the one real lemma.
4. The cost is the relabelling: every step passes between `Fin n` and the subtype `{v // v ≠ i}`, and the count must be stated for any finite vertex type (cardinality only), not for `Fin n`.
5. Alternatives: the Prüfer code (a bijection trees ↔ `Fin n → Fin n` of length `n - 2`, same relabelling cost, no degree bookkeeping) or rooted forests (`k n^{n-k-1}` forests with `k` given roots, induction on `n`).
6. Estimate: 600 to 1200 lines (not measured). Nothing in the quartic Borel result (`quarticZ_borel_summable`) uses it; it serves the loop-vertex-expansion route to GF7, which is not in the library. Parked as a hard Lean row.
