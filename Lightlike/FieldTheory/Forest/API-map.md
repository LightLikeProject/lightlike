# Forest formulas

## Abstract (Alpha)

This API proves the Brydges–Kennedy Taylor forest formula of Abdesselam and Rivasseau (Theorem III.1, eq. (III.2)):
for a smooth function `H` from `ℝ^{P_n}` to a Banach space, `P_n` the links (unordered pairs of distinct points) of
`n` points, `H(1)` is the sum over the forests `F` of `∫_{I^F} (∏_{l ∈ F} ∂/∂x_l) H (X^F(h)) dh`, `I` the unit
interval, where `X^F(h)_l` is the infimum of the `h` along the path of `F` joining the ends of `l`, and `0` if there is
none. It also proves that the matrix with `1` on the diagonal and these entries off it is positive (Rivasseau–Wang,
Theorem II.1).

## Content (Alpha)

The links of `Fin n`, forests (sets of links with no cycle) and, for parameters `w` on the links of a set `F`, the
ultrametric `ultra F w a b`: the largest `w_l`, `l ∈ F`, such that `a` and `b` are joined by the links of `F` with
parameter at least `w_l`, and `0` if there is none. For a forest it is the infimum of `w` along the path joining `a`
to `b` (for `w ≥ 0`), the source's `h^F_{ab}` [1] {1}. Adding to a forest a link whose parameter is at most every
parameter of the forest keeps the ultrametric of the points already joined and gives that parameter to the points it
newly joins [1].

Partial derivatives of a smooth function commute, so `∏_{l ∈ F} ∂/∂x_l H` does not depend on an order of `F` [2].
On the unit cube `I^{P_n}` with Lebesgue measure, one coordinate integrates at a time, ties between coordinates have
measure zero, the cube splits by the coordinate of a finite set that is smallest, and restricting to the coordinates
of `F` carries the cube to `I^F` [3].

**The forest formula** (eq. (III.2)) holds for every smooth `H` from `ℝ^{P_n}` to a Banach space, with the integral
over `I^F` [4] {1}, and with the integral over the whole cube `I^{P_n}` of the same integrand, a function of
the `h_l`, `l ∈ F`, only [4]. The proof is the iterated Taylor interpolation of Gurau, Rivasseau and Sfondrini
(proof of Theorem 6.1) {3}, as an induction on the number of links: with all the entries between different clusters
of `F` equal to `s`, the fundamental theorem of calculus in `s` from `0` to the smallest parameter of `F` gives the
term of `F` and the forests with one more link, the new link being the one with the smallest parameter [4].

**The forest matrix is positive** (Rivasseau–Wang, Theorem II.1): for parameters at most `1` on `F`, the symmetric
matrix with `1` on the diagonal and the ultrametric of `F` off it is positive semidefinite, being the integral over
`t ∈ (0, 1]` of the block matrices of ones of the clusters of the links with parameter at least `t` [5] {2}.

**Missing.** The rooted forest formula (Theorem III.2, eq. (III.3)), the jungle formulas (Section IV) and the use of the
formula for the loop vertex expansion are not formalised here. The comparison with the sources is in
`docs/notes/g2-045-forest-formula.md`.

## Lean References

1. Lightlike/FieldTheory/Forest/Graph.lean - `FieldTheory.Forest.Link`, `FieldTheory.Forest.IsForest`,
   `FieldTheory.Forest.isForest_insert_iff`, `FieldTheory.Forest.ultra`, `FieldTheory.Forest.ultra_insert_of_joined`,
   `FieldTheory.Forest.ultra_insert_of_not_joined`, `FieldTheory.Forest.walkLinks`, `FieldTheory.Forest.ultra_eq_path_inf`
2. Lightlike/FieldTheory/Forest/Partial.lean - `FieldTheory.Forest.pd`, `FieldTheory.Forest.pd_comm`, `FieldTheory.Forest.pdF`,
   `FieldTheory.Forest.pdF_insert`
3. Lightlike/FieldTheory/Forest/Cube.lean - `FieldTheory.Forest.cube`, `FieldTheory.Forest.integral_cube_update`,
   `FieldTheory.Forest.cube_eq_null`, `FieldTheory.Forest.integral_eq_sum_argmin`,
   `FieldTheory.Forest.integral_indicator_argmin`, `FieldTheory.Forest.measurePreserving_restrictF`
4. Lightlike/FieldTheory/Forest/Formula.lean - `FieldTheory.Forest.forestPoint`, `FieldTheory.Forest.forestPoint_eq_path_inf`,
   `FieldTheory.Forest.forests`, `FieldTheory.Forest.stepTerm_eq`, `FieldTheory.Forest.interp_insert_update`,
   `FieldTheory.Forest.T_succ`, `FieldTheory.Forest.forest_formula`, `FieldTheory.Forest.forest_formula_restrict`
5. Lightlike/FieldTheory/Forest/Positivity.lean - `FieldTheory.Forest.le_ultra_iff`, `FieldTheory.Forest.sum_block_nonneg`,
   `FieldTheory.Forest.forestMatrix`, `FieldTheory.Forest.posSemidef_forestMatrix`

## References

1. A. Abdesselam, V. Rivasseau, Trees, forests and jungles: a botanical garden for cluster expansions,
   arXiv:hep-th/9409094, Theorem II.1 and the definition of `h^F_{ij}`, p. 3; Theorem III.1, eq. (III.2), p. 13.
2. V. Rivasseau, Z. Wang, Loop vertex expansion for Φ^{2k} theory in zero dimension, arXiv:1003.1037, Theorem II.1 and eqs. (II-2)-(II-4),
   pp. 2-3.
3. R. Gurau, V. Rivasseau, A. Sfondrini, Renormalization: an advanced overview, arXiv:1401.5003, Theorem 6.1,
   eq. (6.1), p. 107, and its proof, pp. 107-109.
