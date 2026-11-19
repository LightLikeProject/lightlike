# The Taylor forest formula and the positivity of the forest matrix

Lean: `Lightlike/FieldTheory/Forest/` (API map in that folder).

## Sources read

- A. Abdesselam, V. Rivasseau, *Trees, forests and jungles: a botanical garden for cluster expansions*,
  arXiv:hep-th/9409094: Theorem II.1 (eq. (II.1)) and the definition of `h^F_{ij}(h)` as the infimum of the `h_l`
  over the unique path of `F` from `i` to `j`, `0` if there is none, p. 3; Theorem III.1 (the Brydges–Kennedy
  Taylor forest formula), eq. (III.2), p. 13, for `H` in the space `S` of smooth functions from `ℝ^{P_n}` to an
  arbitrary Banach space `V`, with `X^F_BK(h)` the vector `(x_l)` with `x_l = h^F_l(h)`, and its proof, pp. 13-14.
- R. Gurau, V. Rivasseau, A. Sfondrini, *Renormalization: an advanced overview*, arXiv:1401.5003: Theorem 6.1
  (the forest formula), eq. (6.1), p. 107, with `X^F_ii = 1` and `X^F_ij(w_F)` the infimum of the `w_l` on the path
  of `F` from `i` to `j`, `0` if there is none; its proof by iterated Taylor interpolation, pp. 107-109.
- V. Rivasseau, Z. Wang, *Loop vertex expansion for Φ^{2k} theory in zero dimension*, arXiv:1003.1037: Theorem II.1, eq. (II-1), p. 2, with the
  statement that the symmetric matrix `X^F` (`X_ii = 1`, `X_ij = x^F_ij`) is positive, and the reason given: for any
  ordering of the parameters it is a convex combination (II-4) of block matrices of ones (Definition II.1, (II-2)),
  pp. 2-3.

## Statement against the source

`forest_formula_restrict` is eq. (III.2): for `H : ℝ^{P_n} → V` smooth (`ContDiff ℝ ∞`), `V` a real Banach space,
`H(1) = ∑_{F forest} ∫_{[0,1]^F} (∏_{l ∈ F} ∂/∂x_l) H (X^F(h)) dh`. `forest_formula` is the same with the integral
over the whole cube `[0,1]^{P_n}`, the integrand depending only on the `h_l`, `l ∈ F`.
`posSemidef_forestMatrix` is the positivity in Rivasseau–Wang's Theorem II.1, for parameters `w_l ≤ 1` on `F`.

Differences, by kind:

- representation: the points `1, …, n` are `Fin n`, and `P_n` is `Link n`, the unordered pairs `s(a, b)` with
  `a ≠ b`.
- representation: `X^F(h)_l = h^F_l(h)` is defined by the ultrametric of `F` (`ultra`): the largest `h_m`, `m ∈ F`,
  such that the ends of `l` are joined by the links of `F` with parameter at least `h_m`, and `0` if there is none.
  For `h ≥ 0`, in particular on `[0,1]^F`, it is the infimum of the `h` along the path of `F` joining the ends of `l`,
  and `0` if there is no path (`forestPoint_eq_path_inf`, `forestPoint_of_not_linked`), the source's definition.
- representation: `∫_{[0,1]^F} ∏_{l ∈ F} dh_l` is the integral over `F → ℝ` for the product of the uniform measures
  on `[0, 1]`; `h` is extended by `0` off `F` to a point of `ℝ^{P_n}`, which does not change `X^F(h)`
  (`forestPoint_congr`).
- representation: `∏_{l ∈ F} ∂/∂x_l` is the iterated partial derivative `pdF`, the Fréchet derivative along the
  coordinate vectors, independent of the order (`pdF_insert`, from `pd_comm`).
- representation: "positive" is Mathlib's `Matrix.PosSemidef` (symmetric with `xᵀ X x ≥ 0` for all `x`). The matrix
  can be singular (one link with parameter `1` gives the block `[[1, 1], [1, 1]]`), so the source's "positive" is
  positive semidefinite.

Not differences: the positivity holds for any finite set of links `F` (not only forests) and needs only `w_l ≤ 1` on
`F`, which contains the source's case `w ∈ [0,1]^F`.

## Proof

Abdesselam and Rivasseau derive (III.2) from the algebraic forest formula (II.1) applied to polynomials and the
density of polynomials in `S` (pp. 13-14). The proof here is instead the direct Taylor interpolation of Gurau,
Rivasseau and Sfondrini (pp. 107-109), written as an induction on the number of links without orderings. For a
forest `F` let `Y^F(w, s)` have the entries `X^F(w)` on the links whose ends `F` joins and `s` on the others, and
`T_k = ∑_{|F| = k} ∫ (∂^F H)(Y^F(w, min_F w)) dw`. The fundamental theorem of calculus in `s` from `0` to `min_F w`
gives `T_k = ∑_{|F| = k} ∫ (∂^F H)(X^F(w)) dw + T_{k+1}` (`T_succ`): the derivative in `s` is the sum over the links
`e` between different clusters of `F`, and for `0 ≤ s ≤ min_F w`, `Y^F(w, s) = Y^{F ∪ e}(w', min_{F ∪ e} w')` with
`w' = w` except `w'_e = s` (`interp_insert_update`), so the term of `e` is the part of the cube where `e` has the
smallest parameter of `F ∪ e`; ties have measure zero (`cube_eq_null`), so the parts add up to `T_{k+1}`
(`integral_eq_sum_argmin`). `T_0 = H(1)` and `T_k = 0` for `k` larger than the number of links.

The positivity uses the integral form of (II-4): for `t ∈ (0, 1]`, `t ≤ X^F_ij` exactly when `i` and `j` are joined
by the links with `w ≥ t` (`le_ultra_iff`), so `X^F_ij = ∫_0^1 B_t(i, j) dt` with `B_t` the block matrix of ones of
those clusters, and `∑_ij x_i B_t(i, j) x_j = ∑_C (∑_{i ∈ C} x_i)² ≥ 0` (`sum_block_nonneg`).
