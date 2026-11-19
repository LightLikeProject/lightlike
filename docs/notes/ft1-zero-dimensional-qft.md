# FT1 stage 3: Wick's theorem as a pairing sum, the quartic expansion and its Feynman graphs

Status of 19 November 2026, branches `pl/ft1-wick`, `pl/ft1-graphs`, `pl/ft1-wickpairs` (work in progress). Claim tags: MEASURED = checked in Lean or by
reading the cited location; PROXY / ASSUMPTION = stated as such.

## Source read

M. Borinsky, *Graphs in perturbation theory: Algebraic structure and asymptotics*, PhD thesis (2018),
arXiv:1807.02046v1, read with pdftotext on 19 November 2026 (printed page numbers):

* §2.1, Definitions 2.1.1-2.1.2 (graph = half-edges `H`, vertices `V`, `ν : H → V`, involution `ι` / edge set),
  p. 10; Definitions 2.1.6-2.1.7 (isomorphism = bijections of half-edges and vertices compatible with `ν`, `ι`;
  automorphism), p. 11.
* §2.3, unlabelled graphs as orbits under relabelling, and Proposition 2.3.1 (`|Orb G|/(m! k!) = 1/|Aut G|`, by the
  orbit-stabilizer theorem), p. 15.
* §3.1, the one-variable identity `∫ dx/√(2πħ) e^{-x²/(2aħ)} x^{2n} = √a (aħ)^n (2n - 1)!!` ("the
  zero-dimensional version of Wick's theorem") and Definition 3.1.1 (eq. (3.1.2)), p. 22; Proposition 3.1.1 (the
  formal integral as a sum over graphs weighted by `1/|Aut Γ|`), p. 23; the expansion (3.1.8), whose `ħ²`
  coefficient contains `35 λ₄² a⁴ / 384 = (1/128 + 1/16 + 1/48) λ₄² a⁴`, p. 24.

## Formal statements and how they compare (MEASURED unless tagged)

* `integral_pow_mul_gauss` (ZeroDim/Quartic.lean): `∫ x^{2n} e^{-x²/2} dx = √(2π) (2n - 1)!!`. This is the p. 22
  identity with `a = ħ = 1` (convention: the normalisation `1/√(2π)` is kept on the right).
* `quartic_expansion`: for `g ≥ 0`, `|∫ e^{-x²/2 - g x⁴/24} dx - √(2π) Σ_{m<M} (-g/24)^m (4m - 1)!!/m!| ≤
  √(2π) (g/24)^M (4M - 1)!!/M!`. Borinsky treats the integral formally (Def. 3.1.1) and does not state this analytic
  bound; it is the milestone's "done when" (the expansion of the integral). Comparison with a source for the
  analytic statement: pending.
* `sum_inv_aut` (ZeroDim/Graphs.lean): `Σ_Γ 1/|Aut Γ| = (4m - 1)!!/(24^m m!)` over the vacuum graphs with `m`
  four-valent vertices. Difference, kind representation: a graph is a fixed-point-free involution on the fixed
  corollas `Fin m × Fin 4` and the relabellings are the wreath product `S₄ ≀ S_m` acting by conjugation, instead of
  all labelled graphs under `S_{4m} × S_m` (Borinsky §2.3). An automorphism `(j_H, j_V)` is determined by `j_H`
  (every vertex has a half-edge), and `j_H` then preserves the corollas, so `Aut Γ` is the stabilizer in `S₄ ≀ S_m`.
  With `quartic_expansion` this is Prop. 3.1.1 for the quartic potential (`λ₄ = -g`, `a = 1`).
* `formalIntegral`, `formalIntegral_quartic_two` (ZeroDim/FormalIntegral.lean): Definition 3.1.1 with the
  coefficient of `ħ^k` written out after expanding `e^{V/ħ}`; terms with `m > 2k` vanish for `V ∈ x³ℝ[[x]]`
  (`coeff_pow_eq_zero`). Difference, kind representation: the defining sum is truncated at `m ≤ 2k`.
  The `ħ²` coefficient for `V = λ x⁴/4!`, `a = 1`, is `35 λ²/384` (= (3.1.8)); the wrong factor `1/24` for the
  sunset is shown to fail.
* `moment_eq_pairSum` (Gaussian/Wick.lean): the multivariate Gaussian moment is the sum over the full Wick
  contractions (Physlib's `WickContraction`, `IsFull`) of the products of covariances. Compared with L. Tubaro,
  M. Zanella, *An introduction to Malliavin calculus*, arXiv:2502.07941v1, Theorem 2.19 (Isserlis formula), p. 9
  (read 19 November 2026): `E[ξ₁ ⋯ ξₙ] = Σ ∏_k E[ξ_{i_k} ξ_{j_k}]` over the partitions of `{1, …, n}` into pairs, for
  centred jointly Gaussian `ξ`. Here `ξ_k = x_{l_k}` are coordinates of `N(0, S)`, so `E[ξ_i ξ_j] = S_{l_i l_j}`, and
  the partitions into pairs are the full Wick contractions. Difference, kind weaker: the covariance `S` is positive
  definite (the density is used), so a degenerate jointly Gaussian family is not covered. Attempt 1 to remove it:
  `moment_eq_pairSum_of_posSemidef` (Gaussian/WickSemidef.lean) for positive semidefinite `S`, through `√S`
  (Mathlib's definition of `multivariateGaussian`), multilinearity and the factorisation of the sum over index maps
  along the pairs (`sum_prod_delta`); status: written, compile pending.

## Reuse (check before you build)

Mathlib: `integral_comp_abs`, `integral_rpow_mul_exp_neg_mul_rpow`, `Real.Gamma_nat_add_half`,
`integral_exp_neg_mul_sq`, `Real.pow_div_factorial_le_exp`, the class formula
`MulAction.card_eq_sum_card_group_div_card_stabilizer`, `Equiv.prodShear`. Mathlib's `RegularWreathProduct` is the
regular wreath product (acting on `Λ × Q`), not `S₄ ≀ S_m` on `Fin m × Fin 4`, so it is not used. Physlib:
`WickContraction`, `IsFull`, `extractEquiv`, `insertAndContractNat`, and
`Physlib.Fin.involutionNoFixed_card_even` (the number `(n - 1)!!` of pairings). Physlib's Feynman diagrams are
TODO there. Tau Ceti: not checked.

## Open

* Trust checks in Lean: `sum_inv_aut_two` (the graphs with two vertices have total symmetry factor `35/384`) and
  `sum_inv_aut_one` (`1/8`, the figure-eight).
* The order-`g²` trust check identifies the three graphs by their symmetry factors only numerically
  (`1/128 + 1/16 + 1/48 = 35/384`); computing the three orbits and their stabilizers in Lean is open.
