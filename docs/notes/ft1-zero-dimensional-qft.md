# FT1 stage 3: Wick's theorem as a pairing sum, the quartic expansion and its Feynman graphs

Status of 19 November 2026 (work in progress). Claim tags: MEASURED = checked in Lean or by
reading the cited location; PROXY / ASSUMPTION = stated as such.

## Source read

M. Borinsky, *Graphs in perturbation theory: Algebraic structure and asymptotics*, PhD thesis (2018),
arXiv:1807.02046v1, read with pdftotext on 19 November 2026 (printed page numbers):

* §2.1, Definitions 2.1.1-2.1.2 (graph = half-edges `H`, vertices `V`, `ν : H → V`, involution `ι` / edge set),
  p. 10; Definitions 2.1.6-2.1.7 (isomorphism = bijections of half-edges and vertices compatible with `ν`, `ι`;
  automorphism), p. 11.
* §2.3, unlabelled graphs as orbits under relabelling, and Proposition 2.3.1 (`|Orb G|/(m! k!) = 1/|Aut G|`, by the
  orbit-stabilizer theorem), p. 15.
* §2.4.2, eqs. (2.4.5)-(2.4.6) (`X = Σ_Γ Γ/|Aut Γ|`, `X_c` the same over the connected graphs) and Theorem 2.4.1
  (the exponential formula `X = e^{X_c}`, `X_c = log X`, eq. (2.4.7), with its proof), pp. 17-18.
* Chapter 7, p. 117: `W(ħ, j) := ħ log Z(ħ, j)` generates the connected diagrams "as stated in Theorem 2.4.1".
* §3.1, the one-variable identity `∫ dx/√(2πħ) e^{-x²/(2aħ)} x^{2n} = √a (aħ)^n (2n - 1)!!` ("the
  zero-dimensional version of Wick's theorem") and Definition 3.1.1 (eq. (3.1.2)), p. 22; Proposition 3.1.1 (the
  formal integral as a sum over graphs weighted by `1/|Aut Γ|`), p. 23; the expansion (3.1.8), whose `ħ²`
  coefficient contains `35 λ₄² a⁴ / 384 = (1/128 + 1/16 + 1/48) λ₄² a⁴`, p. 24.

## Formal statements and how they compare (MEASURED unless tagged)

* `wick_one_variable` (ZeroDim/Quartic.lean): `∫ dx/√(2πħ) e^{-x²/(2aħ)} x^{2n} = √a (aħ)^n (2n - 1)!!` for
  `a, ħ > 0`, exactly the p. 22 identity (no difference); from `integral_pow_mul_gauss`
  (`∫ x^{2n} e^{-x²/2} dx = √(2π) (2n - 1)!!`) by the substitution `x = √(aħ) y` (`integral_pow_mul_gauss_scaled`).
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
  along the pairs (`sum_prod_delta`); status: compiled (MEASURED), which removes the difference. Remaining difference, kind
  representation: the family is given as the coordinates `x_{l_k}` of `multivariateGaussian 0 S`; every centred jointly
  Gaussian vector has this law with `S` its covariance (positive semidefinite).

* `vacuumSeries_eq_exp` (ZeroDim/Connected.lean): `Z = exp(W)` in `ℚ[[x]]`, where `Z = Σ a_n xⁿ/(24ⁿ n!)` and
  `W = Σ c_n xⁿ/(24ⁿ n!)`, `a_n`, `c_n` the numbers of pairings and of connected pairings of `n` four-valent
  vertices; `derivative_vacuumSeries`: `Z' = W' Z`. With `coeff_vacuumSeries` and `coeff_connectedSeries`
  (ZeroDim/ConnectedGraphs.lean: the coefficients are `Σ 1/|Aut Γ|` over all, resp. the connected, vacuum graphs
  with `n` vertices, by the class formula on the pairings, resp. the connected pairings, which are invariant under
  relabelling) this is `Σ_Γ x^{|V_Γ|}/|Aut Γ| = exp(Σ_{Γ connected} x^{|V_Γ|}/|Aut Γ|)`; `logOf_vacuumSeries`:
  `log Z = W` (Mathlib's `logOf`, through `subst_log_exp_sub_one`), so `coeff_logOf_vacuumSeries`: the coefficients
  of `log Z` are the sums of `1/|Aut Γ|` over the connected graphs. Compared with Borinsky,
  Theorem 2.4.1, eq. (2.4.7), p. 18 (`X = e^{X_c}`, `X_c = log X`, read 19 November 2026; proof: a graph with `n`
  components is a disjoint union of `n` connected graphs, and `1/n!` corrects the overcounting), and with p. 117
  (`W = ħ log Z` generates the connected diagrams "as stated in Theorem 2.4.1"). Difference, kind weaker: the
  theorem is an identity in Borinsky's algebra `G` of all graphs (any vertex degrees, legs), and p. 117 has a general
  potential and a source `j`; here only the four-valent vacuum graphs (quartic potential, `j = 0`), as an identity
  of power series counting a graph by its vertices (for these graphs the excess `|E| - |V|` equals `|V|`, so this is
  also the counting by `ħ`). Proof (MEASURED): every vertex lies in exactly one closed connected vertex set, its
  component (`existsUnique_component`: the closed set of least size through the vertex is connected, because the
  complement of a closed subset in a closed set is closed for an involution); the pairings in which `S` is the
  component of `v₀` are the pairs (connected pairing of `S`, pairing of `R \ S`) (`card_fiber`); the counts depend
  only on the number of vertices (`card_pairOn_map`, extension by the identity along an embedding); this gives
  `a_{n+1} = Σ_k C(n, k) c_{k+1} a_{n-k}` (`numPairings_succ`), which is `Z' = W' Z`, and `exp(W)` solves the same
  equation with the same constant term (`derivative_subst`, `derivative_exp`; uniqueness by induction on the
  coefficients, `eq_of_derivative_eq_mul`). Trust checks: `c₁ = 3`, `c₂ = 96`, so the connected graphs with two
  vertices have `Σ 1/|Aut Γ| = 1/12 = 1/16 + 1/48` and the disconnected one `35/384 - 1/12 = 1/128 = (1/8)²/2`
  (`sum_inv_aut_connected_two`). The weaker difference is lifted by the general statements recorded in
  `docs/notes/ft1-graph-algebra.md`: Theorem 2.4.1 in the algebra of all graphs (`expXc_eq_X`) and p. 117 for a general
  potential with a source (`gen_X_eq_formalZ`, `coeff_formalZ_eq_exp`).

## Reuse (check before you build)

Mathlib: `PowerSeries.exp`, `PowerSeries.subst`, `derivative_subst`, `derivative_exp`,
`constantCoeff_subst_of_constantCoeff_zero`, `Function.extend`, `Finset.sum_powerset_insert`,
`Finset.sum_powerset_apply_card`, `sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`, `Measure.integral_comp_mul_left`,
`integral_comp_abs`, `integral_rpow_mul_exp_neg_mul_rpow`, `Real.Gamma_nat_add_half`,
`integral_exp_neg_mul_sq`, `Real.pow_div_factorial_le_exp`, the class formula
`MulAction.card_eq_sum_card_group_div_card_stabilizer`, `Equiv.prodShear`. Mathlib's `RegularWreathProduct` is the
regular wreath product (acting on `Λ × Q`), not `S₄ ≀ S_m` on `Fin m × Fin 4`, so it is not used. Physlib:
`WickContraction`, `IsFull`, `extractEquiv`, `insertAndContractNat`, and
`Physlib.Fin.involutionNoFixed_card_even` (the number `(n - 1)!!` of pairings). Physlib's Feynman diagrams are
TODO there. Tau Ceti: not checked.

## Open

* G3-175: done, in the algebra of all graphs and with a source; route, sources and attempt record in
  `docs/notes/ft1-graph-algebra.md`.
* G2-037, the graph form (Polyak, arXiv:math/0406251v1, Proposition 2.17, p. 9, eq. (19)), done
  (`integral_homogPoly_pow_graphs`, `integral_polyPot_pow_graphs`): the sum over labelled contractions becomes a sum over Feynman graphs with `1/|Aut Γ|` by the class formula on the pairings of the legs
  under the vertex-preserving permutations (as for `sum_inv_aut`), for a symmetric coefficient tensor. Normalisation
  (MEASURED, by counting in Polyak's own example, §2.6, p. 7): with `U = Σ U_{ijk} x_i x_j x_k` as written in §2.6,
  the `ħ²` coefficient is `(1/2!) Σ_{15 pairings}`, and the Θ graph occurs 6 times, giving `6/2! = 3` times its label
  sum, while (19) gives `1/|Aut Θ| = 1/12`; the ratio is `(3!)² = 36`. So (19) holds for
  `U = Σ_k (1/k!) U_{i₁…i_k} x_{i₁} ⋯ x_{i_k}`, and a statement following (19) carries that convention, named as such.
* G2-037: the Feynman expansion of finite-dimensional (`ℝⁿ`) Gaussian integrals, done for a homogeneous and for a
  general polynomial potential (`integral_homogPoly_pow`, `integral_polyPot_pow`).

* Trust checks in Lean: `sum_inv_aut_two` (the graphs with two vertices have total symmetry factor `35/384`) and
  `sum_inv_aut_one` (`1/8`, the figure-eight).
* The order-`g²` trust check identifies the three graphs by their symmetry factors only numerically
  (`1/128 + 1/16 + 1/48 = 35/384`); computing the three orbits and their stabilizers in Lean is open.
