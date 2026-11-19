# Field theory in finite dimensions

## Abstract (Alpha)

This API treats Gaussian integrals on `ℝⁿ`, the starting point of zero-dimensional field theory. It proves that the standard Gaussian measure is Lebesgue measure with the standard density, that the centred multivariate Gaussian measure with covariance `S` has the density `exp(-(1/2) xᵀ S⁻¹ x)` with its normalisation, and the Gaussian integral `∫ exp(-(1/2) xᵀ A x) dx = (√(2π))ⁿ / √(det A)` for positive definite `A`. The centred multivariate Gaussian measure is shown to be Lebesgue measure with that density, Gaussian integration by parts is proved, and with it Isserlis' recursion for the moments: the moment of a list of coordinates is a sum over the positions paired with the first one, so odd moments vanish, the two-point function is the covariance and the four-point function is the sum over three pairings. Wick's theorem as an explicit sum over all pairings, and Feynman graphs, are open.

## Content (Alpha)

Mathlib defines the multivariate Gaussian measure by its covariance, as the image of the standard Gaussian measure under the matrix square root of the covariance {1}. Mathlib has no density for it and no moment theorem. Here the standard Gaussian measure on `ℝⁿ` is shown to be the product of the one-dimensional densities with respect to Lebesgue measure [1] {1}. A change of variables by an invertible matrix gives the factor `|det R|⁻¹` [2]. With the square root `R` of `S` one has `R S⁻¹ R = 1`, hence `(R y)ᵀ S⁻¹ (R y) = yᵀ y`, and the centred Gaussian measure with covariance `S` integrates a function `f` as `(√(2π))⁻ⁿ (det S)^{-1/2} ∫ exp(-(1/2) xᵀ S⁻¹ x) f(x) dx` [2] {1}. Taking `f = 1` and `S = A⁻¹` gives the Gaussian integral of a positive definite `A` [2]. The measure is Lebesgue measure with density `normConst S · weight S⁻¹` [3]. The weight `exp(-(1/2) xᵀ A x)` has line derivative `-(A x)ⱼ` times itself along the coordinate direction `eⱼ`, and Mathlib's integration by parts for line derivatives gives `∫ w ∂ⱼg = ∫ (A x)ⱼ w g` [4]. For the monomial of a list of coordinates the derivative along `eⱼ` is the sum over the positions carrying the index `j` of the monomial without that position [5]. All monomials are integrable for the Gaussian measure, because a Gaussian measure has finite moments of every order {1}, and Isserlis' recursion `E[x_i x_{l₀} ⋯ x_{lₙ}] = ∑ₘ S_{i,lₘ} E[∏_{k≠m} x_{lₖ}]` follows from the integration by parts and `S S⁻¹ = 1` [6]. It gives that odd moments vanish, `E[x_i x_j] = S_{ij}` and `E[x_i x_j x_k x_l] = S_{ij}S_{kl} + S_{ik}S_{jl} + S_{il}S_{jk}` [6]. Checks: the two-point function agrees with Mathlib's covariance of the multivariate Gaussian, the four-point function with one variable of variance `1` is `3`, and for `A = 1` the value is `(2π)^{n/2}`, which agrees with Mathlib's separate computation of `∫ exp(-b ‖x‖²)`, and the integrals for `A = 1` and `A = 2` in one variable differ, so the determinant is needed.

Borinsky's formal integral, the zero-dimensional field theory as a formal power series in `ħ`, has the coefficient `35λ²/384` at order `ħ²` for the quartic potential `λx⁴/4!`, the sum `1/128 + 1/16 + 1/48` of the symmetry factors of the three vacuum graphs; a wrong factor for the sunset graph is shown to fail [7] {2}.

The vacuum graphs with `m` four-valent vertices are the orbits of the pairings of their half-edges under the permutations that keep the vertices (the wreath product `S₄ ≀ S_m`, of order `24^m m!`), the symmetry factor of a graph is the inverse of the order of its stabilizer, its automorphism group, and the symmetry factors sum to `(4m - 1)!!/(24^m m!)`, by the class formula [8] {2}; for two vertices the sum is `35/384` and for one vertex `1/8`.

Wick's theorem: the moment `E[x_{l₀} ⋯ x_{l_{n-1}}]` of the centred Gaussian measure with positive definite covariance `S` is the sum, over the full Wick contractions of the `n` positions (Physlib's `WickContraction` with `IsFull`), of the products `∏ S_{l_p l_q}` over the contracted pairs; both sides satisfy Isserlis' recursion [9] {3}. The same holds for every positive semidefinite covariance, through the square root `√S` of Mathlib's definition of the Gaussian measure, multilinearity, and the factorisation of the sum over index maps along the pairs [11] {3}.

The one-variable Wick identity `∫ dx/√(2πħ) e^{-x²/(2aħ)} x^{2n} = √a (aħ)^n (2n - 1)!!` holds for `a, ħ > 0`, and the series `√(2π) Σ_{m<M} (-g/24)^m (4m - 1)!!/m!` approximates `∫ e^{-x²/2 - g x⁴/24} dx` for `g ≥ 0` with an error at most the size of the next term, by the alternating Taylor bound for `e^{-t}` [10] {2}.

Graphs with legs on a half-edge type `π : H → V` are the involutions of `H` (edges are 2-cycles, legs are fixed points); every vertex lies in exactly one closed connected vertex set, and splitting off the component of a vertex gives `#graphs(R) = Σ_{v₀ ∈ S ⊆ R} #connected(S) · #graphs(R \ S)` [12] {2}.

A labelled graph with half-edges `Fin n` and vertices `Fin k` is an attachment map with an involution of the half-edges; the pairs of bijections `S_n × S_k` act by relabelling, isomorphic graphs are the same orbit and the automorphisms are the stabilizer, so `1/|Aut Γ| = |orbit Γ|/(n! k!)` [13] {2}.

The disjoint union of labelled graphs is compatible with relabelling, so it is defined on isomorphism classes; the formal sums of classes of all sizes carry the disjoint-union product (finite in each grade of half-edges and vertices), and `X = Σ_Γ Γ/|Aut Γ|`, its connected part `X_c` and `e^{X_c}` are defined there [14] {2}.

**The exponential formula `X = e^{X_c}`** holds coefficientwise in the algebra of all graphs (any vertex degrees, legs allowed) {2}: the components of a labelled graph are its closed connected vertex sets and their number is a class invariant [15]; cutting a graph at a component and gluing it back is a bijection with the pairs (connected graph, rest) [16]; double counting the pairs (graph, component) gives `X_c^m(c) = [c has m components] · m! · #labelled copies/(n! k!)`, and so `e^{X_c} = X` [17].

**Missing.** The error bound of the quartic expansion is not stated in Borinsky, who treats the integral formally. The formal integral is compared with Borinsky's Definition 3.1.1 and eq. (3.1.8) {2}, the graphs with Borinsky §2.1 and §2.3 {2}, and Wick's theorem with Tubaro–Zanella's Theorem 2.19 {3}; the Gaussian measure and its integrals are not yet compared with a source.

## Lean References

1. Lightlike/FieldTheory/Gaussian/Density.lean - `FieldTheory.pi_gaussianReal_eq_withDensity`, `FieldTheory.integral_stdGaussian`
2. Lightlike/FieldTheory/Gaussian/Integral.lean - `FieldTheory.integral_comp_toEuclideanLin`, `FieldTheory.integral_multivariateGaussian`, `FieldTheory.integral_exp_neg_half_quad`
3. Lightlike/FieldTheory/Gaussian/Measure.lean - `FieldTheory.multivariateGaussian_eq_withDensity`, `FieldTheory.integrable_weight_mul`
4. Lightlike/FieldTheory/Gaussian/Ibp.lean - `FieldTheory.hasLineDerivAt_weight`, `FieldTheory.integral_weight_mul_lineDeriv`
5. Lightlike/FieldTheory/Gaussian/Mono.lean - `FieldTheory.mono`, `FieldTheory.dmono`, `FieldTheory.hasLineDerivAt_mono`
6. Lightlike/FieldTheory/Gaussian/Moments.lean - `FieldTheory.integrable_mono`, `FieldTheory.integral_dmono`, `FieldTheory.moment_cons`, `FieldTheory.moment_odd`, `FieldTheory.moment_two`, `FieldTheory.moment_four`
7. Lightlike/FieldTheory/ZeroDim/FormalIntegral.lean - `FieldTheory.formalIntegral`, `FieldTheory.formalIntegral_quartic_two`
8. Lightlike/FieldTheory/ZeroDim/Graphs.lean - `FieldTheory.vertexPerm`, `FieldTheory.Pairing`, `FieldTheory.sum_inv_card_stabilizer`,
   `FieldTheory.sum_inv_aut`, `FieldTheory.sum_inv_aut_two`, `FieldTheory.sum_inv_aut_one`
9. Lightlike/FieldTheory/Gaussian/Wick.lean - `FieldTheory.pairWeight`, `FieldTheory.pairSum`, `FieldTheory.pairSum_succ_succ`,
   `FieldTheory.moment_ofFn_eq_pairSum`, `FieldTheory.moment_eq_pairSum`
10. Lightlike/FieldTheory/ZeroDim/Quartic.lean - `FieldTheory.integral_pow_mul_gauss`, `FieldTheory.integral_pow_mul_gauss_scaled`,
   `FieldTheory.wick_one_variable`, `FieldTheory.abs_exp_neg_sub_sum_le`, `FieldTheory.quartic_expansion`
11. Lightlike/FieldTheory/Gaussian/WickSemidef.lean - `FieldTheory.moment_eq_sum_sqrt`, `FieldTheory.sum_prod_delta`,
   `FieldTheory.moment_eq_pairSum_of_posSemidef`
12. Lightlike/FieldTheory/ZeroDim/Components.lean - `FieldTheory.HalfEdge.invOn`, `FieldTheory.HalfEdge.connInvOn`,
   `FieldTheory.HalfEdge.existsUnique_componentOn`, `FieldTheory.HalfEdge.card_invOn_eq_sum`
13. Lightlike/FieldTheory/ZeroDim/GraphIso.lean - `FieldTheory.GraphAlg.LGraph`, `FieldTheory.GraphAlg.IsIso`, `FieldTheory.GraphAlg.isIso_iff_smul`,
   `FieldTheory.GraphAlg.mem_aut_iff`, `FieldTheory.GraphAlg.card_orbit_mul_card_aut`, `FieldTheory.GraphAlg.inv_card_aut`
14. Lightlike/FieldTheory/ZeroDim/GraphAlgebra.lean - `FieldTheory.GraphAlg.union`, `FieldTheory.GraphAlg.union_smul`, `FieldTheory.GraphAlg.unionC`,
   `FieldTheory.GraphAlg.GAlg`, `FieldTheory.GraphAlg.mul`, `FieldTheory.GraphAlg.X`, `FieldTheory.GraphAlg.Xc`, `FieldTheory.GraphAlg.expXc`
15. Lightlike/FieldTheory/ZeroDim/GraphComp.lean - `FieldTheory.GraphAlg.comps`, `FieldTheory.GraphAlg.ncomp`, `FieldTheory.GraphAlg.existsUnique_comp`,
   `FieldTheory.GraphAlg.comps_smul`, `FieldTheory.GraphAlg.ncomp_smul`
16. Lightlike/FieldTheory/ZeroDim/GraphSplit.lean - `FieldTheory.GraphAlg.restrictL`, `FieldTheory.GraphAlg.glue`, `FieldTheory.GraphAlg.glue_restrictL`,
   `FieldTheory.GraphAlg.anyClass_glue`, `FieldTheory.GraphAlg.comps_glue`
17. Lightlike/FieldTheory/ZeroDim/GraphExp.lean - `FieldTheory.GraphAlg.X_eq_lab`, `FieldTheory.GraphAlg.card_split`, `FieldTheory.GraphAlg.card_mul_ncomp`,
   `FieldTheory.GraphAlg.pow_Xc_eq`, `FieldTheory.GraphAlg.expXc_eq_X`

## References

1. Mathlib, `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean` (`multivariateGaussian`, `stdGaussian`) and `Fernique.lean` (`IsGaussian.memLp_id`).
2. M. Borinsky, Graphs in perturbation theory: Algebraic structure and asymptotics, PhD thesis, Humboldt-Universität zu Berlin (2018), arXiv:1807.02046, §2.1 (Definitions 2.1.1, 2.1.2, p. 10; Definitions 2.1.6, 2.1.7, p. 11), §2.3 (Proposition 2.3.1, p. 15), §2.4.2 (eqs. (2.4.5)-(2.4.7) and Theorem 2.4.1, pp. 17-18) and §3.1 (Definition 3.1.1, eq. (3.1.2), p. 22; Proposition 3.1.1, p. 23; eq. (3.1.8), p. 24).
3. L. Tubaro, M. Zanella, An introduction to Malliavin calculus, arXiv:2502.07941v1, Theorem 2.19 (Isserlis formula), p. 9.
