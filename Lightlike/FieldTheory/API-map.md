# Field theory in finite dimensions

## Abstract (Alpha)

This API treats Gaussian integrals on `ℝⁿ`, the starting point of zero-dimensional field theory. It proves that the standard Gaussian measure is Lebesgue measure with the standard density, that the centred multivariate Gaussian measure with covariance `S` has the density `exp(-(1/2) xᵀ S⁻¹ x)` with its normalisation, and the Gaussian integral `∫ exp(-(1/2) xᵀ A x) dx = (√(2π))ⁿ / √(det A)` for positive definite `A`. The centred multivariate Gaussian measure is shown to be Lebesgue measure with that density, Gaussian integration by parts is proved, and with it Isserlis' recursion for the moments: the moment of a list of coordinates is a sum over the positions paired with the first one, so odd moments vanish, the two-point function is the covariance and the four-point function is the sum over three pairings. Wick's theorem as an explicit sum over all pairings, and Feynman graphs, are open.

## Content (Alpha)

Mathlib defines the multivariate Gaussian measure by its covariance, as the image of the standard Gaussian measure under the matrix square root of the covariance {1}. Mathlib has no density for it and no moment theorem. Here the standard Gaussian measure on `ℝⁿ` is shown to be the product of the one-dimensional densities with respect to Lebesgue measure [1] {1} {3} {5}. A change of variables by an invertible matrix gives the factor `|det R|⁻¹` [2]. With the square root `R` of `S` one has `R S⁻¹ R = 1`, hence `(R y)ᵀ S⁻¹ (R y) = yᵀ y`, and the centred Gaussian measure with covariance `S` integrates a function `f` as `(√(2π))⁻ⁿ (det S)^{-1/2} ∫ exp(-(1/2) xᵀ S⁻¹ x) f(x) dx` [2] {1} {5}. Taking `f = 1` and `S = A⁻¹` gives the Gaussian integral of a positive definite `A` [2]. The measure is Lebesgue measure with density `normConst S · weight S⁻¹` [3]. The weight `exp(-(1/2) xᵀ A x)` has line derivative `-(A x)ⱼ` times itself along the coordinate direction `eⱼ`, and Mathlib's integration by parts for line derivatives gives `∫ w ∂ⱼg = ∫ (A x)ⱼ w g` [4], the finite-dimensional form of the Gaussian integration by parts `E[⟨DF, h⟩] = E[W(h) F]` {3}. For the monomial of a list of coordinates the derivative along `eⱼ` is the sum over the positions carrying the index `j` of the monomial without that position [5]. All monomials are integrable for the Gaussian measure, because a Gaussian measure has finite moments of every order {1}, and Isserlis' recursion `E[x_i x_{l₀} ⋯ x_{lₙ}] = ∑ₘ S_{i,lₘ} E[∏_{k≠m} x_{lₖ}]` follows from the integration by parts and `S S⁻¹ = 1` [6] {3}. It gives that odd moments vanish, `E[x_i x_j] = S_{ij}` and `E[x_i x_j x_k x_l] = S_{ij}S_{kl} + S_{ik}S_{jl} + S_{il}S_{jk}` [6]. Checks: the two-point function agrees with Mathlib's covariance of the multivariate Gaussian, the four-point function with one variable of variance `1` is `3`, and for `A = 1` the value is `(2π)^{n/2}`, which agrees with Mathlib's separate computation of `∫ exp(-b ‖x‖²)`, and the integrals for `A = 1` and `A = 2` in one variable differ, so the determinant is needed.

Borinsky's formal integral, the zero-dimensional field theory as a formal power series in `ħ`, has the coefficient `35λ²/384` at order `ħ²` for the quartic potential `λx⁴/4!`, the sum `1/128 + 1/16 + 1/48` of the symmetry factors of the three vacuum graphs; a wrong factor for the sunset graph is shown to fail [7] {2}.

The vacuum graphs with `m` four-valent vertices are the orbits of the pairings of their half-edges under the permutations that keep the vertices (the wreath product `S₄ ≀ S_m`, of order `24^m m!`), the symmetry factor of a graph is the inverse of the order of its stabilizer, its automorphism group, and the symmetry factors sum to `(4m - 1)!!/(24^m m!)`, by the class formula [8] {2}; for two vertices the sum is `35/384` and for one vertex `1/8`. The graphs with two vertices are exactly the two figure-eights, the dumbbell and the melon, with `|Aut Γ| = 128, 16, 48` (`1/128 + 1/16 + 1/48 = 35/384`, Borinsky's (3.1.8)) [8] {2}.

Wick's theorem: the moment `E[x_{l₀} ⋯ x_{l_{n-1}}]` of the centred Gaussian measure with positive definite covariance `S` is the sum, over the full Wick contractions of the `n` positions (Physlib's `WickContraction` with `IsFull`), of the products `∏ S_{l_p l_q}` over the contracted pairs; both sides satisfy Isserlis' recursion [9] {3}. The same holds for every positive semidefinite covariance, through the square root `√S` of Mathlib's definition of the Gaussian measure, multilinearity, and the factorisation of the sum over index maps along the pairs [11] {3}.

The one-variable Wick identity `∫ dx/√(2πħ) e^{-x²/(2aħ)} x^{2n} = √a (aħ)^n (2n - 1)!!` holds for `a, ħ > 0`, and the series `√(2π) Σ_{m<M} (-g/24)^m (4m - 1)!!/m!` approximates `∫ e^{-x²/2 - g x⁴/24} dx` for `g ≥ 0` with an error at most the size of the next term, by the alternating Taylor bound for `e^{-t}` [10] {2}.

Graphs with legs on a half-edge type `π : H → V` are the involutions of `H` (edges are 2-cycles, legs are fixed points); every vertex lies in exactly one closed connected vertex set, and splitting off the component of a vertex gives `#graphs(R) = Σ_{v₀ ∈ S ⊆ R} #connected(S) · #graphs(R \ S)` [12] {2}.

A labelled graph with half-edges `Fin n` and vertices `Fin k` is an attachment map with an involution of the half-edges; the pairs of bijections `S_n × S_k` act by relabelling, isomorphic graphs are the same orbit and the automorphisms are the stabilizer, so `1/|Aut Γ| = |orbit Γ|/(n! k!)` [13] {2}.

The disjoint union of labelled graphs is compatible with relabelling, so it is defined on isomorphism classes; the formal sums of classes of all sizes carry the disjoint-union product (finite in each grade of half-edges and vertices), and `X = Σ_Γ Γ/|Aut Γ|`, its connected part `X_c` and `e^{X_c}` are defined there [14] {2}.

**The exponential formula `X = e^{X_c}`** holds coefficientwise in the algebra of all graphs (any vertex degrees, legs allowed) {2}: the components of a labelled graph are its closed connected vertex sets and their number is a class invariant [15]; cutting a graph at a component and gluing it back is a bijection with the pairs (connected graph, rest) [16]; double counting the pairs (graph, component) gives `X_c^m(c) = [c has m components] · m! · #labelled copies/(n! k!)`, and so `e^{X_c} = X` [17].

The Feynman expansion of a Gaussian integral on `ℝⁿ`: for a homogeneous polynomial `V` of degree `d` with coefficient tensor `c` and a positive semidefinite covariance `S`, `E_S[V^m]` is the sum over the labellings of the `m` vertices and the full Wick contractions of their `md` legs of `∏_v c_(i_v) ∏_(pairs) S`; it vanishes when `md` is odd [18] {4}. The same holds for a general polynomial potential `U = Σ_κ V_κ` with homogeneous parts of degrees `d κ`: `E_S[U^m]` is the sum over the types of the `m` vertices, their labellings and the full Wick contractions of all the legs [19] {4}. As a sum over Feynman graphs: for a symmetric coefficient tensor, `E_S[(V/d!)^m]/m!` is the sum over the orbits of the leg pairings under `S_d ≀ S_m` of the graph weight divided by the order of the stabilizer, `|Aut Γ|` [20] {4}. For a general polynomial `U = Σ_κ V_κ/d_κ!` (vertices of several types and degrees), `E_S[U^m]/m!` is the sum over the multiplicities of the vertex types and the Feynman graphs with these vertices of the graph weight over `|Aut Γ|`, by the multinomial theorem [21] {4}.

**The Feynman rules with a source**: a weight on graph classes that is multiplicative under disjoint union turns `X = e^{X_c}` into `Σ_Γ w(Γ)/|Aut Γ| = exp(Σ_γ w(γ)/|Aut γ|)` for the generating functions graded by half-edges and vertices [22]. With the vertex weights `μ_d` (`μ_1 = j`, `μ_d = λ_d`) on the leg-free graphs, distributing the half-edges over the vertices [23] and pairing them gives the formal partition function with a source, `Z(ħ, j) = Σ_Γ ∏_v μ_{deg v}/|Aut Γ|`, and `Z = exp(W/ħ)` with `W/ħ` the sum over the connected graphs [24] {2}.

Every vertex of a vacuum graph lies in exactly one connected component; splitting it off gives `a_{n+1} = Σ_k C(n, k) c_{k+1} a_{n-k}` for the numbers `a_n` of pairings and `c_n` of connected pairings of `n` vertices, so the series `Z = Σ a_n xⁿ/(24ⁿ n!)` and `W = Σ c_n xⁿ/(24ⁿ n!)` satisfy `Z' = W' Z`, `Z = exp(W)` and `log Z = W` [25] [26] {2}. The coefficients of `Z` and `W` are the sums of `1/|Aut Γ|` over all and over the connected vacuum graphs with `n` vertices, so this is the exponential formula `Σ_Γ x^{|V_Γ|}/|Aut Γ| = exp(Σ_{Γ connected} x^{|V_Γ|}/|Aut Γ|)` for the quartic theory; at two vertices the connected graphs have total symmetry factor `1/12` and the disconnected one `1/128` [26] {2}.

The formal partition function is tied to the Gaussian integrals and to the formal integral: its double factorials are the moments `∫ xⁿ dγ` of the standard Gaussian measure, so each coefficient is `(∫ xⁿ dγ)/k! · [xⁿ] Vᵏ`, and Borinsky's formal integral with `a = 1` is the partition function read along `n = 2(K + m)`, `k = m`; the explicit bound of the quartic expansion gives the asymptotic expansion of the quartic integral, the error after `N + 1` terms being `o(g^N)` as `g → 0⁺` [27] {2} {6}.

**Missing.** The explicit error bound of the quartic expansion is not stated in the sources read: Borinsky treats the integral formally, and Skinner states the asymptotic expansion (2.28) in the sense of (2.20) {6}, which the bound implies [27]. The formal integral is compared with Borinsky's Definition 3.1.1 and eq. (3.1.8) {2}, the graphs with Borinsky §2.1 and §2.3 {2}, the exponential formula with Theorem 2.4.1 {2}, and Wick's theorem with Tubaro–Zanella's Theorem 2.19 {3}, the Feynman expansion with Polyak's eq. (18) {4} (labelled contractions of a polynomial potential) and Proposition 2.17 {4} (graphs with `1/|Aut Γ|` for a general polynomial potential, with the `1/k!` normalisation); the Gaussian densities and their normalisation with Rasmussen–Williams's eq. (A.4) {5} and Tubaro–Zanella's Definition 2.1 {3}, and the Gaussian integration by parts and the moment recursion with Tubaro–Zanella's Proposition 5.5, eq. (22), and its proof {3}.

## Lean References

1. Lightlike/FieldTheory/Gaussian/Density.lean - `FieldTheory.pi_gaussianReal_eq_withDensity`, `FieldTheory.integral_stdGaussian`
2. Lightlike/FieldTheory/Gaussian/Integral.lean - `FieldTheory.integral_comp_toEuclideanLin`, `FieldTheory.integral_multivariateGaussian`, `FieldTheory.integral_exp_neg_half_quad`
3. Lightlike/FieldTheory/Gaussian/Measure.lean - `FieldTheory.multivariateGaussian_eq_withDensity`, `FieldTheory.integrable_weight_mul`
4. Lightlike/FieldTheory/Gaussian/Ibp.lean - `FieldTheory.hasLineDerivAt_weight`, `FieldTheory.integral_weight_mul_lineDeriv`
5. Lightlike/FieldTheory/Gaussian/Mono.lean - `FieldTheory.mono`, `FieldTheory.dmono`, `FieldTheory.hasLineDerivAt_mono`
6. Lightlike/FieldTheory/Gaussian/Moments.lean - `FieldTheory.integrable_mono`, `FieldTheory.integral_dmono`, `FieldTheory.moment_cons`, `FieldTheory.moment_odd`, `FieldTheory.moment_two`, `FieldTheory.moment_four`
7. Lightlike/FieldTheory/ZeroDim/FormalIntegral.lean - `FieldTheory.formalIntegral`, `FieldTheory.formalIntegral_quartic_two`
8. Lightlike/FieldTheory/ZeroDim/Graphs.lean - `FieldTheory.vertexPerm`, `FieldTheory.Pairing`, `FieldTheory.sum_inv_card_stabilizer`,
   `FieldTheory.sum_inv_aut`, `FieldTheory.sum_inv_aut_two`, `FieldTheory.sum_inv_aut_one`,
   `FieldTheory.crossCount_smul`, `FieldTheory.figEights`, `FieldTheory.dumbbell`, `FieldTheory.melon`,
   `FieldTheory.card_stabilizer_figEights`, `FieldTheory.card_stabilizer_dumbbell`, `FieldTheory.card_stabilizer_melon`,
   `FieldTheory.vacuum_graphs_two`
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
18. Lightlike/FieldTheory/Gaussian/FeynmanExpansion.lean - `FieldTheory.homogPoly`, `FieldTheory.legLabels`, `FieldTheory.homogPoly_pow`,
   `FieldTheory.moment_ofFn_eq_pairSum_of_posSemidef`, `FieldTheory.integral_homogPoly_pow`, `FieldTheory.integral_homogPoly_pow_of_odd`
19. Lightlike/FieldTheory/Gaussian/FeynmanPoly.lean - `FieldTheory.polyPot`, `FieldTheory.legLabelsSigma`, `FieldTheory.polyPot_pow`,
   `FieldTheory.integral_polyPot_pow`
20. Lightlike/FieldTheory/Gaussian/FeynmanGraphs.lean - `FieldTheory.edgeWeight`, `FieldTheory.edges`, `FieldTheory.pairSum_eq_sum_involutions`,
   `FieldTheory.pairSum_legLabels`, `FieldTheory.LegPairing`, `FieldTheory.legPerm`, `FieldTheory.card_legPerm`, `FieldTheory.sum_eq_sum_orbits`,
   `FieldTheory.graphWeight`, `FieldTheory.graphWeight_smul`, `FieldTheory.integral_homogPoly_pow_graphs`
21. Lightlike/FieldTheory/Gaussian/FeynmanGraphsPoly.lean - `FieldTheory.pairSum_comp_equiv`, `FieldTheory.TPairing`, `FieldTheory.TPerm`,
   `FieldTheory.card_tperm`, `FieldTheory.tgraphWeight`, `FieldTheory.tgraphWeight_smul`, `FieldTheory.integral_prod_pow_graphs`,
   `FieldTheory.integral_polyPot_pow_graphs`
22. Lightlike/FieldTheory/ZeroDim/GraphEval.lean - `FieldTheory.GraphAlg.IsMultWeight`, `FieldTheory.GraphAlg.gen`, `FieldTheory.GraphAlg.gen_mul`,
   `FieldTheory.GraphAlg.gen_pow`, `FieldTheory.GraphAlg.coeff_gen_X`
23. Lightlike/FieldTheory/ZeroDim/MapsEGF.lean - `FieldTheory.GraphAlg.derivative_prod_univ`, `FieldTheory.GraphAlg.egf`, `FieldTheory.GraphAlg.sum_maps_prod_fiber`
24. Lightlike/FieldTheory/ZeroDim/GraphRules.lean - `FieldTheory.GraphAlg.fweight`, `FieldTheory.GraphAlg.isMultWeight_fwC`, `FieldTheory.GraphAlg.sum_fweight`,
   `FieldTheory.GraphAlg.formalZ`, `FieldTheory.GraphAlg.gen_X_eq_formalZ`, `FieldTheory.GraphAlg.coeff_formalZ_eq_exp`
25. Lightlike/FieldTheory/ZeroDim/Connected.lean - `FieldTheory.Closed`, `FieldTheory.ConnOn`, `FieldTheory.pairOn`, `FieldTheory.connPairOn`,
   `FieldTheory.existsUnique_component`, `FieldTheory.card_pairOn_eq_sum`, `FieldTheory.numPairings`, `FieldTheory.numConnected`,
   `FieldTheory.numPairings_succ`, `FieldTheory.vacuumSeries`, `FieldTheory.connectedSeries`, `FieldTheory.derivative_vacuumSeries`,
   `FieldTheory.vacuumSeries_eq_exp`
26. Lightlike/FieldTheory/ZeroDim/ConnectedGraphs.lean - `FieldTheory.ConnPairing`, `FieldTheory.connOn_smul`, `FieldTheory.sum_inv_aut_connected`,
   `FieldTheory.coeff_vacuumSeries`, `FieldTheory.coeff_connectedSeries`, `FieldTheory.logOf_vacuumSeries`,
   `FieldTheory.coeff_logOf_vacuumSeries`, `FieldTheory.numConnected_two`, `FieldTheory.sum_inv_aut_connected_two`

27. Lightlike/FieldTheory/ZeroDim/Ties.lean - `FieldTheory.dfact_eq_integral`, `FieldTheory.coeff_formalZ_eq_integral`,
   `FieldTheory.coeff_formalIntegral_eq_formalZ`, `FieldTheory.tendsto_quartic_div`
## References

1. Mathlib, `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean` (`multivariateGaussian`, `stdGaussian`) and `Fernique.lean` (`IsGaussian.memLp_id`).
2. M. Borinsky, Graphs in perturbation theory: Algebraic structure and asymptotics, PhD thesis, Humboldt-Universität zu Berlin (2018), arXiv:1807.02046, §2.1 (Definitions 2.1.1, 2.1.2, p. 10; Definitions 2.1.6, 2.1.7, p. 11), §2.3 (Proposition 2.3.1, p. 15), §2.4.2 (eqs. (2.4.5)-(2.4.7) and Theorem 2.4.1, pp. 17-18), §3.1 (Definition 3.1.1, eq. (3.1.2), p. 22; Proposition 3.1.1, p. 23; eq. (3.1.8), p. 24) and Chapter 7 (§7.1, pp. 116-117).
3. L. Tubaro, M. Zanella, An introduction to Malliavin calculus, arXiv:2502.07941v1, Definition 2.1, p. 4; Theorem 2.19 (Isserlis formula), p. 9; eqs. (20), (21), pp. 18-19; Proposition 5.5 (eq. (22)), p. 19, and its proof, p. 20.
4. M. Polyak, Feynman diagrams for pedestrians and mathematicians, arXiv:math/0406251v1, §2.3 (Theorem 2.8, p. 5), §2.6 (eq. (18), p. 7) and §2.8 (Proposition 2.17, p. 9).
5. C. E. Rasmussen, C. K. I. Williams, Gaussian Processes for Machine Learning, MIT Press (2006), Appendix A, §A.2, eq. (A.4), p. 200, and the sampling of `N(m, K)` as `m + L u` with `K = L Lᵀ`, p. 201.
6. D. Skinner, Advanced Quantum Field Theory, lecture notes, University of Cambridge, Chapter 2, QFT in zero dimensions (www.damtp.cam.ac.uk/user/dbs26/AQFT/chap2.pdf), eq. (2.20), p. 17, and eqs. (2.26)-(2.28), pp. 19-20.
