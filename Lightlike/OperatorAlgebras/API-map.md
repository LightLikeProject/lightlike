# Operator algebras and Hilbert-space representations

## Abstract (Alpha)

This API holds the definitions for unbounded self-adjoint operators and the Weyl relations. The operator
type is Mathlib's partially defined linear map, with its adjoint and self-adjointness. It adds strongly
continuous one-parameter unitary groups with their generators, for Stone's theorem, and Bogoliubov
transformations, Hilbert–Schmidt maps and Fock representations, for Shale's criterion. The theorems
themselves are open proof tasks, in `Tasks/OP/`.

## Content (Alpha)

The generator of a unitary group is self-adjoint: its domain is dense and invariant, it is symmetric, and a vector of the domain of its adjoint satisfies `U t y = y + i ∫₀ᵗ U s (A† y) ds`, so it lies in the domain [9]. Two groups with the same generator are equal, because the norm of `U t ψ - V t ψ` is constant [10].

A strongly continuous one-parameter unitary group is a family of unitaries `U t` with `U 0 = 1`,
`U (s + t) = U s ∘ U t` and `t ↦ U t ψ` continuous [1]. Its generator `A` is `-i d/dt U t ψ` at `0`, on
the vectors where the derivative exists, so that formally `U t = exp (i t A)` [1]. Stone's theorem says
that the generator is self-adjoint, that every self-adjoint operator is a generator, and that the group is
determined by it {1}. The phase group `exp (i λ t)` has the generator `λ`, and the generators of `λ = 1`
and `λ = -1` differ [2]. A Bogoliubov transformation of a complex Hilbert space `h` is a continuous
real-linear bijection that preserves the symplectic form `Im ⟪f, g⟫`, with a complex-linear part and an
antilinear part [3]. A representation of the Weyl relations is a family of unitaries `W f` with
`W f ∘ W g = exp (-i Im ⟪f, g⟫ / 2) W (f + g)`, and a Fock representation has a cyclic unit vector with the
vacuum expectation `exp (-‖f‖² / 4)` [3]. Shale's criterion says that a Bogoliubov transformation is
implemented by a unitary of the Fock representation exactly when its antilinear part is Hilbert–Schmidt {2}.
In one mode the squeezing has `|α|² - |β|² = 1` and the dilation `f ↦ 2 f` is not symplectic [4]. A map with `‖B f‖ = c ‖f‖`, `c > 0`, is not Hilbert–Schmidt when a Hilbert basis is infinite [4]. On `L²(ℝ)` translation `ψ(x + t)` is a strongly continuous unitary group [5], and its generator is `-i d/dx` on `C²` functions with compact support, not `+i d/dx` [6]. On `L²(0, 1)` the operator `-i d/dx` on the `C²` functions supported inside `(0, 1)` is given by its graph [7]. The deficiency spaces of an operator are the kernels of the adjoint minus `±i`, and a self-adjoint operator has none [8]. The
Fock space itself is not built here, and a Fock representation is characterized by its vacuum. The
unbounded spectral theorem is not in Mathlib. Stone's theorem and Shale's criterion are [TODO] here.

The graph of `-i d/dx` on the `C_c^∞(0, 1)` functions is the image of the smooth test functions under the same pair map, and lies inside the `C²` graph [11]. It contains a nonzero vector, a bump function supported in `(0, 1)` [12]. Mollification by a normed bump function maps a `C²` test function to a `C_c^∞` one, with the derivative of the mollified function the mollified derivative, and converges uniformly with its derivative, so the two graphs have the same closure [13].

`-i d/dx` on the `C²` test functions of `(0, 1)` is densely defined, since a vector orthogonal to all test functions is zero [16]. A function with zero weak derivative on `(0, 1)` is almost everywhere constant, by a primitive of `ψ - (∫ ψ) φ₀` [16]. The deficiency vectors of this operator at `z` with `conj z = i b` are the multiples of `exp (b x)`, so both deficiency spaces are one-dimensional, the deficiency indices `(1, 1)` [17]. The exponentials lie in the right spaces and are nonzero [18].

A dense subspace of the domain of the generator of a unitary group that is invariant under the group is a core: the closure of the generator restricted to it is the generator [19]. The classes of `C_c^∞` functions form such a subspace for the translation group on `L²(ℝ)`, so every vector of the domain of the momentum operator is a limit of `C_c^∞` functions with the derivatives converging [20], and the subspace is not zero [21].

Two linear maps from finitely supported coefficients whose generators have the same Gram matrix have the same norm, and with dense ranges there is a unitary between the spaces that intertwines them [22]. The Fock kernel `⟪k_f, k_g⟫ = e(f) e(g) exp (⟪f, g⟫ / 2)` is positive semidefinite: the kernel `exp (⟪f, g⟫ / 2)` is the sum of the entrywise powers of the Gram matrix, each positive semidefinite by the Schur product theorem [23]. Its reproducing kernel Hilbert space, with the Weyl unitaries `W g k_f = exp (-i σ(g, f) / 2) k_{f+g}` obtained from the Gram invariance of the shift and the vacuum `k_0`, is a Fock representation, so a Fock representation of every complex Hilbert space exists [24]. It is not the trivial representation [25].

Every nonzero vector of a Fock representation is cyclic for the Weyl unitaries (irreducibility): for a bounded operator `C` commuting with all `W f`, the function `x ↦ ⟪W x Ω, C Ω⟫ / exp (-‖x‖² / 4)` is antiholomorphic along complex lines, and equal to the conjugate of the corresponding function of `C* Ω` at `-x`, so it is both holomorphic and antiholomorphic, hence constant; so `C Ω` is a multiple of `Ω` and `C` is a scalar, and the projection onto the closed span of `W f ψ` is `1` [35]. The kernel vectors of the constructed representation are cyclic [36].

A Bogoliubov transformation `T` is implemented in a Fock representation iff there is a vector `Ψ` with `⟪Ψ, W f Ψ⟫ = exp (-‖T f‖² / 4)`: `Ψ = U⁻¹ Ω` for an implementing unitary `U`, and conversely the vectors `W f Ψ` and `W (T f) Ω` have the same Gram matrix, `Ψ` is cyclic by irreducibility, and the Gram unitary intertwines the Weyl operators [37]. The identity transformation is implemented, with `Ψ = Ω` [38].

For a self-adjoint operator `A` and `z` with `Im z ≠ 0`, `A - z` is a bijection from the domain onto the space with `‖(A - z) x‖ ≥ |Im z| ‖x‖`, and its inverse, the resolvent, is a bounded operator of norm at most `1 / |Im z|` whose adjoint is the resolvent at `conj z` [26]. The resolvent of the generator `λ • 1` of the phase group is `(λ - z)⁻¹` [27].

For a self-adjoint `A`, `t R (i t) y → i y` and `t R (-i t) y → -i y` for every `y` (on the domain from `R z (A x) = x + z R z x`, then everywhere by density and the bound `‖t R‖ ≤ 1`) [28]. The operators `A_n = (t² / 2) (R (i t) + R (-i t))`, `t = n + 1`, are bounded and self-adjoint, and `A_n x → A x` on the domain [28]. For the phase-group generator `λ • 1` the approximant is `t² λ / (λ² + t²)` [29].

For a bounded self-adjoint operator `B`, `exp (i s B)` is a unitary group, strongly continuous in `s`, and for two commuting bounded self-adjoint operators `‖exp (i t B) y - exp (i t B') y‖ ≤ |t| ‖(B - B') y‖`, the mean value inequality for `s ↦ exp (i s B) exp (i (t - s) B') y` [30]. With `B' = 0` this is `‖exp (i t B) y - y‖ ≤ |t| ‖B y‖` [32]. The resolvents of a self-adjoint operator satisfy `R z - R w = (z - w) R z R w`, so they commute, and so do the approximants, which are self-adjoint as bounded operators [31].

For a self-adjoint `A`, the approximating unitaries `exp (i t A_n)` have a strong limit `U t`: `U_n t x` is Cauchy on the domain by the estimate above, hence for every vector by density and isometry, and `‖U_n t x - U t x‖ ≤ |t| ‖A_n x - A x‖` on the domain. The limit is a strongly continuous unitary group, the difference quotient of `U t x` at `0` is within `2 ‖A_n x - A x‖` of that of `exp (i t A_n) x`, so the generator of the limit extends `A`, and since both are self-adjoint it equals `A`: this is Stone's theorem, existence [33]. For the phase group it recovers the phase group [34].

The Gram matrix of the vectors `W f Ω` of a Fock representation is a function of `f` and `g` alone, by the Weyl relations and the vacuum expectation, so the map `c ↦ ∑ c f W f Ω` has the same norm for two Fock representations; it extends to a unitary that maps the vacuum to the vacuum and intertwines the Weyl unitaries, which is the uniqueness of the Fock representation [14]. The Gram function is Hermitian and normalized, and over the zero Hilbert space there is a Fock representation to which the uniqueness applies [15].

## Lean References

1. Lightlike/OperatorAlgebras/UnitaryGroup.lean - `OperatorAlgebras.UnitaryGroup`,
   `OperatorAlgebras.UnitaryGroup.generatorDomain`, `OperatorAlgebras.UnitaryGroup.generator`
2. Lightlike/OperatorAlgebras/TestsUnitaryGroup.lean - `OperatorAlgebras.phaseGroup`,
   `OperatorAlgebras.phaseGroup_domain`, `OperatorAlgebras.phaseGroup_generator`,
   `OperatorAlgebras.phaseGroup_generator_ne`
3. Lightlike/OperatorAlgebras/Weyl.lean - `OperatorAlgebras.symp`, `OperatorAlgebras.Bogoliubov`,
   `OperatorAlgebras.Bogoliubov.alphaPart`, `OperatorAlgebras.Bogoliubov.betaPart`,
   `OperatorAlgebras.IsHilbertSchmidt`, `OperatorAlgebras.CCRRep`, `OperatorAlgebras.FockRep`,
   `OperatorAlgebras.Implements`
4. Lightlike/OperatorAlgebras/TestsWeyl.lean - `OperatorAlgebras.squeezeMap`,
   `OperatorAlgebras.squeeze`, `OperatorAlgebras.squeeze_alpha`, `OperatorAlgebras.squeeze_beta`,
   `OperatorAlgebras.squeeze_norm_sq`, `OperatorAlgebras.dilation_not_symplectic`,
   `OperatorAlgebras.not_isHilbertSchmidt_of_norm_eq`
5. Lightlike/OperatorAlgebras/Translation.lean - `OperatorAlgebras.L2R`,
   `OperatorAlgebras.shiftL`, `OperatorAlgebras.translationGroup`
6. Lightlike/OperatorAlgebras/GeneratorTranslation.lean - `OperatorAlgebras.norm_toLp_le`,
   `OperatorAlgebras.taylor_bound`, `OperatorAlgebras.ofCS`,
   `OperatorAlgebras.translationGroup_hasDerivAt`, `OperatorAlgebras.translationGroup_generator_ofCS`,
   `OperatorAlgebras.translationGroup_generator_ne`, `OperatorAlgebras.exists_core_ne_zero`
7. Lightlike/OperatorAlgebras/MomentumInterval.lean - `OperatorAlgebras.L2I`, `OperatorAlgebras.classI`,
   `OperatorAlgebras.testFunctions`, `OperatorAlgebras.momentumGraph`, `OperatorAlgebras.momentumMin`,
   `OperatorAlgebras.momentumMin_graph`
8. Lightlike/OperatorAlgebras/Deficiency.lean - `OperatorAlgebras.deficiencySpace`,
   `OperatorAlgebras.deficiencyDim`, `OperatorAlgebras.deficiencyDim_of_isSelfAdjoint`
9. Lightlike/OperatorAlgebras/StoneGenerator.lean - `OperatorAlgebras.UnitaryGroup.dvec`,
   `OperatorAlgebras.UnitaryGroup.prim`, `OperatorAlgebras.UnitaryGroup.dense_generatorDomain`,
   `OperatorAlgebras.UnitaryGroup.generator_isSelfAdjoint` (the proof of task T-OP1-P1)
10. Lightlike/OperatorAlgebras/StoneUnique.lean - `OperatorAlgebras.UnitaryGroup.eq_of_generator_eq`
    (the proof of task T-OP1-P3)
11. Lightlike/OperatorAlgebras/MomentumSmooth.lean - `OperatorAlgebras.momentumPairLin`,
    `OperatorAlgebras.smoothTestFunctions`, `OperatorAlgebras.momentumGraphSmooth`,
    `OperatorAlgebras.momentumGraphSmooth_le` (the graph of the momentum operator on smooth test functions;
    the statement of task T-OP1-P6 is that its closure equals the closure of the C² graph)
12. Lightlike/OperatorAlgebras/TestsMomentumSmooth.lean - `OperatorAlgebras.bumpHalf`,
    `OperatorAlgebras.momentumGraphSmooth_ne_bot`
13. Lightlike/OperatorAlgebras/MomentumMollify.lean - `OperatorAlgebras.moll`,
    `OperatorAlgebras.bumpOfRadius`, `OperatorAlgebras.momentumGraph_le_closure`,
    `OperatorAlgebras.closure_momentumGraphSmooth_eq` (the proof of task T-OP1-P6, by mollification)
14. Lightlike/OperatorAlgebras/FockUnique.lean - `OperatorAlgebras.fockGram`, `OperatorAlgebras.fockMap`,
    `OperatorAlgebras.fockEquiv`, `OperatorAlgebras.fockUnitary`, `OperatorAlgebras.fockUnitary_spec`
    (the proof of task T-OP2-P2)
15. Lightlike/OperatorAlgebras/TestsFock.lean - `OperatorAlgebras.fockGram_zero`,
    `OperatorAlgebras.fockGram_conj`, `OperatorAlgebras.trivialFock`, `OperatorAlgebras.trivialFock_unitary`
16. Lightlike/OperatorAlgebras/WeakConstant.lean - `OperatorAlgebras.bumpB`, `OperatorAlgebras.bump0`,
    `OperatorAlgebras.weak_const`
17. Lightlike/OperatorAlgebras/MomentumDeficiency.lean - `OperatorAlgebras.dense_momentumMin_domain`,
    `OperatorAlgebras.expC`, `OperatorAlgebras.expL2`, `OperatorAlgebras.deficiencyDim_eq_one`,
    `OperatorAlgebras.deficiency_indices_momentumMin` (the proof of task T-OP1-P5)
18. Lightlike/OperatorAlgebras/TestsMomentumDeficiency.lean - `OperatorAlgebras.expL2_neg_mem_deficiency_I`,
    `OperatorAlgebras.expL2_mem_deficiency_negI`
19. Lightlike/OperatorAlgebras/StoneCore.lean - `OperatorAlgebras.UnitaryGroup.WeakGen`,
    `OperatorAlgebras.UnitaryGroup.closure_domRestrict_generator`
20. Lightlike/OperatorAlgebras/TranslationCore.lean - `OperatorAlgebras.smoothCS`,
    `OperatorAlgebras.translationGroup_core_smooth` (the proof of task T-OP1-P4)
21. Lightlike/OperatorAlgebras/TestsTranslationCore.lean - `OperatorAlgebras.bumpRB`,
    `OperatorAlgebras.bumpR`, `OperatorAlgebras.smoothCS_exists_ne_zero`
22. Lightlike/OperatorAlgebras/GramUnitary.lean - `OperatorAlgebras.exists_unitary_of_gram_eq`
23. Lightlike/OperatorAlgebras/FockKernel.lean - `OperatorAlgebras.posSemidef_gram_inf`,
    `OperatorAlgebras.gramPow`, `OperatorAlgebras.posSemidef_gramPow`,
    `OperatorAlgebras.posSemidef_of_hasSum`, `OperatorAlgebras.gaussE`, `OperatorAlgebras.fockGram_eq`,
    `OperatorAlgebras.expKer`, `OperatorAlgebras.fockMat`, `OperatorAlgebras.posSemidef_fockMat`
24. Lightlike/OperatorAlgebras/FockExists.lean - `OperatorAlgebras.fockKer`, `OperatorAlgebras.FockSpace`,
    `OperatorAlgebras.kf`, `OperatorAlgebras.fockPhase`, `OperatorAlgebras.fockPhase_cocycle`,
    `OperatorAlgebras.fockGram_shift`, `OperatorAlgebras.fockPhi`, `OperatorAlgebras.exists_fockWeyl`,
    `OperatorAlgebras.fockW`, `OperatorAlgebras.continuous_of_dense_isometries`,
    `OperatorAlgebras.fockRepOf` (the proof of task T-OP2-P1)
25. Lightlike/OperatorAlgebras/TestsFockExists.lean - `OperatorAlgebras.fockRepOf_W_ne_one`
26. Lightlike/OperatorAlgebras/Resolvent.lean - `OperatorAlgebras.shiftMap`,
    `OperatorAlgebras.sa_shiftMap_surjective`, `OperatorAlgebras.shiftEquiv`,
    `OperatorAlgebras.resolventCLM`, `OperatorAlgebras.resolvent_spec`,
    `OperatorAlgebras.resolvent_adjoint`
27. Lightlike/OperatorAlgebras/TestsResolvent.lean - `OperatorAlgebras.resolvent_phaseGroup`
28. Lightlike/OperatorAlgebras/Yosida.lean - `OperatorAlgebras.tendsto_of_dense_bounded`,
    `OperatorAlgebras.tResP_tendsto`, `OperatorAlgebras.tResM_tendsto`, `OperatorAlgebras.approx`,
    `OperatorAlgebras.approx_tendsto`, `OperatorAlgebras.approx_selfadjoint`
29. Lightlike/OperatorAlgebras/TestsYosida.lean - `OperatorAlgebras.approx_phaseGroup`
30. Lightlike/OperatorAlgebras/BoundedGroup.lean - `OperatorAlgebras.bdU`, `OperatorAlgebras.bdU_norm`,
    `OperatorAlgebras.bdU_cauchy`, `OperatorAlgebras.bdUnitary`
31. Lightlike/OperatorAlgebras/ResolventIdentity.lean - `OperatorAlgebras.resolvent_identity`,
    `OperatorAlgebras.resolvent_commute`, `OperatorAlgebras.approx_commute`,
    `OperatorAlgebras.approx_isSelfAdjoint`
32. Lightlike/OperatorAlgebras/TestsBoundedGroup.lean - `OperatorAlgebras.bdU_sub_self_le`
33. Lightlike/OperatorAlgebras/YosidaLimit.lean - `OperatorAlgebras.Un`,
    `OperatorAlgebras.cauchySeq_of_dense_isometries`, `OperatorAlgebras.Ulim`, `OperatorAlgebras.Uunit`,
    `OperatorAlgebras.stoneGroup`, `OperatorAlgebras.hasDerivAt_Ulim_domain`,
    `OperatorAlgebras.generator_stoneGroup` (the proof of task T-OP1-P2)
34. Lightlike/OperatorAlgebras/TestsYosidaLimit.lean - `OperatorAlgebras.stoneGroup_phaseGroup`
35. Lightlike/OperatorAlgebras/FockIrreducible.lean - `OperatorAlgebras.const_of_holo_antiholo`,
    `OperatorAlgebras.kv`, `OperatorAlgebras.FF`, `OperatorAlgebras.differentiable_conj_FF`,
    `OperatorAlgebras.commutant_scalar`, `OperatorAlgebras.fockRep_cyclic` (the proof of task T-OP2-P4)
36. Lightlike/OperatorAlgebras/TestsFockIrreducible.lean - `OperatorAlgebras.kf_cyclic`
37. Lightlike/OperatorAlgebras/FockReduction.lean - `OperatorAlgebras.gaussian_vector_of_implements`,
    `OperatorAlgebras.implements_of_gaussian_vector`, `OperatorAlgebras.implements_iff_gaussian_vector`
    (the proof of task T-OP2-P5)
38. Lightlike/OperatorAlgebras/TestsFockReduction.lean - `OperatorAlgebras.Bogoliubov.id`,
    `OperatorAlgebras.implements_id`

39. Lightlike/OperatorAlgebras/HilbertSchmidtBasis.lean -
    `OperatorAlgebras.hasSum_norm_sq_inner_basis`, `OperatorAlgebras.hasSum_norm_sq_apply_eq_adjoint`,
    `OperatorAlgebras.hasSum_norm_sq_apply_of_basis`
40. Lightlike/OperatorAlgebras/ShaleAlgebra.lean - `OperatorAlgebras.Bogoliubov.map_eq`,
    `OperatorAlgebras.Bogoliubov.norm_alpha_sq_sub_norm_beta_sq`, `OperatorAlgebras.Bogoliubov.four_norm_beta_sq`,
    `OperatorAlgebras.Bogoliubov.alphaCLM`, `OperatorAlgebras.Bogoliubov.alpha_sub_one_nonneg`,
    `OperatorAlgebras.Bogoliubov.norm_sqrt_sq`
41. Lightlike/OperatorAlgebras/ShaleHilbertSchmidt.lean -
    `OperatorAlgebras.Bogoliubov.isHilbertSchmidt_betaPart`,
    `OperatorAlgebras.Bogoliubov.isHilbertSchmidt_of_finite_bound`
42. Lightlike/OperatorAlgebras/ShaleDeterminant.lean - `OperatorAlgebras.det_four_add_of_posSemidef`,
    `OperatorAlgebras.uncertaintyMatrix`, `OperatorAlgebras.cayleyBlock`,
    `OperatorAlgebras.four_pow_mul_le_det_one_add` (the determinant bound from the uncertainty relation)
43. Lightlike/OperatorAlgebras/FockVacuumAverage.lean - `OperatorAlgebras.modeVec`,
    `OperatorAlgebras.integral_vacuumIntegrand`, `OperatorAlgebras.gaussZ_mul_norm_inner_sq_le` (the Gaussian
    average of the Weyl unitaries over finitely many modes bounds the vacuum overlap)
44. Lightlike/OperatorAlgebras/ShaleNecessity.lean - `OperatorAlgebras.covMatrix`,
    `OperatorAlgebras.posSemidef_uncertaintyMatrix`, `OperatorAlgebras.norm_inner_sq_mul_sqrt_le_one`,
    `OperatorAlgebras.shale_necessity_of_implements` (the proof of task T-OP2-P6)
45. Lightlike/OperatorAlgebras/FockContinuity.lean - `OperatorAlgebras.FockRep.continuous_W` (norm continuity
    of the Weyl unitaries of a Fock representation), `OperatorAlgebras.Bogoliubov.twist`
46. Lightlike/OperatorAlgebras/VacuumProjection.lean - `OperatorAlgebras.vacAvg` (the vacuum projection of
    finitely many modes), `OperatorAlgebras.vacAvg_symm`, `OperatorAlgebras.vacAvg_W_vacAvg`,
    `OperatorAlgebras.vacAvg_idem`, `OperatorAlgebras.exists_fixed_of_decreasing_projections`
47. Lightlike/OperatorAlgebras/ShaleSufficiency.lean - `OperatorAlgebras.det_le_exp_trace_sub_card`,
    `OperatorAlgebras.norm_sq_vacAvg_twist_Ω`, `OperatorAlgebras.shale_sufficiency_of_hilbertSchmidt` (the
    proof of task T-OP2-P7), `OperatorAlgebras.shale_criterion` (both directions)
48. Lightlike/OperatorAlgebras/TestsShale.lean - `OperatorAlgebras.Bogoliubov.neg`,
    `OperatorAlgebras.isHilbertSchmidt_id_betaPart`, `OperatorAlgebras.implements_neg`
49. Lightlike/OperatorAlgebras/TestsShaleSqueeze.lean - `OperatorAlgebras.Bogoliubov.squeeze`,
    `OperatorAlgebras.Bogoliubov.squeeze_betaPart`, `OperatorAlgebras.implements_squeeze`

## References

1. B. C. Hall, *Quantum Theory for Mathematicians*, Graduate Texts in Mathematics 267, Springer, 2013,
   Chapter 10 (Stone's theorem).
2. O. Bratteli and D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, 2nd ed.,
   Springer, 1997, Chapter 5, after D. Shale, *Linear symmetries of free boson fields*, Trans. Amer. Math.
   Soc. 103 (1962) 149.
