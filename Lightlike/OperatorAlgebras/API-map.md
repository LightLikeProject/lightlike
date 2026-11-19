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
unbounded spectral theorem is not in Mathlib; it is ported from physicslib4: every self-adjoint operator has a unique
projection-valued measure on the Borel sets of `ℝ` whose spectral integral of `λ` is the operator {4} [62]; the group `e^{itA}` of a self-adjoint operator is a `UnitaryGroup` whose generator is `A` [63]. Stone's theorem and Shale's criterion are [TODO] here.

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

A strongly continuous contraction semigroup on a Banach space has a generator, the limit of the difference quotients on the vectors where it exists, a partially defined linear map. A densely defined operator `A` with `λ - A` bounded below by `λ` and surjective for every `λ > 0` is the generator of a contraction semigroup (the generation direction of the Hille–Yosida theorem) [42] {3}: the resolvent `R(λ) = (λ - A)⁻¹` has norm at most `λ⁻¹`, the Yosida approximants `λ² R(λ) - λ` give contractions `exp (t (λ² R(λ) - λ))` that converge, by a Cauchy estimate and the density of the domain, to a semigroup whose generator contains `A`, and a dissipative generator with `λ - A` surjective equals `A`. Checks: the trivial semigroup is a contraction semigroup, the theorem applies to `A = 0`, and `A = id` fails the lower bound at `λ = 1` [43]. The converse holds as well, so the two form the equivalence of the Hille–Yosida theorem for contraction semigroups [44] {3}: the orbits `t ↦ S t x` are continuous for all times `t ≥ 0` by the semigroup law and continuity at `0` [45], the averages `t⁻¹ ∫₀ᵗ S s x ds` lie in the domain of the generator and converge to `x`, which makes the domain dense [45], the resolvent `∫₀^∞ e^{-λ t} S t y dt` is a Bochner integral that lies in the domain with `(λ - A) R(λ) y = y` [46], and `norm_dissip` gives the lower bound [44].

A bounded operator on a complex Hilbert space is trace class when the diagonal sum `∑ ⟪eᵢ, |T| eᵢ⟫` converges in a Hilbert basis, and the trace and the trace norm do not depend on the basis [47]. The Hilbert-Schmidt operators, those with `∑ ‖S eᵢ‖² < ∞` in one basis, are two-sided ideal elements, and the diagonal sums of `R S` and `S R` for Hilbert-Schmidt `R`, `S` agree (cyclicity of the trace) [48]; a product of two Hilbert-Schmidt operators is trace class [49]. The trace pairing `A ↦ Tr (A ·)` is an isometry of the bounded operators into the dual of the trace class [50], and every continuous functional on the trace class is a trace pairing, so the dual of the trace class is the bounded operators [51]. The trace of the rank-one operator on `ℂ` is `1`, and every operator on a finite-dimensional space is trace class; the identity of an infinite-dimensional Hilbert space is not Hilbert-Schmidt [52]. The diagonal operator with eigenvalues `1 / (n + 1)` on `ℓ²(ℕ)` is Hilbert-Schmidt and not trace class [53]. This layer is ported from Physlib with attribution; the duality between the compact operators and the trace class is not covered.

For a Hilbert basis `{eᵢ}`, `∑ᵢ |⟪eᵢ, y⟫|² = ‖y‖²` (Parseval), the Hilbert-Schmidt square sum `∑ᵢ ‖S eᵢ‖²` of a bounded `S` in one basis equals that of `S⋆` in a second basis, and so it converges in every Hilbert basis to the same sum once it converges in one [39]. A Bogoliubov transformation is `T f = α f + β f` with `α` complex-linear and `β` antilinear, and the symplectic condition gives `‖α e‖² - ‖β e‖² = ‖e‖²` and `4 ‖β e‖² = ‖T e‖² + ‖T (i e)‖² - 2 ‖e‖²`; `α` is a bounded operator with `α†α - 1` positive and `‖√(α†α - 1) e‖² = ‖β e‖²` [40]. Hence the antilinear part is Hilbert-Schmidt as soon as `∑ᵢ ‖β bᵢ‖²` converges in one Hilbert basis, and in particular when the finite sums `∑_{i ∈ s} (‖T bᵢ‖² + ‖T (i bᵢ)‖² - 2)` are bounded, the quantity that the vacuum projections onto finitely many modes control in the necessity part of Shale's criterion [41].

On `L²(0, 1)`, a vector lies in the domain of the adjoint of `-i d/dx` (on the `C²` test functions) iff it is a primitive `c + ∫₀ˣ g` with `g ∈ L²`, equivalently iff it agrees almost everywhere with an absolutely continuous function whose derivative is in `L²`, and then the adjoint is `-i g` [64], [65]. Its continuous representative has boundary values `y(0)`, `y(1)`, and integration by parts for absolutely continuous functions gives the boundary form `⟪A† y, z⟫ - ⟪y, A† z⟫ = i (conj y(1) z(1) - conj y(0) z(0))`; the affine functions give every pair of boundary values [65]. The closure of the momentum is the adjoint on the vectors with zero boundary values, the restriction `P_θ` of the adjoint to `y(1) = e^{iθ} y(0)` is self-adjoint, and every self-adjoint extension of the momentum is a `P_θ` {5}, [66]. The constant `1` lies in the periodic domain and not in the antiperiodic one, so `P_0 ≠ P_π`, and the closure is not self-adjoint [67].

The plane waves `e^{i(θ + 2πn)x}`, `n ∈ ℤ`, lie in the domain of `P_θ` and are orthonormal eigenvectors with eigenvalue `θ + 2πn`; an eigenvector of `P_θ` with eigenvalue `μ ∈ ℂ` has the continuous representative `y(0) e^{iμx}`, so `μ = θ + 2πn` and the eigenspaces are one-dimensional; off `θ + 2πℤ` the resolvent equation is solved explicitly, so the spectrum of `P_θ`, in Physlib's sense, is `θ + 2πℤ` and equals the point spectrum {5}, [68]. `θ` is in the spectrum of `P_θ` and `θ + π` is not [69].
A representation of the CAR over `ℝᵐ` is a family of self-adjoint operators with `φ a φ b + φ b φ a = 2 δ_ab`; the Pauli matrices are one over `ℝ³`, the tensor product construction joins two, and the Jordan-Wigner operators `σ₃ ⊗ ⋯ ⊗ σ₃ ⊗ σ₁,₂ ⊗ 1 ⊗ ⋯ ⊗ 1` are one over `ℝ²ⁿ`, whose annihilation operators `aⱼ = (φ_{2j} + i φ_{2j+1}) / 2` satisfy `aᵢ aⱼ* + aⱼ* aᵢ = δᵢⱼ` and kill the empty configuration [70]. On the exterior algebra, left multiplication `a*(v)` and contraction `a(d)` satisfy the CAR with the vacuum `1` [71], and `|x⟩ ↦ ∏_{xⱼ = 1} eⱼ` is a linear isomorphism `⊗ⁿℂ² ≅ Λ(ℂⁿ)` that intertwines the Jordan-Wigner creation and annihilation operators with these [72]. The Fock inner product on `Λ(ℂⁿ)`, for which the configuration vectors are orthonormal, is the only sesquilinear form with `⟪1, 1⟫ = 1` for which `a*(eⱼ)` and `a(eⱼ*)` are mutually adjoint, and the Fock representation on it is irreducible [74]. Every representation over `ℝ²ⁿ` is unitarily equivalent to the Jordan-Wigner one tensored with the identity of its vacuum space `K = ⋂ⱼ ker aⱼ`, it is irreducible iff `K` is one-dimensional, two irreducible ones are unitarily equivalent, and over `ℝ²ⁿ⁺¹` the last generator becomes `Iₙ ⊗ T` for a self-adjoint unitary `T` of `K` {6}; the proof uses the ordered creation words `c₀^{x₀} ⋯ c_{n-1}^{x_{n-1}}` on `K`, their orthonormality and the resolution of the identity `∑ₓ cWord x · a₀c₀ ⋯ · aWord x = 1` [73].

For a finite-dimensional `h`, the Weyl unitaries are jointly strongly continuous [75]. The Gaussian average `P = ∫ e^{-‖z‖²/4} W z dz` satisfies `P W f P = (2π)^d e^{-‖f‖²/4} P` (von Neumann's identity, from the Gaussian kernel integral [76]), so `P₀ = (2π)^{-d} P` is an orthogonal projection, nonzero on a nonzero space by Fourier inversion, and a unit vector of its range has the Fock vacuum expectation [77]. Hence every representation of the Weyl relations of `h` is the Hilbert sum of Fock representations over an orthonormal basis of the range of `P₀`, it is irreducible iff that range is one-dimensional, and an irreducible one is unitarily equivalent to the Fock representation: the Stone-von Neumann theorem {7} [78].

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
42. Lightlike/OperatorAlgebras/Semigroup/Generation.lean - `OperatorAlgebras.hille_yosida_generation`,
    `OperatorAlgebras.ContractionSemigroup.norm_dissip` (the proof of task T-OP1-P7); definitions in
    the file Semigroup/Defs: `OperatorAlgebras.ContractionSemigroup`, `OperatorAlgebras.ContractionSemigroup.generator`
43. Lightlike/OperatorAlgebras/Semigroup/Tests.lean - `OperatorAlgebras.trivialSemigroup`
44. Lightlike/OperatorAlgebras/Semigroup/Converse.lean - `OperatorAlgebras.contractionSemigroup_generator_hypotheses`,
    `OperatorAlgebras.hilleYosida_contraction`
45. Lightlike/OperatorAlgebras/Semigroup/Continuity.lean - `OperatorAlgebras.ContractionSemigroup.continuous_orbit`,
    `OperatorAlgebras.ContractionSemigroup.dense_generatorDomain`
46. Lightlike/OperatorAlgebras/Semigroup/LaplaceResolvent.lean - `OperatorAlgebras.ContractionSemigroup.resolvent`,
    `OperatorAlgebras.ContractionSemigroup.tendsto_quot_resolvent`
47. Lightlike/OperatorAlgebras/TraceClass/Basic.lean - `OperatorAlgebras.TraceClass.IsTraceClass`,
    `OperatorAlgebras.TraceClass.trace`, `OperatorAlgebras.TraceClass.traceNorm`
48. Lightlike/OperatorAlgebras/TraceClass/HilbertSchmidt.lean -
    `OperatorAlgebras.TraceClass.HilbertSchmidt.IsHilbertSchmidt`,
    `OperatorAlgebras.TraceClass.HilbertSchmidt.tsum_diagonal_mul_eq_tsum_diagonal_swap`
49. Lightlike/OperatorAlgebras/TraceClass/GeneralProduct.lean -
    `OperatorAlgebras.TraceClass.isTraceClass_mul_of_isHilbertSchmidt`
50. Lightlike/OperatorAlgebras/TraceClass/TracePairingNorm.lean -
    `OperatorAlgebras.TraceClass.TraceClass.tracePairingLinearIsometry`
51. Lightlike/OperatorAlgebras/TraceClass/TracePairingSurjectivity.lean -
    `OperatorAlgebras.TraceClass.TraceClass.tracePairing_surjective_concrete`
52. Lightlike/OperatorAlgebras/TestsTraceClass.lean - `OperatorAlgebras.TraceClass.trace_rankOne_complex_one`,
    `OperatorAlgebras.TraceClass.isTraceClass_id_complex`,
    `OperatorAlgebras.TraceClass.not_isHilbertSchmidt_one`,
    `OperatorAlgebras.TraceClass.diag_weights_square_summable_not_summable`
53. Lightlike/OperatorAlgebras/TestsTraceClassDiag.lean - `OperatorAlgebras.TraceClass.diagOp`,
    `OperatorAlgebras.TraceClass.invDiag_isHilbertSchmidt`, `OperatorAlgebras.TraceClass.invDiag_not_isTraceClass`
54. Lightlike/OperatorAlgebras/ShaleDeterminant.lean - `OperatorAlgebras.det_four_add_of_posSemidef`,
    `OperatorAlgebras.uncertaintyMatrix`, `OperatorAlgebras.cayleyBlock`,
    `OperatorAlgebras.four_pow_mul_le_det_one_add` (the determinant bound from the uncertainty relation)
55. Lightlike/OperatorAlgebras/FockVacuumAverage.lean - `OperatorAlgebras.modeVec`,
    `OperatorAlgebras.integral_vacuumIntegrand`, `OperatorAlgebras.gaussZ_mul_norm_inner_sq_le` (the Gaussian
    average of the Weyl unitaries over finitely many modes bounds the vacuum overlap)
56. Lightlike/OperatorAlgebras/ShaleNecessity.lean - `OperatorAlgebras.covMatrix`,
    `OperatorAlgebras.posSemidef_uncertaintyMatrix`, `OperatorAlgebras.norm_inner_sq_mul_sqrt_le_one`,
    `OperatorAlgebras.shale_necessity_of_implements` (the proof of task T-OP2-P6)
57. Lightlike/OperatorAlgebras/FockContinuity.lean - `OperatorAlgebras.FockRep.continuous_W` (norm continuity
    of the Weyl unitaries of a Fock representation), `OperatorAlgebras.Bogoliubov.twist`
58. Lightlike/OperatorAlgebras/VacuumProjection.lean - `OperatorAlgebras.vacAvg` (the vacuum projection of
    finitely many modes), `OperatorAlgebras.vacAvg_symm`, `OperatorAlgebras.vacAvg_W_vacAvg`,
    `OperatorAlgebras.vacAvg_idem`, `OperatorAlgebras.exists_fixed_of_decreasing_projections`
59. Lightlike/OperatorAlgebras/ShaleSufficiency.lean - `OperatorAlgebras.det_le_exp_trace_sub_card`,
    `OperatorAlgebras.norm_sq_vacAvg_twist_Ω`, `OperatorAlgebras.shale_sufficiency_of_hilbertSchmidt` (the
    proof of task T-OP2-P7), `OperatorAlgebras.shale_criterion` (both directions)
60. Lightlike/OperatorAlgebras/TestsShale.lean - `OperatorAlgebras.Bogoliubov.neg`,
    `OperatorAlgebras.isHilbertSchmidt_id_betaPart`, `OperatorAlgebras.implements_neg`
61. Lightlike/OperatorAlgebras/TestsShaleSqueeze.lean - `OperatorAlgebras.Bogoliubov.squeeze`,
    `OperatorAlgebras.Bogoliubov.squeeze_betaPart`, `OperatorAlgebras.implements_squeeze`
62. Lightlike/OperatorAlgebras/Spectral/Unbounded/Cayley.lean - `OperatorAlgebras.Spectral.Unbounded.existsUnique_spectralMeasure_unbounded`,
    `OperatorAlgebras.Spectral.ProjectionValuedMeasure`
63. Lightlike/OperatorAlgebras/Spectral/StoneBridge.lean - `OperatorAlgebras.Spectral.Stone.generator_eq`,
    `OperatorAlgebras.Spectral.Stone.spectralGroup`, `OperatorAlgebras.Spectral.Stone.spectralGroup_generator`
64. Lightlike/OperatorAlgebras/MomentumAdjoint.lean - `OperatorAlgebras.adjoint_eq_primitive`,
    `OperatorAlgebras.mem_adjoint_of_primitive`, `OperatorAlgebras.mem_adjoint_iff_primitive`
65. Lightlike/OperatorAlgebras/MomentumBoundary.lean - `OperatorAlgebras.integral_conj_mul_add_eq`,
    `OperatorAlgebras.boundary_form_momentum`, `OperatorAlgebras.bv_linVec`, `OperatorAlgebras.mem_adjoint_iff_ac`
66. Lightlike/OperatorAlgebras/MomentumTheta.lean - `OperatorAlgebras.momentumZero_eq_closure`, `OperatorAlgebras.momentumTheta`,
    `OperatorAlgebras.momentumTheta_isSelfAdjoint`, `OperatorAlgebras.eq_momentumTheta_of_selfAdjoint`,
    `OperatorAlgebras.selfAdjoint_extensions_momentumZero`
67. Lightlike/OperatorAlgebras/TestsMomentumTheta.lean - `OperatorAlgebras.momentumTheta_zero_ne_pi`,
    `OperatorAlgebras.closure_ne_momentumTheta`
68. Lightlike/OperatorAlgebras/MomentumSpectrum.lean - `OperatorAlgebras.momentumTheta_planeWave`,
    `OperatorAlgebras.orthonormal_planeWave`, `OperatorAlgebras.eigenvalue_momentumTheta`,
    `OperatorAlgebras.eigenvector_momentumTheta`, `OperatorAlgebras.exists_momentumTheta_sub_eq`,
    `OperatorAlgebras.spectrum_momentumTheta`, `OperatorAlgebras.pointSpectrum_momentumTheta`
69. Lightlike/OperatorAlgebras/TestsMomentumSpectrum.lean - `OperatorAlgebras.theta_mem_spectrum`,
    `OperatorAlgebras.theta_add_pi_not_mem_spectrum`
70. Lightlike/OperatorAlgebras/FiniteCAR.lean - `OperatorAlgebras.IsCARRep`, `OperatorAlgebras.isCARRep_pauli`,
    `OperatorAlgebras.IsCARRep.tensor`, `OperatorAlgebras.jordanWigner`, `OperatorAlgebras.isCARRep_jordanWigner`,
    `OperatorAlgebras.carAnnihilation`, `OperatorAlgebras.carCreation`,
    `OperatorAlgebras.carAnnihilation_carCreation`, `OperatorAlgebras.carAnnihilation_jordanWigner_vacuum`
71. Lightlike/OperatorAlgebras/FermionFock.lean - `OperatorAlgebras.creation`, `OperatorAlgebras.annihilation`,
    `OperatorAlgebras.annihilation_creation_anticomm`, `OperatorAlgebras.annihilation_one`
72. Lightlike/OperatorAlgebras/FockJW.lean - `OperatorAlgebras.jwFockEquiv`, `OperatorAlgebras.jwFockEquiv_vacuum`,
    `OperatorAlgebras.jwFockEquiv_carCreation`, `OperatorAlgebras.jwFockEquiv_carAnnihilation`
73. Lightlike/OperatorAlgebras/CARUnique.lean - `OperatorAlgebras.IsCAROn`, `OperatorAlgebras.carVacuum`,
    `OperatorAlgebras.car_unitarily_equivalent_jordanWigner`, `OperatorAlgebras.isIrreducibleCAR_iff`,
    `OperatorAlgebras.car_irreducible_unitarily_equivalent`, `OperatorAlgebras.car_odd_unitarily_equivalent`,
    `OperatorAlgebras.isIrreducibleCAR_jordanWigner`
74. Lightlike/OperatorAlgebras/FockInner.lean - `OperatorAlgebras.fockInner`, `OperatorAlgebras.fockInner_fockVec`,
    `OperatorAlgebras.fockInner_creation`, `OperatorAlgebras.fockInner_unique`, `OperatorAlgebras.fock_irreducible`
75. Lightlike/OperatorAlgebras/CCRJoint.lean - `OperatorAlgebras.CCRRep.continuous_W`,
    `OperatorAlgebras.continuous_apply_of_isometries`
76. Lightlike/OperatorAlgebras/GaussKernel.lean - `OperatorAlgebras.integral_gauss_kernel`,
    `OperatorAlgebras.symp_eq_real_inner`
77. Lightlike/OperatorAlgebras/GaussAvg.lean - `OperatorAlgebras.gaussAvg`, `OperatorAlgebras.gaussAvg_W_gaussAvg`,
    `OperatorAlgebras.exists_gaussAvg_ne_zero`
78. Lightlike/OperatorAlgebras/StoneVN.lean - `OperatorAlgebras.vnProj`, `OperatorAlgebras.inner_W_of_vnProj`,
    `OperatorAlgebras.stone_von_neumann`, `OperatorAlgebras.isIrreducible_iff_finrank_vnRange`,
    `OperatorAlgebras.stone_von_neumann_irreducible`

## References

1. B. C. Hall, *Quantum Theory for Mathematicians*, Graduate Texts in Mathematics 267, Springer, 2013,
   Chapter 10 (Stone's theorem).
2. O. Bratteli and D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, 2nd ed.,
   Springer, 1997, Chapter 5, after D. Shale, *Linear symmetries of free boson fields*, Trans. Amer. Math.
   Soc. 103 (1962) 149.
3. Math 7334 lecture notes, Georgia Tech (Spring 2017), Section 4: The Theorem of Hille and Yosida concerning semi-groups, Theorem 1.9, https://loss.math.gatech.edu/17SPRINGTEA/7334/NOTES/section4hilleyosida.pdf.
4. G. Teschl, *Mathematical Methods in Quantum Mechanics*, Graduate Studies in Mathematics 99, American Mathematical
   Society, 2009 (online edition), Theorem 3.7 (spectral theorem). The Lean files are ported from physicslib4
   (github.com/physicslib/physicslib4, Apache-2.0).
5. G. Bonneau, J. Faraut and G. Valent, *Self-adjoint extensions of operators and the teaching of quantum
   mechanics*, arXiv:quant-ph/0103153, Appendix A.3 and Section 5.3, eqs. (14) and (15).
6. J. Dereziński, *Introduction to representations of the canonical commutation and anticommutation
   relations*, in *Large Coulomb Systems*, Lecture Notes in Physics 695, Springer, 2006, Theorem 10 and
   Corollary 2.
7. J. Dereziński, *Introduction to representations of the canonical commutation and anticommutation
   relations*, Theorem 4 and Corollary 1; M. Faulhuber, *Time-Frequency Analysis*, lecture notes, 2022,
   Section 7.3.1 (von Neumann's proof).
