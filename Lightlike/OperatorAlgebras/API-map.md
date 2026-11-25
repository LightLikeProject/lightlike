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
Necessity goes through the determinant bound from the uncertainty matrix [54], the Gaussian average of the Weyl
unitaries over finitely many modes [55] and the matrix of the quadratic form `f ↦ ‖T f‖²` on finitely many modes
[56]; sufficiency goes
through the norm continuity of the Weyl unitaries [57], the vacuum projection of finitely many modes [58] and the
bound `det ≤ exp (tr - n)` [59]. The parity `f ↦ -f` is implemented in every Fock representation [60], a one-mode squeezing is implemented
[61], and the same squeezing on every mode of `ℓ²` has an antilinear part that is not Hilbert–Schmidt and is not
implemented [64].
In one mode the squeezing has `|α|² - |β|² = 1` and the dilation `f ↦ 2 f` is not symplectic [4]. A map with `‖B f‖ = c ‖f‖`, `c > 0`, is not Hilbert–Schmidt when a Hilbert basis is infinite [4]. On `L²(ℝ)` translation `ψ(x + t)` is a strongly continuous unitary group [5], and its generator is `-i d/dx` on `C²` functions with compact support, not `+i d/dx` [6]. On `L²(0, 1)` the operator `-i d/dx` on the `C²` functions supported inside `(0, 1)` is given by its graph [7]. The deficiency spaces of an operator are the kernels of the adjoint minus `±i`, and a self-adjoint operator has none [8]. The
Fock space itself is not built here, and a Fock representation is characterized by its vacuum. The
unbounded spectral theorem is not in Mathlib; it is ported from physicslib4: every self-adjoint operator has a unique
projection-valued measure [117] on the Borel sets of `ℝ` whose spectral integral of `λ` is the operator {4} [62]; the group `e^{itA}` of a self-adjoint operator is a `UnitaryGroup` whose generator is `A` [63]. On a matrix algebra the modular flow of the faithful state `Tr (e^{-H} ·)` is `a ↦ e^{-izH} a e^{izH}` and the state is KMS at inverse temperature `1` for it {10} [91]; the flow is a multiplicative one-parameter group that leaves the state invariant [91]; the Tomita operator `S` is an antilinear involution with `S (a ρ^{1/2}) = a† ρ^{1/2}` and the modular operator `Δ y = ρ y ρ⁻¹` satisfies `Δ = S† S` {10} [91]; the modular state is KMS at inverse temperature `1` in the sense of the KMS condition of finite quantum systems, and a diagonal qubit state that is not Gibbs fails that condition [91]. Stone's theorem and Shale's criterion are [TODO] here.

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

A strongly continuous contraction semigroup on a Banach space has a generator, the limit of the difference quotients on the vectors where it exists, a partially defined linear map [116]. A densely defined operator `A` with `λ - A` bounded below by `λ` and surjective for every `λ > 0` is the generator of a contraction semigroup (the generation direction of the Hille–Yosida theorem) [42] {3}: the resolvent `R(λ) = (λ - A)⁻¹` has norm at most `λ⁻¹`, the Yosida approximants `λ² R(λ) - λ` give contractions `exp (t (λ² R(λ) - λ))` that converge, by a Cauchy estimate and the density of the domain, to a semigroup whose generator contains `A`, and a dissipative generator with `λ - A` surjective equals `A`. Checks: the trivial semigroup is a contraction semigroup, the theorem applies to `A = 0`, and `A = id` fails the lower bound at `λ = 1` [43]. The converse holds as well, so the two form the equivalence of the Hille–Yosida theorem for contraction semigroups [44] {3}: the orbits `t ↦ S t x` are continuous for all times `t ≥ 0` by the semigroup law and continuity at `0` [45], the averages `t⁻¹ ∫₀ᵗ S s x ds` lie in the domain of the generator and converge to `x`, which makes the domain dense [45], the resolvent `∫₀^∞ e^{-λ t} S t y dt` is a Bochner integral that lies in the domain with `(λ - A) R(λ) y = y` [46], and `norm_dissip` gives the lower bound [44].

A bounded operator on a complex Hilbert space is trace class when the diagonal sum `∑ ⟪eᵢ, |T| eᵢ⟫` converges in a Hilbert basis, and the trace and the trace norm do not depend on the basis [47]. The Hilbert-Schmidt operators, those with `∑ ‖S eᵢ‖² < ∞` in one basis, are two-sided ideal elements, and the diagonal sums of `R S` and `S R` for Hilbert-Schmidt `R`, `S` agree (cyclicity of the trace) [48]; a product of two Hilbert-Schmidt operators is trace class [49]. The trace pairing `A ↦ Tr (A ·)` is an isometry of the bounded operators into the dual of the trace class [50], and every continuous functional on the trace class is a trace pairing, so the dual of the trace class is the bounded operators [51]. The trace of the rank-one operator on `ℂ` is `1`, and every operator on a finite-dimensional space is trace class; the identity of an infinite-dimensional Hilbert space is not Hilbert-Schmidt [52]. The diagonal operator with eigenvalues `1 / (n + 1)` on `ℓ²(ℕ)` is Hilbert-Schmidt and not trace class [53]. This layer is ported from Physlib with attribution; the duality between the compact operators and the trace class is not covered.

For a Hilbert basis `{eᵢ}`, `∑ᵢ |⟪eᵢ, y⟫|² = ‖y‖²` (Parseval), the Hilbert-Schmidt square sum `∑ᵢ ‖S eᵢ‖²` of a bounded `S` in one basis equals that of `S⋆` in a second basis, and so it converges in every Hilbert basis to the same sum once it converges in one [39]. A Bogoliubov transformation is `T f = α f + β f` with `α` complex-linear and `β` antilinear, and the symplectic condition gives `‖α e‖² - ‖β e‖² = ‖e‖²` and `4 ‖β e‖² = ‖T e‖² + ‖T (i e)‖² - 2 ‖e‖²`; `α` is a bounded operator with `α†α - 1` positive and `‖√(α†α - 1) e‖² = ‖β e‖²` [40]. Hence the antilinear part is Hilbert-Schmidt as soon as `∑ᵢ ‖β bᵢ‖²` converges in one Hilbert basis, and in particular when the finite sums `∑_{i ∈ s} (‖T bᵢ‖² + ‖T (i bᵢ)‖² - 2)` are bounded, the quantity that the vacuum projections onto finitely many modes control in the necessity part of Shale's criterion [41].

On `L²(0, 1)`, a vector lies in the domain of the adjoint of `-i d/dx` (on the `C²` test functions) iff it is a primitive `c + ∫₀ˣ g` with `g ∈ L²`, equivalently iff it agrees almost everywhere with an absolutely continuous function whose derivative is in `L²`, and then the adjoint is `-i g` [65], [66]. Its continuous representative has boundary values `y(0)`, `y(1)`, and integration by parts for absolutely continuous functions gives the boundary form `⟪A† y, z⟫ - ⟪y, A† z⟫ = i (conj y(1) z(1) - conj y(0) z(0))`; the affine functions give every pair of boundary values [66]. The closure of the momentum is the adjoint on the vectors with zero boundary values, the restriction `P_θ` of the adjoint to `y(1) = e^{iθ} y(0)` is self-adjoint, and every self-adjoint extension of the momentum is a `P_θ` {5}, [67]. The constant `1` lies in the periodic domain and not in the antiperiodic one, so `P_0 ≠ P_π`, and the closure is not self-adjoint [68].

The plane waves `e^{i(θ + 2πn)x}`, `n ∈ ℤ`, lie in the domain of `P_θ` and are orthonormal eigenvectors with eigenvalue `θ + 2πn`; an eigenvector of `P_θ` with eigenvalue `μ ∈ ℂ` has the continuous representative `y(0) e^{iμx}`, so `μ = θ + 2πn` and the eigenspaces are one-dimensional; off `θ + 2πℤ` the resolvent equation is solved explicitly, so the spectrum of `P_θ`, in Physlib's sense, is `θ + 2πℤ` and equals the point spectrum {5}, [69]. `θ` is in the spectrum of `P_θ` and `θ + π` is not [70].

A Weyl system of a symplectic vector space `(V, ω)` is a map `W` into a unital star algebra with `W(0) = 1`, `W(-φ) = W(φ)*` and `W(φ) W(ψ) = e^{-iω(φ,ψ)/2} W(φ + ψ)`; its elements are unitary and linearly independent, the independence by induction on the number of terms with the conjugations `W(ψ) W(χ) W(-ψ) = e^{-iω(ψ,χ)} W(χ)` [71]. The operators `(W(φ)F)(ψ) = e^{iω(φ,ψ)/2} F(φ + ψ)` on `ℓ²(V)`, or on any Hilbert space with a Hilbert basis indexed by `V`, form a Weyl system, and the closed star subalgebra they generate is the CCR algebra, a C*-algebra {6} [71]. In a C*-algebra the spectrum of `W(χ)`, `χ ≠ 0`, is the whole unit circle, so `‖W(φ) - W(ψ)‖ = 2` for `φ ≠ ψ`, and a C*-algebra with a Weyl system of a nonzero symplectic space, the CCR algebra among them, is not separable [71]. The Weyl unitaries of a representation of the CCR over a complex inner product space form a Weyl system of `σ = Im⟪·,·⟫` [71]. In the CCR algebra of `ℝ²` with `ω((a, b), (c, d)) = ad - bc` the elements `W(e₁)` and `W(e₂)` do not commute [72].
A representation of the CAR over `ℝᵐ` is a family of self-adjoint operators with `φ a φ b + φ b φ a = 2 δ_ab`; the Pauli matrices are one over `ℝ³`, the tensor product construction joins two, and the Jordan-Wigner operators `σ₃ ⊗ ⋯ ⊗ σ₃ ⊗ σ₁,₂ ⊗ 1 ⊗ ⋯ ⊗ 1` are one over `ℝ²ⁿ`, whose annihilation operators `aⱼ = (φ_{2j} + i φ_{2j+1}) / 2` satisfy `aᵢ aⱼ* + aⱼ* aᵢ = δᵢⱼ` and kill the empty configuration [73]. On the exterior algebra, left multiplication `a*(v)` and contraction `a(d)` satisfy the CAR with the vacuum `1` [74], and `|x⟩ ↦ ∏_{xⱼ = 1} eⱼ` is a linear isomorphism `⊗ⁿℂ² ≅ Λ(ℂⁿ)` that intertwines the Jordan-Wigner creation and annihilation operators with these [75]. The Fock inner product on `Λ(ℂⁿ)`, for which the configuration vectors are orthonormal, is the only sesquilinear form with `⟪1, 1⟫ = 1` for which `a*(eⱼ)` and `a(eⱼ*)` are mutually adjoint, and the Fock representation on it is irreducible [77]. Every representation over `ℝ²ⁿ` is unitarily equivalent to the Jordan-Wigner one tensored with the identity of its vacuum space `K = ⋂ⱼ ker aⱼ`, it is irreducible iff `K` is one-dimensional, two irreducible ones are unitarily equivalent, and over `ℝ²ⁿ⁺¹` the last generator becomes `Iₙ ⊗ T` for a self-adjoint unitary `T` of `K` {7}; the proof uses the ordered creation words `c₀^{x₀} ⋯ c_{n-1}^{x_{n-1}}` on `K`, their orthonormality and the resolution of the identity `∑ₓ cWord x · a₀c₀ ⋯ · aWord x = 1` [76].

For a finite-dimensional `h`, the Weyl unitaries are jointly strongly continuous [78]. The Gaussian average `P = ∫ e^{-‖z‖²/4} W z dz` satisfies `P W f P = (2π)^d e^{-‖f‖²/4} P` (von Neumann's identity, from the Gaussian kernel integral [79]), so `P₀ = (2π)^{-d} P` is an orthogonal projection, nonzero on a nonzero space by Fourier inversion, and a unit vector of its range has the Fock vacuum expectation [80]. Hence every representation of the Weyl relations of `h` is the Hilbert sum of Fock representations over an orthonormal basis of the range of `P₀`, it is irreducible iff that range is one-dimensional, and an irreducible one is unitarily equivalent to the Fock representation: the Stone-von Neumann theorem {7} {8} [81].

A map `y ↦ W y` into the unitaries with the Weyl relations is regular as soon as it has a cyclic quasi-free vector `Ψ`, `⟪Ψ, W y Ψ⟫ = exp(-η(y, y)/4)` [82]; then `Ψ` lies in the domain of every field operator `φ(y)`, the generator of `t ↦ W(t y)`, with `⟪φ(y₁)Ψ, φ(y₂)Ψ⟫ = ½(η(y₁, y₂) + i σ(y₁, y₂))` and `|σ(y₁, y₂)| ≤ η(y₁, y₁)^{1/2} η(y₂, y₂)^{1/2}` {7}; the Fock vacuum is quasi-free with `η = Re⟪·,·⟫` [83]. For a quasi-free vector the generating function `t ↦ ⟪Ψ, W(t₀y₀) ⋯ W(tₙ₋₁yₙ₋₁) Ψ⟫` is the exponential of a quadratic form, and its n-point functions, `(-i)ⁿ` times the mixed derivative at `0`, are the sums over pairings of the two-point functions (Wick's formula in generating-function form, from Isserlis' formula for `exp` of a quadratic form) [86].

For a complex Hilbert space `Z` with a Hilbert basis indexed by a linearly ordered `ι`, a Hilbert space with a Hilbert basis `B` indexed by the finite subsets of `ι` is the fermionic Fock space: the creation operators `a*(eⱼ) B S = ±B (S ∪ {j})` and their adjoints satisfy the CAR, `a*(w) = ∑ⱼ ⟪eⱼ, w⟫ a*(eⱼ)` has norm at most `‖w‖`, and the field operators `φ(w) = a*(w) + a(w)` are self-adjoint with `φ(w) φ(w') + φ(w') φ(w) = 2 Re⟪w, w'⟫` and form an irreducible representation [84] {7}; the annihilation operators kill the vacuum and the model `ℓ²(Finset ι)` is checked in [85].

In a Fock representation, a contraction `p` of `h` has a second quantization `Γ(p)`, the contraction with `Γ(p) W(f) Ω = exp((‖p f‖² - ‖f‖²)/4) W(p f) Ω`, from the positive semidefinite kernel `exp(⟪f, g⟫/2) - exp(⟪p f, p g⟫/2)` (Schur's product theorem); it is functorial, `Γ(p)* = Γ(p*)`, unitary iff `p` is, and for a unitary `U` the unique implementer of `U` with `Γ(U) Ω = Ω`, every implementer being a phase times `Γ(U)`; a strongly continuous unitary group `U(t)` gives the strongly continuous group `Γ(U(t))`, whose generator is `dΓ` [87] {7}; `Γ(0)` is the vacuum projection [88].

For finitely many modes, `dΓ(h) = ∑ᵢⱼ hᵢⱼ aᵢ* aⱼ` in any algebra whose `aᵢ`, `aᵢ*` satisfy the CAR or the CCR has `[dΓ(h), a*(w)] = a*(hw)`, `[dΓ(h), a(w)] = -a(h* w)` and `[dΓ(h₁), dΓ(h₂)] = dΓ([h₁, h₂])` [111] [112], and Physlib's bosonic ladder systems are such algebras [113]. The same commutators hold for a finite-rank `h = ∑ₖ |uₖ⟩⟨vₖ|` on any inner product space, with `dΓ(h) = ∑ₖ a*(uₖ) a(vₖ)` [114]. On the coordinate tensor power `ℓ²(Fin n → ι)` of a Hilbert space with a Hilbert basis indexed by `ι`, `h` acting on one slot has norm at most `‖h‖`, and `dΓₙ(h) = ∑ⱼ 1 ⊗ ⋯ ⊗ h ⊗ ⋯ ⊗ 1` has norm at most `n ‖h‖` [115]. On the fermionic Fock space `ℓ²(Finset ι)` the `n`-particle vectors embed isometrically into the coordinate tensor power by `Eₙ ψ (f) = (n!)^{-1/2} sign(f) ψ(image f)`, the sign of the permutation sorting `f`, and `dΓₙ(h) = Eₙ* (∑ⱼ hⱼ) Eₙ` has norm at most `n ‖h‖` for every bounded `h`; with `Eₙ Eₙ* = A` and `Eₙ* Eₙ = 1` on the `n`-particle vectors, every bounded `h` there has `[dΓ(h), a*(w)] = a*(hw)`, `[dΓ(h), a(w)] = -a(h* w)`, `[dΓ(h₁), dΓ(h₂)] = dΓ([h₁, h₂])` and `dΓ(h)* = dΓ(h*)` on each particle sector [118]. On the bosonic and fermionic Fock spaces `Γⁿ_{s/a}(Z) = Θ_{s/a} ⊗ⁿZ` of any Hilbert space, with `a*(w) = √(n+1) Θ_{s/a}(w ⊗ ·)` and `a(w) = a*(w)*`, the same three commutators hold for every bounded `h`, as identities of operators between consecutive tensor powers [119].

For a Hamiltonian given by a Hilbert basis and real eigenvalues `λₙ` with `∑ e^{-βλₙ} < ∞` (every `H` with a trace-class `e^{-βH}` has this form {4}), the Gibbs state `ω(A) = ∑ e^{-βλₙ} ⟪bₙ, A bₙ⟫ / Z` is a state invariant under `τᵗ(A) = e^{itH} A e^{-itH}`, and the double series `F_{A,B}(z) = ∑ₘₙ e^{-βλₘ} ⟪bₘ, A bₙ⟫ ⟪bₙ, B bₘ⟫ e^{iz(λₙ - λₘ)} / Z`, dominated on the strip `0 ≤ Im z ≤ β` by `|⟪bₘ, A bₙ⟫| |⟪bₙ, B bₘ⟫| (e^{-βλₘ} + e^{-βλₙ})`, is bounded and continuous there, analytic inside, with `F(t) = ω(A τᵗ(B))` and `F(t + iβ) = ω(τᵗ(B) A)`: the KMS condition {9} [89]. The oscillator `λₙ = n` is an example for every `β > 0`, and at `β = 0` the partition sum diverges [90].

The states of `C(X)` for a compact Hausdorff `X` are the positive linear functionals with `ω 1 = 1`, and the pure ones are the extreme points of this convex set. A pure state is multiplicative: for `0 ≤ g ≤ 1` it splits as `ω(g) ω(· g)/ω(g) + ω(1 - g) ω(· (1 - g))/ω(1 - g)`, so `ω(f g) = ω(f) ω(g)`; a multiplicative state is continuous, its kernel is a closed maximal ideal, so it is the evaluation at a point; and every evaluation is pure {11} [92]. On `C(Bool)` the average of the two evaluations is a mixed state [93]. For a locally compact Hausdorff `X`, a state of `C₀(X)` (positive, of norm one) extends to the state `F ↦ ω(F - F(∞)) + F(∞)` of `C(X̃)` on the one-point compactification, a pure one to a pure one, so the pure states of `C₀(X)` are again the evaluations at the points of `X` [94].

On a compact metric space the couplings of two probability measures are the probability measures on the product with these marginals, the product measure among them, and `W₁` is the infimum of the transport costs `∫ d dπ`; for every coupling and `1`-Lipschitz `u`, `∫ u dμ - ∫ u dν ≤ ∫ d dπ`, the easy half of Kantorovich-Rubinstein duality, and `W₁(δₓ, δ_y) = d(x, y)` {12} [95]. The diagonal coupling gives `W₁(μ, μ) = 0` [96].

For a continuous cost `h` on the product of a compact metric space with itself there is an optimal coupling, and its cost is `sup {∫ f dμ + ∫ g dν | f(x) + g(y) ≤ h(x, y)}` over continuous `f`, `g` {12} [97]; the proof goes through the Hahn-Banach theorem for the sublinear functional `ω(k) = inf {∫ f dμ + ∫ g dν | k ≤ f ⊕ g}` and the Riesz-Markov-Kakutani theorem. For a separable cost `a(x) + b(y)` the dual value is `∫ a dμ + ∫ b dν` [98].

Kantorovich-Rubinstein duality: on a compact metric space `W₁(μ, ν) = sup {∫ u dμ - ∫ u dν | u 1-Lipschitz}`, and the infimum defining `W₁` is attained {12} [99]; the `c`-transform `u(x) = inf_y (d(x, y) - g(y))` of a dual pair `(f, g)` is `1`-Lipschitz with `f ≤ u ≤ -g` [99]. For Dirac measures the supremum is `d(x, y)`, and `2`-Lipschitz tests exceed `W₁` [100].
A compact symmetric operator `T` on a real or complex Hilbert space has a Hilbert basis of eigenvectors with real eigenvalues, assembled from Hilbert bases of the eigenspaces, whose sum is dense, and `T x = ∑ᵢ μᵢ ⟪bᵢ, x⟫ bᵢ` in it; only finitely many eigenvalues have `‖μ‖ ≥ ε`, since unit eigenvectors to distinct eigenvalues are orthonormal and their images are then `ε` apart inside a compact set, so the eigenvalues and the spectrum are countable [101]. The identity of `ℓ²(ℕ)` is symmetric, not compact, and has an infinite-dimensional eigenspace, and `0` is in the spectrum of the compact self-adjoint `diag(1/(n+1))` without being an eigenvalue [102]. A Hilbert-Schmidt operator is the norm limit of its finite sections `x ↦ ∑_{i ∈ F} ⟪bᵢ, x⟫ K bᵢ` and so is compact [103].

A compact operator `K` has a canonical form `K x = ∑ⱼ sⱼ ⟪φⱼ, x⟫ φ'ⱼ`, `K* x = ∑ⱼ sⱼ ⟪φ'ⱼ, x⟫ φⱼ` with orthonormal `φ`, `φ'` and positive singular values `sⱼ`: from a Hilbert basis of eigenvectors of the compact symmetric `K*K`, `sⱼ = √μⱼ` on the eigenvalues `μⱼ > 0` and `φ'ⱼ = sⱼ⁻¹ K φⱼ`; only finitely many `sⱼ` exceed any `ε > 0`, and `‖K‖` is the largest of them. For `μ ≠ 0` the `μ`-eigenspace of `K*K` is spanned by the `φⱼ` with `sⱼ² = μ` and has dimension `#{j | sⱼ² = μ}`, and likewise for `KK*` with the `φ'ⱼ` [104]. The zero operator has no singular values and a nonzero operator has one [105].

The Schatten sum `‖K‖_p^p` is the supremum of `∑ₖ |⟪ψₖ, K ϕₖ⟫|^p` over pairs of finite orthonormal families; for every canonical form and `p ≥ 1` it equals `∑ⱼ sⱼ^p`, by Hölder with the weights `|⟪φⱼ, ϕₖ⟫|²` and Cauchy-Schwarz twice on one side and the orthonormal families of the canonical form on the other, and it bounds `‖K‖^p` and is unchanged by the adjoint [106]. For a compact `K` the square sum `∑ᵢ ‖K bᵢ‖²` in every Hilbert basis is `‖K‖₂²`, so the Hilbert-Schmidt operators are the compact ones with `‖K‖₂ < ∞` [107]; the trace norm of a product of two Hilbert-Schmidt operators is at most the product of their Hilbert-Schmidt norms, `|K|` acts on an eigenvector of `K*K` with eigenvalue `μ` by `√μ`, and the trace-class operators are the compact ones with `‖K‖₁ < ∞` [108]. The Schatten norms satisfy the triangle inequality (Minkowski on the finite sums), are homogeneous and definite, pass to norm limits, and a Cauchy sequence of compact operators converges in them [109]. The diagonal operator `diag(1/(n+1))` is in `J₂` and not in `J₁` [110].

Further results of this area in the results catalogue:
For a finite quantum system with Hamiltonian H, a state is KMS at inverse temperature beta iff it is the
Gibbs state e^{-beta H} / tr e^{-beta H} [120]. A faithful state of a finite matrix algebra is KMS at
inverse temperature beta = -1 for its modular dynamics, generated by log rho [121]. OP2 in one place: a
Fock representation exists on every complex Hilbert space, a Bogoliubov transformation is implemented
iff its antilinear part is Hilbert-Schmidt (Shale), |alpha|^2 - |beta|^2 = 1 for one mode, and a
constant |beta| on l^2(N) is not implementable [122]. A quasi-free state of the Weyl algebra of a
finite-dimensional symplectic space with a compatible complex structure (J^2 = -1, eta J-invariant and
positive definite, omega(x,y) = -eta(x,Jy)) is pure; the degenerate-omega case factors through a
surjection onto such a space [123]. The Sorkin-Johnston state of a finite causal set is pure: |iD| is
the positive square root of -D^2, the Pauli-Jordan matrix is a(C - C^T) for the causal matrix C, and the
quasi-free state of (D, |iD|) is pure for every a [124]. Fermionic Bogoliubov transformations of the
CAR: b = alpha a + beta c has anticommutators alpha alpha* + beta beta* and alpha beta^T + beta alpha^T;
under alpha alpha* + beta beta* = 1 and alpha beta^T + beta alpha^T = 0 the CAR is preserved, the
transformation is invertible, the transformed Majorana family of an irreducible CAR representation is an
irreducible CAR representation, hence unitarily implemented (finite dimensions) [125]. Bogoliubov vacua
of the CAR: a vector killed by every transformed annihilation operator has two-point functions <a_i Psi,
a_j Psi> = (beta* beta)_ij |Psi|^2, <c_i Psi, c_j Psi> = (alpha* alpha)_ij |Psi|^2, <a_i Psi, c_j Psi> =
(beta* alpha)_ij |Psi|^2; it exists for the Jordan-Wigner representation and is unique up to a scalar
[126]. Fermionic Shale in infinitely many modes, sufficiency for a small antilinear part: a surjective
real-linear map R of a Hilbert space Z preserving Re of the inner product, whose antilinear part beta
satisfies sum over every finite set of |beta e_k|^2 at most h < 1, is implemented by a unitary of the
fermionic Fock space, U phi(w) = phi(R w) U; and for any R, a unit vector killed by the transformed
annihilation operators gives such a unitary [127]. The Sorkin-Johnston state of a finite causal set is
pure for the retarded matrix K_R = a M (1 - a b M)^-1 (the link matrix in four dimensions, the causal
matrix in two, any mass), and 1 - a b M is invertible because M is supported on the causal order [128].
Wick's theorem for fermionic fields on a vacuum for every number of fields: the vacuum expectation of a
product of split fields (annihilation part killing the vacuum, creation part killed by the functional,
scalar anticommutators with the annihilation parts) is the Pfaffian-type recursion of the pairings
[129]. Wick's theorem for the CAR fields of a Bogoliubov vacuum, for every number of fields: the vacuum
expectation of a product of linear combinations of the transformed operators b, b* is the Pfaffian
recursion of the pairings, whose two-point value is the sum of u_i v'_i [130].

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
    `OperatorAlgebras.ContractionSemigroup.norm_dissip` (the proof of task T-OP1-P7)
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
62. Lightlike/OperatorAlgebras/Spectral/Unbounded/Cayley.lean - `OperatorAlgebras.Spectral.Unbounded.existsUnique_spectralMeasure_unbounded`
63. Lightlike/OperatorAlgebras/Spectral/StoneBridge.lean - `OperatorAlgebras.Spectral.Stone.generator_eq`,
    `OperatorAlgebras.Spectral.Stone.spectralGroup`, `OperatorAlgebras.Spectral.Stone.spectralGroup_generator`
64. Lightlike/OperatorAlgebras/TestsShaleInfinite.lean - `OperatorAlgebras.Bogoliubov.squeezeConj`,
    `OperatorAlgebras.Bogoliubov.squeezeConj_norm_betaPart_sq`, `OperatorAlgebras.squeezeEllTwo`,
    `OperatorAlgebras.not_isHilbertSchmidt_squeezeEllTwo`, `OperatorAlgebras.not_implements_squeezeEllTwo`
    (the wrong-input control: a squeezing of infinitely many modes is not implemented)
65. Lightlike/OperatorAlgebras/MomentumAdjoint.lean - `OperatorAlgebras.adjoint_eq_primitive`,
    `OperatorAlgebras.mem_adjoint_of_primitive`, `OperatorAlgebras.mem_adjoint_iff_primitive`
66. Lightlike/OperatorAlgebras/MomentumBoundary.lean - `OperatorAlgebras.integral_conj_mul_add_eq`,
    `OperatorAlgebras.boundary_form_momentum`, `OperatorAlgebras.bv_linVec`, `OperatorAlgebras.mem_adjoint_iff_ac`
67. Lightlike/OperatorAlgebras/MomentumTheta.lean - `OperatorAlgebras.momentumZero_eq_closure`, `OperatorAlgebras.momentumTheta`,
    `OperatorAlgebras.momentumTheta_isSelfAdjoint`, `OperatorAlgebras.eq_momentumTheta_of_selfAdjoint`,
    `OperatorAlgebras.selfAdjoint_extensions_momentumZero`
68. Lightlike/OperatorAlgebras/TestsMomentumTheta.lean - `OperatorAlgebras.momentumTheta_zero_ne_pi`,
    `OperatorAlgebras.closure_ne_momentumTheta`
69. Lightlike/OperatorAlgebras/MomentumSpectrum.lean - `OperatorAlgebras.momentumTheta_planeWave`,
    `OperatorAlgebras.orthonormal_planeWave`, `OperatorAlgebras.eigenvalue_momentumTheta`,
    `OperatorAlgebras.eigenvector_momentumTheta`, `OperatorAlgebras.exists_momentumTheta_sub_eq`,
    `OperatorAlgebras.spectrum_momentumTheta`, `OperatorAlgebras.pointSpectrum_momentumTheta`
70. Lightlike/OperatorAlgebras/TestsMomentumSpectrum.lean - `OperatorAlgebras.theta_mem_spectrum`,
    `OperatorAlgebras.theta_add_pi_not_mem_spectrum`
71. Lightlike/OperatorAlgebras/WeylAlgebra.lean - `OperatorAlgebras.IsSymplecticForm`, `OperatorAlgebras.IsWeylSystem`,
    `OperatorAlgebras.IsWeylSystem.mem_unitary`, `OperatorAlgebras.IsWeylSystem.linearIndependent`,
    `OperatorAlgebras.weylOp`, `OperatorAlgebras.isWeylSystem_weylOp`, `OperatorAlgebras.ccrAlgebra`,
    `OperatorAlgebras.ccrW`, `OperatorAlgebras.isWeylSystem_ccrW`, `OperatorAlgebras.symplecticForm`,
    `OperatorAlgebras.CCRRep.isWeylSystem`, `OperatorAlgebras.IsWeylSystem.mem_spectrum`, `OperatorAlgebras.IsWeylSystem.norm_sub`,
    `OperatorAlgebras.IsWeylSystem.not_separableSpace`, `OperatorAlgebras.ccrAlgebra_not_separableSpace`,
    `OperatorAlgebras.IsWeylSystem.conj_sum`, `OperatorAlgebras.IsWeylSystem.norm_coeff_zero_le`, `OperatorAlgebras.twMul`,
    `OperatorAlgebras.twNormSq`, `OperatorAlgebras.IsWeylSystem.linearCombination_twMul`,
    `OperatorAlgebras.IsWeylSystem.linearCombination_twNormSq`, `OperatorAlgebras.twNormSq_apply_zero`,
    `OperatorAlgebras.IsWeylSystem.norm_apply_zero_le`, `OperatorAlgebras.IsWeylSystem.sum_norm_sq_le`
72. Lightlike/OperatorAlgebras/TestsWeylAlgebra.lean - `OperatorAlgebras.IsWeylSystem.mul_twist`,
    `OperatorAlgebras.IsWeylSystem.mul_ne_mul`, `OperatorAlgebras.not_isSymplecticForm_zero`,
    `OperatorAlgebras.weylOp_ell2Basis_apply`, `OperatorAlgebras.ccrW_mul_ne` (the CCR algebra of `ℝ²` is not
    commutative)
73. Lightlike/OperatorAlgebras/FiniteCAR.lean - `OperatorAlgebras.IsCARRep`, `OperatorAlgebras.isCARRep_pauli`,
    `OperatorAlgebras.IsCARRep.tensor`, `OperatorAlgebras.jordanWigner`, `OperatorAlgebras.isCARRep_jordanWigner`,
    `OperatorAlgebras.carAnnihilation`, `OperatorAlgebras.carCreation`,
    `OperatorAlgebras.carAnnihilation_carCreation`, `OperatorAlgebras.carAnnihilation_jordanWigner_vacuum`
74. Lightlike/OperatorAlgebras/FermionFock.lean - `OperatorAlgebras.creation`, `OperatorAlgebras.annihilation`,
    `OperatorAlgebras.annihilation_creation_anticomm`, `OperatorAlgebras.annihilation_one`
75. Lightlike/OperatorAlgebras/FockJW.lean - `OperatorAlgebras.jwFockEquiv`, `OperatorAlgebras.jwFockEquiv_vacuum`,
    `OperatorAlgebras.jwFockEquiv_carCreation`, `OperatorAlgebras.jwFockEquiv_carAnnihilation`
76. Lightlike/OperatorAlgebras/CARUnique.lean - `OperatorAlgebras.IsCAROn`, `OperatorAlgebras.carVacuum`,
    `OperatorAlgebras.car_unitarily_equivalent_jordanWigner`, `OperatorAlgebras.isIrreducibleCAR_iff`,
    `OperatorAlgebras.car_irreducible_unitarily_equivalent`, `OperatorAlgebras.car_odd_unitarily_equivalent`,
    `OperatorAlgebras.isIrreducibleCAR_jordanWigner`
77. Lightlike/OperatorAlgebras/FockInner.lean - `OperatorAlgebras.fockInner`, `OperatorAlgebras.fockInner_fockVec`,
    `OperatorAlgebras.fockInner_creation`, `OperatorAlgebras.fockInner_unique`, `OperatorAlgebras.fock_irreducible`
78. Lightlike/OperatorAlgebras/CCRJoint.lean - `OperatorAlgebras.CCRRep.continuous_W`,
    `OperatorAlgebras.continuous_apply_of_isometries`
79. Lightlike/OperatorAlgebras/GaussKernel.lean - `OperatorAlgebras.integral_gauss_kernel`,
    `OperatorAlgebras.symp_eq_real_inner`
80. Lightlike/OperatorAlgebras/GaussAvg.lean - `OperatorAlgebras.gaussAvg`, `OperatorAlgebras.gaussAvg_W_gaussAvg`,
    `OperatorAlgebras.exists_gaussAvg_ne_zero`
81. Lightlike/OperatorAlgebras/StoneVN.lean - `OperatorAlgebras.vnProj`, `OperatorAlgebras.inner_W_of_vnProj`,
    `OperatorAlgebras.stone_von_neumann`, `OperatorAlgebras.isIrreducible_iff_finrank_vnRange`,
    `OperatorAlgebras.stone_von_neumann_irreducible`
82. Lightlike/OperatorAlgebras/QuasiFree.lean -
    `OperatorAlgebras.WeylSystem.continuous_line_of_quasiFree`, `OperatorAlgebras.CCRRep.IsQuasiFree`,
    `OperatorAlgebras.CCRRep.field`, `OperatorAlgebras.CCRRep.IsQuasiFree.mem_domain`,
    `OperatorAlgebras.CCRRep.IsQuasiFree.inner_field_field`,
    `OperatorAlgebras.CCRRep.IsQuasiFree.abs_symp_le`, `OperatorAlgebras.FockRep.isQuasiFree_vacuum`,
    `OperatorAlgebras.WeylSystem.toCCRRep`, `OperatorAlgebras.CCRRep.IsQuasiFree.abs_symp_le_two_mul`
83. Lightlike/OperatorAlgebras/TestsQuasiFree.lean - `OperatorAlgebras.FockRep.inner_field_field_vacuum`
84. Lightlike/OperatorAlgebras/FermiFockGeneral.lean - `OperatorAlgebras.fermiCre`,
    `OperatorAlgebras.fermiAnn`, `OperatorAlgebras.fermiAnn_fermiCre_anticomm`, `OperatorAlgebras.creW`,
    `OperatorAlgebras.annW_creW_anticomm`, `OperatorAlgebras.fockField`,
    `OperatorAlgebras.fockField_anticomm`, `OperatorAlgebras.fockField_irreducible`,
    `OperatorAlgebras.isSelfAdjoint_fockField`
85. Lightlike/OperatorAlgebras/TestsFermiFock.lean - `OperatorAlgebras.fermiAnn_vacuum`
86. Lightlike/OperatorAlgebras/QuasiFreeWick.lean - `OperatorAlgebras.mixedDeriv`, `OperatorAlgebras.haf`,
    `OperatorAlgebras.mixedDeriv_exp_quad`, `OperatorAlgebras.CCRRep.npoint`, `OperatorAlgebras.CCRRep.IsQuasiFree.genFun_eq`,
    `OperatorAlgebras.CCRRep.IsQuasiFree.npoint_two`, `OperatorAlgebras.CCRRep.IsQuasiFree.npoint_eq_haf`
87. Lightlike/OperatorAlgebras/SecondQuantization.lean - `OperatorAlgebras.FockRep.gamma`,
    `OperatorAlgebras.FockRep.gamma_W_Ω`, `OperatorAlgebras.FockRep.gamma_comp`,
    `OperatorAlgebras.FockRep.adjoint_gamma`, `OperatorAlgebras.FockRep.gamma_mem_unitary_iff`,
    `OperatorAlgebras.FockRep.secondQuant`, `OperatorAlgebras.FockRep.eq_smul_secondQuant`,
    `OperatorAlgebras.posSemidef_kernel`, `OperatorAlgebras.FockRep.secondQuantGroup`,
    `OperatorAlgebras.FockRep.dGamma`, `OperatorAlgebras.FockRep.norm_gamma_le`,
    `OperatorAlgebras.FockRep.norm_le_one_of_gamma`, `OperatorAlgebras.FockRep.secondQuant_conj`,
    `OperatorAlgebras.FockRep.eq_secondQuant_of_pos`
88. Lightlike/OperatorAlgebras/TestsSecondQuantization.lean - `OperatorAlgebras.FockRep.secondQuant_trans_symm`,
    `OperatorAlgebras.FockRep.gamma_zero`
89. Lightlike/OperatorAlgebras/GibbsKMS.lean - `OperatorAlgebras.GibbsKMS.diag`, `OperatorAlgebras.GibbsKMS.domain`,
    `OperatorAlgebras.GibbsKMS.hamiltonian`, `OperatorAlgebras.GibbsKMS.inner_basis_hamiltonian`, `OperatorAlgebras.GibbsKMS.evol`,
    `OperatorAlgebras.GibbsKMS.dyn`, `OperatorAlgebras.GibbsKMS.inner_dyn`, `OperatorAlgebras.GibbsKMS.gibbs`,
    `OperatorAlgebras.GibbsKMS.gibbs_one`, `OperatorAlgebras.GibbsKMS.gibbs_star_mul_self_nonneg`,
    `OperatorAlgebras.GibbsKMS.gibbs_dyn`, `OperatorAlgebras.GibbsKMS.kmsFun`, `OperatorAlgebras.GibbsKMS.continuousOn_kmsFun`,
    `OperatorAlgebras.GibbsKMS.differentiableOn_kmsFun`, `OperatorAlgebras.GibbsKMS.norm_kmsFun_le`,
    `OperatorAlgebras.GibbsKMS.kmsFun_ofReal`, `OperatorAlgebras.GibbsKMS.kmsFun_add_I_mul`
90. Lightlike/OperatorAlgebras/TestsGibbsKMS.lean - `OperatorAlgebras.GibbsKMS.summable_exp_neg_mul_nat`,
    `OperatorAlgebras.GibbsKMS.oscillator_isKMS`, `OperatorAlgebras.GibbsKMS.not_summable_exp_zero` (the wrong input
    `β = 0`)
91. Lightlike/OperatorAlgebras/ModularFinite.lean - `OperatorAlgebras.kms`, `OperatorAlgebras.inner_tomita`,
    `OperatorAlgebras.omega_flow`, `OperatorAlgebras.flow_add`, `OperatorAlgebras.flow_mul`,
    `OperatorAlgebras.isKMS_boltz`, `OperatorAlgebras.not_isKMS_of_ne`
92. Lightlike/OperatorAlgebras/PureStates.lean - `OperatorAlgebras.PureStates.states`, `OperatorAlgebras.PureStates.IsPure`,
    `OperatorAlgebras.PureStates.mul_of_isPure`, `OperatorAlgebras.PureStates.exists_eq_eval_of_mul`,
    `OperatorAlgebras.PureStates.isPure_evalAt`, `OperatorAlgebras.PureStates.isPure_iff_exists_eval`,
    `OperatorAlgebras.PureStates.isPure_iff_mul`
93. Lightlike/OperatorAlgebras/TestsPureStates.lean - `OperatorAlgebras.PureStates.isPure_evalAt_true`,
    `OperatorAlgebras.PureStates.not_isPure_half` (a mixed state of `C(Bool)`)
94. Lightlike/OperatorAlgebras/PureStatesC0.lean - `OperatorAlgebras.PureStates.states₀`, `OperatorAlgebras.PureStates.IsPure₀`,
    `OperatorAlgebras.PureStates.ext`, `OperatorAlgebras.PureStates.ext_mem_states`, `OperatorAlgebras.PureStates.isPure_ext`,
    `OperatorAlgebras.PureStates.evalAt₀`, `OperatorAlgebras.PureStates.isPure₀_evalAt₀`,
    `OperatorAlgebras.PureStates.isPure₀_iff_exists_eval`
95. Lightlike/OperatorAlgebras/Wasserstein.lean - `OperatorAlgebras.Transport.couplings`,
    `OperatorAlgebras.Transport.prod_mem_couplings`, `OperatorAlgebras.Transport.wasserstein1`,
    `OperatorAlgebras.Transport.integral_sub_le_of_mem_couplings`, `OperatorAlgebras.Transport.integral_sub_le_wasserstein1`,
    `OperatorAlgebras.Transport.wasserstein1_le`, `OperatorAlgebras.Transport.wasserstein1_dirac`
96. Lightlike/OperatorAlgebras/TestsWasserstein.lean - `OperatorAlgebras.Transport.diag_mem_couplings`,
    `OperatorAlgebras.Transport.wasserstein1_self`, `OperatorAlgebras.Transport.wasserstein1_dirac_pos`
97. Lightlike/OperatorAlgebras/MongeKantorovich.lean - `OperatorAlgebras.Transport.omega`,
    `OperatorAlgebras.Transport.integral_le_omega`, `OperatorAlgebras.Transport.exists_linear_le_omega`,
    `OperatorAlgebras.Transport.exists_coupling_eq_omega`, `OperatorAlgebras.Transport.dualValues`,
    `OperatorAlgebras.Transport.exists_optimal_coupling`, `OperatorAlgebras.Transport.integral_optimal_eq_sSup`
98. Lightlike/OperatorAlgebras/TestsMongeKantorovich.lean - `OperatorAlgebras.Transport.sepCost`,
    `OperatorAlgebras.Transport.integral_sepCost`, `OperatorAlgebras.Transport.sSup_dualValues_sepCost`
99. Lightlike/OperatorAlgebras/KantorovichRubinstein.lean - `OperatorAlgebras.Transport.ctrans`,
    `OperatorAlgebras.Transport.lipschitzWith_ctrans`, `OperatorAlgebras.Transport.le_ctrans`,
    `OperatorAlgebras.Transport.ctrans_le_neg`, `OperatorAlgebras.Transport.exists_optimal_coupling_dist`,
    `OperatorAlgebras.Transport.wasserstein1_eq_sSup`
100. Lightlike/OperatorAlgebras/TestsKantorovichRubinstein.lean - `OperatorAlgebras.Transport.sSup_dirac`,
    `OperatorAlgebras.Transport.two_lipschitz_exceeds`, `OperatorAlgebras.Transport.ctrans_zero`
101. Lightlike/OperatorAlgebras/Spectral/Compact.lean - `OperatorAlgebras.CompactSpectral.exists_hilbertBasis_eigenvectors`,
    `OperatorAlgebras.CompactSpectral.hasSum_eigen`, `OperatorAlgebras.CompactSpectral.finite_eigenvalues_ge`,
    `OperatorAlgebras.CompactSpectral.countable_eigenvalues`, `OperatorAlgebras.CompactSpectral.countable_spectrum`,
    `OperatorAlgebras.CompactSpectral.hasEigenvalue_of_mem_spectrum`,
    `OperatorAlgebras.CompactSpectral.finiteDimensional_eigenspace`
102. Lightlike/OperatorAlgebras/Spectral/TestsCompact.lean - `OperatorAlgebras.CompactSpectral.not_finiteDimensional_eigenspace_id`,
    `OperatorAlgebras.CompactSpectral.not_isCompactOperator_id`,
    `OperatorAlgebras.CompactSpectral.exists_hilbertBasis_eigenvectors_of_finiteDimensional`,
    `OperatorAlgebras.CompactSpectral.invDiag_zero_mem_spectrum_not_hasEigenvalue` (0 is in the spectrum of
    diag(1/(n+1)) and is not an eigenvalue)
103. Lightlike/OperatorAlgebras/Spectral/HilbertSchmidtCompact.lean - `OperatorAlgebras.CompactSpectral.isCompactOperator_of_isHilbertSchmidt`
104. Lightlike/OperatorAlgebras/Spectral/CanonicalForm.lean - `OperatorAlgebras.CompactSpectral.IsCanonicalForm`, `OperatorAlgebras.CompactSpectral.isCanonicalForm_of_eigenbasis`,
    `OperatorAlgebras.CompactSpectral.exists_isCanonicalForm`,
    `OperatorAlgebras.CompactSpectral.isCompactOperator_adjoint_comp`, `OperatorAlgebras.CompactSpectral.isSymmetric_adjoint_comp`,
    `OperatorAlgebras.CompactSpectral.IsCanonicalForm.le_opNorm`, `OperatorAlgebras.CompactSpectral.IsCanonicalForm.opNorm_le`,
    `OperatorAlgebras.CompactSpectral.IsCanonicalForm.exists_eq_opNorm`, `OperatorAlgebras.CompactSpectral.IsCanonicalForm.toAdjoint`,
    `OperatorAlgebras.CompactSpectral.IsCanonicalForm.finite_sq_eq`, `OperatorAlgebras.CompactSpectral.IsCanonicalForm.eigenspace_adjoint_comp`,
    `OperatorAlgebras.CompactSpectral.IsCanonicalForm.finrank_eigenspace_adjoint_comp`,
    `OperatorAlgebras.CompactSpectral.IsCanonicalForm.eigenspace_comp_adjoint`,
    `OperatorAlgebras.CompactSpectral.hasSum_norm_sq_of_orthonormal`
105. Lightlike/OperatorAlgebras/Spectral/TestsCanonicalForm.lean - `OperatorAlgebras.CompactSpectral.isEmpty_of_canonical_zero`,
    `OperatorAlgebras.CompactSpectral.nonempty_of_canonical_ne_zero`
106. Lightlike/OperatorAlgebras/Spectral/Schatten.lean - `OperatorAlgebras.CompactSpectral.schattenSum`,
    `OperatorAlgebras.CompactSpectral.schattenSum_eq_tsum`, `OperatorAlgebras.CompactSpectral.schattenSum_le_tsum`,
    `OperatorAlgebras.CompactSpectral.tsum_le_schattenSum`, `OperatorAlgebras.CompactSpectral.schatten_core`,
    `OperatorAlgebras.CompactSpectral.norm_rpow_le_schattenSum`, `OperatorAlgebras.CompactSpectral.schattenSum_adjoint`
107. Lightlike/OperatorAlgebras/Spectral/SchattenHS.lean - `OperatorAlgebras.CompactSpectral.tsum_norm_sq_apply_eq`,
    `OperatorAlgebras.CompactSpectral.schattenSum_two_eq_tsum_norm_sq`, `OperatorAlgebras.CompactSpectral.isHilbertSchmidt_iff`
108. Lightlike/OperatorAlgebras/Spectral/SchattenTrace.lean - `OperatorAlgebras.CompactSpectral.schattenSum_one_mul_le`,
    `OperatorAlgebras.CompactSpectral.abs_apply_of_adjoint_apply_apply`, `OperatorAlgebras.CompactSpectral.isTraceClass_iff`
109. Lightlike/OperatorAlgebras/Spectral/SchattenBanach.lean - `OperatorAlgebras.CompactSpectral.schattenNorm`,
    `OperatorAlgebras.CompactSpectral.schattenNorm_add_le`, `OperatorAlgebras.CompactSpectral.schattenSum_smul`,
    `OperatorAlgebras.CompactSpectral.schattenNorm_eq_zero_iff`, `OperatorAlgebras.CompactSpectral.schattenSum_le_of_tendsto`,
    `OperatorAlgebras.CompactSpectral.exists_tendsto_schattenNorm`
110. Lightlike/OperatorAlgebras/Spectral/TestsSchatten.lean - `OperatorAlgebras.CompactSpectral.schattenSum_two_invDiag_lt_top`,
    `OperatorAlgebras.CompactSpectral.schattenSum_one_invDiag_eq_top` (diag(1/(n+1)) is in J₂ and not in J₁)
111. Lightlike/OperatorAlgebras/SecondQuantFinite.lean - `OperatorAlgebras.SecondQuantFinite.IsModeAlgebra`, `OperatorAlgebras.SecondQuantFinite.isModeAlgebra_car`,
    `OperatorAlgebras.SecondQuantFinite.isModeAlgebra_ccr`, `OperatorAlgebras.SecondQuantFinite.IsModeAlgebra.four`, `OperatorAlgebras.SecondQuantFinite.commutator_number`, `OperatorAlgebras.SecondQuantFinite.dGamma`,
    `OperatorAlgebras.SecondQuantFinite.dGamma_sub`, `OperatorAlgebras.SecondQuantFinite.dGamma_mul`, `OperatorAlgebras.SecondQuantFinite.commutator_dGamma`, `OperatorAlgebras.SecondQuantFinite.dGamma_commutator_creation`,
    `OperatorAlgebras.SecondQuantFinite.dGamma_commutator_annihilation`, `OperatorAlgebras.SecondQuantFinite.dGamma_commutator`
112. Lightlike/OperatorAlgebras/TestsSecondQuantFinite.lean - `OperatorAlgebras.SecondQuantFinite.annOne`, `OperatorAlgebras.SecondQuantFinite.creOne`, `OperatorAlgebras.SecondQuantFinite.isModeAlgebra_oneMode`,
    `OperatorAlgebras.SecondQuantFinite.dGamma_oneMode`, `OperatorAlgebras.SecondQuantFinite.not_isModeAlgebra_oneMode_boson`
113. Lightlike/OperatorAlgebras/SecondQuantLadder.lean - `OperatorAlgebras.SecondQuantFinite.isModeAlgebra_ladderSystem`, `OperatorAlgebras.SecondQuantFinite.dGamma_ladderSystem`
114. Lightlike/OperatorAlgebras/SecondQuantRank.lean - `OperatorAlgebras.SecondQuantFinite.IsFieldAlgebra`, `OperatorAlgebras.SecondQuantFinite.rankOp`, `OperatorAlgebras.SecondQuantFinite.rankOpAdj`, `OperatorAlgebras.SecondQuantFinite.dGammaRank`,
    `OperatorAlgebras.SecondQuantFinite.dGammaRank_commutator_creation`, `OperatorAlgebras.SecondQuantFinite.dGammaRank_commutator_annihilation`, `OperatorAlgebras.SecondQuantFinite.compLeft`, `OperatorAlgebras.SecondQuantFinite.rankOp_comp`,
    `OperatorAlgebras.SecondQuantFinite.dGammaRank_commutator`
115. Lightlike/OperatorAlgebras/SecondQuantSlot.lean - `OperatorAlgebras.SecondQuantSlot.slotMap`, `OperatorAlgebras.SecondQuantSlot.norm_slotMap_le`,
    `OperatorAlgebras.SecondQuantSlot.coordL`, `OperatorAlgebras.SecondQuantSlot.uncoordL`, `OperatorAlgebras.SecondQuantSlot.slotC`, `OperatorAlgebras.SecondQuantSlot.norm_slotC_le`,
    `OperatorAlgebras.SecondQuantSlot.slotEquiv`, `OperatorAlgebras.SecondQuantSlot.slotOp`, `OperatorAlgebras.SecondQuantSlot.norm_slotOp_le`, `OperatorAlgebras.SecondQuantSlot.dGammaTensor`,
    `OperatorAlgebras.SecondQuantSlot.norm_dGammaTensor_le`
116. Lightlike/OperatorAlgebras/Semigroup/Defs.lean - `OperatorAlgebras.ContractionSemigroup`,
    `OperatorAlgebras.ContractionSemigroup.generator`
117. Lightlike/OperatorAlgebras/Spectral/ProjectionValuedMeasure.lean - `OperatorAlgebras.Spectral.ProjectionValuedMeasure`
118. Lightlike/OperatorAlgebras/SecondQuantWedge.lean - `OperatorAlgebras.SecondQuantWedge.tupleSign`, `OperatorAlgebras.SecondQuantWedge.sort_comp_perm`, `OperatorAlgebras.SecondQuantWedge.tupleSign_comp`,
    `OperatorAlgebras.SecondQuantWedge.Enum`, `OperatorAlgebras.SecondQuantWedge.enumEquiv`, `OperatorAlgebras.SecondQuantWedge.card_enum`, `OperatorAlgebras.SecondQuantWedge.embFun`, `OperatorAlgebras.SecondQuantWedge.norm_tupleSign`, `OperatorAlgebras.SecondQuantWedge.norm_embFun_sq`,
    `OperatorAlgebras.SecondQuantWedge.Fiber`, `OperatorAlgebras.SecondQuantWedge.injective_of_card_image`, `OperatorAlgebras.SecondQuantWedge.hasSum_fiber`, `OperatorAlgebras.SecondQuantWedge.hasSum_norm_embFun`, `OperatorAlgebras.SecondQuantWedge.summable_sq_of_lp`,
    `OperatorAlgebras.SecondQuantWedge.memℓp_embFun`, `OperatorAlgebras.SecondQuantWedge.embL`, `OperatorAlgebras.SecondQuantWedge.embL_apply`, `OperatorAlgebras.SecondQuantWedge.norm_sq_embL`, `OperatorAlgebras.SecondQuantWedge.norm_sq_lp`, `OperatorAlgebras.SecondQuantWedge.norm_embL_le`,
    `OperatorAlgebras.SecondQuantWedge.norm_embL_of_support`, `OperatorAlgebras.SecondQuantWedge.embCLM`, `OperatorAlgebras.SecondQuantWedge.norm_embCLM_le`, `OperatorAlgebras.SecondQuantWedge.dGammaFock`, `OperatorAlgebras.SecondQuantWedge.norm_dGammaFock_le`,
    `OperatorAlgebras.SecondQuantWedge.permEquiv`, `OperatorAlgebras.SecondQuantWedge.permEquiv_apply`, `OperatorAlgebras.SecondQuantWedge.permL`, `OperatorAlgebras.SecondQuantWedge.permL_apply`, `OperatorAlgebras.SecondQuantWedge.antisym`, `OperatorAlgebras.SecondQuantWedge.antisym_apply`,
    `OperatorAlgebras.SecondQuantWedge.embFun_comp`, `OperatorAlgebras.SecondQuantWedge.antisym_embL`,
    `OperatorAlgebras.SecondQuantWedge.tensorFun`, `OperatorAlgebras.SecondQuantWedge.hasSum_norm_tensorFun`, `OperatorAlgebras.SecondQuantWedge.hasSum_norm_sq_lp`, `OperatorAlgebras.SecondQuantWedge.memℓp_tensorFun`,
    `OperatorAlgebras.SecondQuantWedge.creTL`, `OperatorAlgebras.SecondQuantWedge.creTL_apply`, `OperatorAlgebras.SecondQuantWedge.norm_creTL`, `OperatorAlgebras.SecondQuantWedge.creT`, `OperatorAlgebras.SecondQuantWedge.creT_apply`, `OperatorAlgebras.SecondQuantWedge.slotOp_zero_creT`,
    `OperatorAlgebras.SecondQuantWedge.removeNth_succ_eq`, `OperatorAlgebras.SecondQuantWedge.slotOp_succ_creT`, `OperatorAlgebras.SecondQuantWedge.dGammaTensor_creT`, `OperatorAlgebras.SecondQuantWedge.dGammaTensor_zero_creT`,
    `OperatorAlgebras.SecondQuantWedge.sign_eq_signAux`, `OperatorAlgebras.SecondQuantWedge.tupleSign_eq_prod`, `OperatorAlgebras.SecondQuantWedge.tupleSign_cons`, `OperatorAlgebras.SecondQuantWedge.sign_mul_self`, `OperatorAlgebras.SecondQuantWedge.antisym_comp`, `OperatorAlgebras.SecondQuantWedge.antisym_apply_of_not_injective`,
    `OperatorAlgebras.SecondQuantWedge.sum_perm_apply_zero`, `OperatorAlgebras.SecondQuantWedge.tupleSign_of_strictMono`, `OperatorAlgebras.SecondQuantWedge.prod_succ_lt_zero`, `OperatorAlgebras.SecondQuantWedge.prod_comp_le_zero`, `OperatorAlgebras.SecondQuantWedge.fermiSign_strictMono`, `OperatorAlgebras.SecondQuantWedge.image_tail_comp`,
    `OperatorAlgebras.SecondQuantWedge.factorial_sqrt_identity`, `OperatorAlgebras.SecondQuantWedge.embFun_creW_strictMono`, `OperatorAlgebras.SecondQuantWedge.embFun_creW`, `OperatorAlgebras.SecondQuantWedge.embL_creW`,
    `OperatorAlgebras.SecondQuantWedge.slotEquiv_symm_apply`, `OperatorAlgebras.SecondQuantWedge.slotOp_apply_eq`, `OperatorAlgebras.SecondQuantWedge.slotOp_permL`, `OperatorAlgebras.SecondQuantWedge.dGammaTensor_permL`, `OperatorAlgebras.SecondQuantWedge.dGammaTensor_antisym`,
    `OperatorAlgebras.SecondQuantWedge.exists_perm_of_image_eq`, `OperatorAlgebras.SecondQuantWedge.embFun_single_self`, `OperatorAlgebras.SecondQuantWedge.embFun_single_eq_zero`, `OperatorAlgebras.SecondQuantWedge.inner_embL_single`, `OperatorAlgebras.SecondQuantWedge.adjoint_embCLM_apply`,
    `OperatorAlgebras.SecondQuantWedge.adjoint_embCLM_apply_of_card`, `OperatorAlgebras.SecondQuantWedge.adjoint_embCLM_apply_image`, `OperatorAlgebras.SecondQuantWedge.sqrt_sign_sq`, `OperatorAlgebras.SecondQuantWedge.embCLM_adjoint_apply`, `OperatorAlgebras.SecondQuantWedge.adjoint_embCLM_embCLM`,
    `OperatorAlgebras.SecondQuantWedge.adjoint_embCLM_antisym`, `OperatorAlgebras.SecondQuantWedge.creWCoeff_apply_of_card`, `OperatorAlgebras.SecondQuantWedge.dGammaFock_apply_of_card`, `OperatorAlgebras.SecondQuantWedge.dGammaFock_creW`, `OperatorAlgebras.SecondQuantWedge.dGammaFock_zero_creW`,
    `OperatorAlgebras.SecondQuantWedge.adjoint_conj`, `OperatorAlgebras.SecondQuantWedge.adjoint_slotMap`, `OperatorAlgebras.SecondQuantWedge.coordL_uncoordL`, `OperatorAlgebras.SecondQuantWedge.adjoint_slotC`, `OperatorAlgebras.SecondQuantWedge.adjoint_slotOp`,
    `OperatorAlgebras.SecondQuantWedge.adjoint_dGammaTensor`, `OperatorAlgebras.SecondQuantWedge.adjoint_dGammaFock`, `OperatorAlgebras.SecondQuantWedge.creL2`, `OperatorAlgebras.SecondQuantWedge.creL2_apply`, `OperatorAlgebras.SecondQuantWedge.annL2`,
    `OperatorAlgebras.SecondQuantWedge.apply_eq_inner_single`, `OperatorAlgebras.SecondQuantWedge.single_apply_of_card`, `OperatorAlgebras.SecondQuantWedge.inner_eq_zero_of_card`, `OperatorAlgebras.SecondQuantWedge.annL2_apply_of_card`, `OperatorAlgebras.SecondQuantWedge.annL2_dGammaFock`,
    `OperatorAlgebras.SecondQuantWedge.annL2_dGammaFock_zero`, `OperatorAlgebras.SecondQuantWedge.uncoordL_coordL`, `OperatorAlgebras.SecondQuantWedge.slotOp_slotOp`, `OperatorAlgebras.SecondQuantWedge.slotOp_sub`, `OperatorAlgebras.SecondQuantWedge.clm_ext_single`,
    `OperatorAlgebras.SecondQuantWedge.slotOp_apply_of_fiber`, `OperatorAlgebras.SecondQuantWedge.slotOp_single_apply`, `OperatorAlgebras.SecondQuantWedge.slotOp_slotOp_single_apply`, `OperatorAlgebras.SecondQuantWedge.slotOp_comm`, `OperatorAlgebras.SecondQuantWedge.dGammaTensor_comm`,
    `OperatorAlgebras.SecondQuantWedge.dGammaFock_dGammaFock`, `OperatorAlgebras.SecondQuantWedge.dGammaFock_comm`
119. Lightlike/OperatorAlgebras/SecondQuantFock.lean - `OperatorAlgebras.SecondQuantFock.Statistics`, `OperatorAlgebras.SecondQuantFock.Statistics.chi`, `OperatorAlgebras.SecondQuantFock.chi_mul`,
    `OperatorAlgebras.SecondQuantFock.chi_mul_self`, `OperatorAlgebras.SecondQuantFock.chi_inv`, `OperatorAlgebras.SecondQuantFock.conj_chi`, `OperatorAlgebras.SecondQuantFock.theta`, `OperatorAlgebras.SecondQuantFock.theta_fermion`,
    `OperatorAlgebras.SecondQuantFock.theta_apply`, `OperatorAlgebras.SecondQuantFock.permL_permL`, `OperatorAlgebras.SecondQuantFock.theta_comp`, `OperatorAlgebras.SecondQuantFock.theta_theta`, `OperatorAlgebras.SecondQuantFock.adjoint_permL`,
    `OperatorAlgebras.SecondQuantFock.adjoint_theta`, `OperatorAlgebras.SecondQuantFock.dGammaT`, `OperatorAlgebras.SecondQuantFock.dGammaT_zero`, `OperatorAlgebras.SecondQuantFock.dGammaT_succ`, `OperatorAlgebras.SecondQuantFock.dGammaT_permL`,
    `OperatorAlgebras.SecondQuantFock.dGammaT_theta`, `OperatorAlgebras.SecondQuantFock.dGammaT_creT`, `OperatorAlgebras.SecondQuantFock.adjoint_dGammaT`, `OperatorAlgebras.SecondQuantFock.creF`, `OperatorAlgebras.SecondQuantFock.annF`,
    `OperatorAlgebras.SecondQuantFock.theta_creF`, `OperatorAlgebras.SecondQuantFock.creF_of_theta`, `OperatorAlgebras.SecondQuantFock.theta_annF`, `OperatorAlgebras.SecondQuantFock.dGammaT_creF`, `OperatorAlgebras.SecondQuantFock.dGammaT_annF`,
    `OperatorAlgebras.SecondQuantFock.dGammaT_comm`, `OperatorAlgebras.SecondQuantFock.embCLM_creW`, `OperatorAlgebras.SecondQuantFock.embCLM_dGammaFock`
120. Lightlike/OperatorAlgebras/FiniteKMS.lean - `OperatorAlgebras.isKMS_iff_eq_gibbs`,
     `OperatorAlgebras.isKMS_gibbs`
121. Lightlike/OperatorAlgebras/FiniteModular.lean - `OperatorAlgebras.isKMS_modular`
122. Lightlike/OperatorAlgebras/FockShale/Summary.lean - `OperatorAlgebras.op2_fock_and_shale`,
     `OperatorAlgebras.op2_one_mode_alpha_beta`,
     `OperatorAlgebras.op2_infinite_modes_not_implementable`,
     `OperatorAlgebras.op2_one_mode_implementable`
123. Lightlike/OperatorAlgebras/QuasiFreeState/ComplexStructure.lean -
     `OperatorAlgebras.QuasiFreeState.isPureState_qfState_of_complexStructure`,
     `OperatorAlgebras.QuasiFreeState.isPureState_qfState_of_complexStructure_retract`
124. Lightlike/OperatorAlgebras/QuasiFreeState/SorkinJohnston.lean -
     `OperatorAlgebras.QuasiFreeState.isPureState_causalSet`,
     `OperatorAlgebras.QuasiFreeState.exists_pjData`
125. Lightlike/OperatorAlgebras/CARBogoliubov.lean - `OperatorAlgebras.bogAnn_bogCre_anticomm`,
     `OperatorAlgebras.bogAnn_anticomm`, `OperatorAlgebras.isCARPairs_bog`, `OperatorAlgebras.bog_inv`,
     `OperatorAlgebras.isCAROn_bogFam`, `OperatorAlgebras.isIrreducibleCAR_bogFam`,
     `OperatorAlgebras.bogoliubov_implementable`
126. Lightlike/OperatorAlgebras/CARQuasiFree.lean - `OperatorAlgebras.bogVacuum_inner_a_a`,
     `OperatorAlgebras.bogVacuum_inner_c_c`, `OperatorAlgebras.bogVacuum_inner_a_c`,
     `OperatorAlgebras.bogVacuum_exists`, `OperatorAlgebras.bogVacuum_unique`,
     `OperatorAlgebras.exists_bogVacuum_jordanWigner`
127. Lightlike/OperatorAlgebras/CARShale.lean - `OperatorAlgebras.CARShale.exists_unitary_of_dense`,
     `OperatorAlgebras.CARShale.dense_words`, `OperatorAlgebras.CARShale.exists_implementer`,
     `OperatorAlgebras.CARShale.exists_vacuum_of_small`,
     `OperatorAlgebras.CARShale.fermionic_shale_of_small`
128. Lightlike/OperatorAlgebras/QuasiFreeState/SJRetarded.lean -
     `OperatorAlgebras.QuasiFreeState.isPureState_retarded`,
     `OperatorAlgebras.QuasiFreeState.isUnit_one_sub_smul`,
     `OperatorAlgebras.QuasiFreeState.retardedMatrix_mul`, `OperatorAlgebras.QuasiFreeState.linkMatrix`
129. Lightlike/OperatorAlgebras/FermionWick.lean - `OperatorAlgebras.wick`, `OperatorAlgebras.A_pass`,
     `OperatorAlgebras.expect_prod`, `OperatorAlgebras.wick_pair`, `OperatorAlgebras.wick_single`
130. Lightlike/OperatorAlgebras/CARWick.lean - `OperatorAlgebras.carField`,
     `OperatorAlgebras.carField_anticomm`, `OperatorAlgebras.car_wick`, `OperatorAlgebras.car_wick_two`

## References

1. B. C. Hall, *Quantum Theory for Mathematicians*, Graduate Texts in Mathematics 267, Springer, 2013,
   Chapter 10 (Stone's theorem).
2. O. Bratteli and D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, 2nd ed.,
   Springer, 1997, Chapter 5, after D. Shale, *Linear symmetries of free boson fields*, Trans. Amer. Math.
   Soc. 103 (1962) 149.
3. Math 7334 lecture notes, Georgia Tech (Spring 2017), Section 4: The Theorem of Hille and Yosida concerning semi-groups, Theorem 1.9, https://loss.math.gatech.edu/17SPRINGTEA/7334/NOTES/section4hilleyosida.pdf.
4. G. Teschl, *Mathematical Methods in Quantum Mechanics*, Graduate Studies in Mathematics 99, American Mathematical
   Society, 2009 (online edition), Theorem 3.7 (spectral theorem) and Theorem 6.6 (compact self-adjoint operators). The Lean files are ported from physicslib4
   (github.com/physicslib/physicslib4, Apache-2.0).
5. G. Bonneau, J. Faraut and G. Valent, *Self-adjoint extensions of operators and the teaching of quantum
   mechanics*, arXiv:quant-ph/0103153, Appendix A.3 and Section 5.3, eqs. (14) and (15).
6. C. Bär, N. Ginoux and F. Pfäffle, *Wave Equations on Lorentzian Manifolds and Quantization*, ESI Lectures in
   Mathematics and Physics, European Mathematical Society, 2007, arXiv:0806.1036, Section 4.2 (Definition 4.2.1,
   Example 4.2.2, Proposition 4.2.3), pp. 116-122.
7. J. Dereziński, *Introduction to representations of the canonical commutation and anticommutation
   relations*, in *Large Coulomb Systems*, Lecture Notes in Physics 695, Springer, 2006, arXiv:math-ph/0511030:
   Theorem 4 and Corollary 1 (Stone-von Neumann), Theorem 10 and Corollary 2 (the CAR over `ℝ²ⁿ`), Sections 5.2,
   5.3, 5.5, 6.4 and 7.1, Theorems 13, 18, 24 and 28 (Fock spaces and second quantization), Section 9.1, Theorems 37
   and 39 (quasi-free states; Theorem 39 (1) in the corrected form `½(η + iω)`).
8. M. Faulhuber, *Time-Frequency Analysis*, lecture notes, 2022, Section 7.3.1 (von Neumann's proof of the
   Stone-von Neumann theorem).
9. J. Panangaden, *Energy Full Counting Statistics and Return to Equilibrium*, master's thesis, McGill University,
   2021, arXiv:2110.01678, Section 5.2: Proposition 5.4, Remark 5.1, Definition 5.8 and Proposition 5.9.
10. E. Witten, *Notes on some entanglement properties of quantum field theory*, Rev. Mod. Phys. 90 (2018) 045003,
   arXiv:1803.04993, Sections 4.1 and 4.2.
11. N. P. Landsman, *Lecture Notes on C*-Algebras, Hilbert C*-modules, and Quantum Mechanics*, 1998,
   arXiv:math-ph/9807030, Section 2.12: Definition 2.12.1, Proposition 2.12.8 and Theorem 2.12.9.
12. W. Huang, R. Wang, Y. Wu and D. Meng, *Exact endpoint asymptotics and almost-sure limits for uniform empirical
   measures in two dimensions*, arXiv:2610.21070, Section 3.2.1 and Section 8.1 (Kantorovich-Rubinstein duality on a
   compact metric space).
