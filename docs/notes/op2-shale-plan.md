# T-OP2-P3 (Shale's criterion): assessment and plan

Statement: for a Fock representation `R` of a complex Hilbert space `h` and a Bogoliubov transformation `T`,
`Implements R T ↔ IsHilbertSchmidt T.betaPart`.

## What exists

`FockRep` (a cyclic vacuum representation of the Weyl relations with the Fock expectation), existence
(`fockRepOf`, the reproducing kernel Hilbert space of the Fock kernel) and uniqueness (`fockUnitary`), the
Gram-matrix unitary (`exists_unitary_of_gram_eq`), the Gram function `fockGram`. No Fock number operator, no
second quantization, no Gaussian measures on finite-dimensional subspaces.

## The mathematical route (both directions need analysis not in the library)

* Reduction. `T` is implemented iff the Weyl relations twisted by `T`, `W'(f) = W(T f)`, give a representation
  equivalent to `W`. Since `fockGram (T f) (T g) = ⟪W f Ψ, W g Ψ⟫` for a vector `Ψ` with
  `⟪Ψ, W f Ψ⟫ = exp (-‖T f‖² / 4)` (the Gram argument of the uniqueness proof), `T` is implemented iff there is
  a *cyclic* vector `Ψ` of `W` with that Gaussian characteristic function. Cyclicity of every nonzero vector is
  the irreducibility of the Fock representation, itself a consequence of the vacuum being the only vector
  with the Fock characteristic function (the projection onto the vacuum is a limit of Gaussian averages of
  the Weyl unitaries).
* `⇒`. For `Ψ = U⁻¹ Ω` the overlap `|⟪Ω, Ψ⟫|² = lim_N ∏_{i ≤ N} (1 + ‖β e_i‖²)^{-1}` (Gaussian integrals over
  the span of the first `N` basis vectors); it is positive, so `∑ ‖β e_i‖² < ∞`.
* `⇐`. For `β` Hilbert-Schmidt, the squeezed vector `Ψ` is a limit of finite-mode squeezed vectors, which
  needs the finite-dimensional symplectic structure (polar decomposition of `T` restricted to finite
  subspaces) and a Cauchy estimate from `∑ ‖β e_i‖² < ∞`.

## Pieces and estimate

1. Irreducibility of the Fock representation, and the projection onto the vacuum as a Gaussian limit: 2-3 days.
2. The reduction above (twisted representation, cyclic vector with Gaussian characteristic function): 1 day.
3. The direction `⇒`, the infinite product and Gaussian integrals: 2 days.
4. The direction `⇐`, finite-mode squeezing and the limit: 2-3 days.

Research-level, about a week of work, with no standard Mathlib support for Gaussian integrals over
finite-dimensional subspaces of a Hilbert space (finite-dimensional Gaussian integrals exist in Mathlib).

## Revised route for the irreducibility (no Gaussian measures)

For `C` in the commutant, `χ = C Ω`, put `k_x = W x Ω` and `F_χ(x) = ⟪k_x, χ⟫ / e(x)`, `e(x) = exp (-‖x‖² / 4)`.
(a) `F_χ` is antiholomorphic along complex lines: for `χ = k_f` it is `e(f) exp (⟪x, f⟫ / 2)`, and a vector is a
limit of finite combinations of the `k_f` with `|F_χ(y) - F_χ'(y)| ≤ ‖χ - χ'‖ exp (‖y‖² / 4)` (locally
uniform).
(b) `C k_b = W b χ`, so `⟪k_a, C k_b⟫ / (e(a) e(b)) = exp (⟪a, b⟫ / 2) F_χ(a - b)`; the left side is
`conj F_{C* k_a}(b)`, holomorphic in `b`.
(c) So `F_χ` is holomorphic and antiholomorphic along every complex line, hence constant, hence `χ ∈ ℂ Ω`,
hence `C` is a scalar; a nonzero vector is cyclic because the projection onto its closed span commutes with
the Weyl unitaries.

## Necessity (`⇒`): what the finite-mode route needs

Done (`ShaleAlgebra.lean`): `‖α e‖² - ‖β e‖² = ‖e‖²` and `4 ‖β e‖² = q(e) + q(i e) - 2 ‖e‖²`, `q f = ‖T f‖²`.

The route: for a finite orthonormal set `F` and `V_F = span_ℝ {e, i e : e ∈ F}`, the operator
`P_F = (2π)^{-n} ∫_{V_F} exp (-‖f‖²/4) W f df` is the projection onto the vectors in which the modes of `F` are in
the vacuum (self-adjoint: `W f* = W (-f)`; idempotent: the Weyl relation and one Gaussian integral
`∫ exp (-|u|²/2 - i σ(u, h)/2) du = (2π)^n exp (-|h|²/8)`; it fixes `Ω`, so `P_F ≥ |Ω⟩⟨Ω|`). For the vector `Ψ` with
`⟪Ψ, W f Ψ⟫ = exp (-q f / 4)`, and any `g`, `⟪W g Ψ, P_F W g Ψ⟫ ≤ (2π)^{-n} ∫ exp (-(‖f‖² + q f)/4) df`
(the phase `exp (i σ(f, g))` has modulus one), which is `2^n det (1 + S_F)^{-1/2}`, `S_F` the compression of
`q` to `V_F`. By irreducibility `⟪Ω, W g Ψ⟫ ≠ 0` for some `g`, so `det ((1 + S_F)/2)` is bounded above
uniformly in `F`.
Open point: `S_F` is the compression of a symplectic matrix, not symplectic, and `S_F` need not dominate `1`
(`q f < ‖f‖²` happens), so `det ((1 + S_F)/2) ≥ 1 + (1/4) ∑ (q(e) + q(i e) - 2)` does not follow from a
trace/determinant inequality alone; the Schur complement of the block form `[[1 + Γ, Λ], [Λ*, 1 + Γ̄]]`
(`Γ = α*α + β*β`, `Λ` the antilinear coupling) has to be used, with `α*α - β*β = 1`.
Estimated as the largest piece of the criterion.

### Numerical check of the open point (PROXY, not a proof)

For random symplectic `S = Tᵀ T` on `ℝ^{2N}` (`N = 5`, `exp (J H)` with random symmetric `H`, four scales), compressed to
the first `n ∈ {1, 2, 3}` modes: `(det ((1 + S_F)/2) - 1) / tr (S_F - 1) ≥ 0.263` in 12000 samples with
`tr (S_F - 1) > 10⁻⁶`. So the candidate inequality `det ((1 + S_F)/2) ≥ 1 + tr (S_F - 1)/4` held with no counterexample.
A proof is still needed. Tools in sight: `S_F⁻¹ ≤ (S⁻¹)_F = J S_F Jᵀ` (compression of an inverse dominates the inverse of
the compression, and `V_F` is `J`-invariant).

### Status of the determinant bound (13:40)

`S_F⁻¹ ≤ J S_F Jᵀ` was checked numerically (smallest eigenvalue of the difference `2.7·10⁻⁵ ≥ 0`, 3000 samples). It gives
`det S_F ≥ 1`, but `det S_F ≥ 1` alone does NOT imply `det ((1+S_F)/2) ≥ 1 + tr (S_F-1)/4`: with eigenvalues
`(0.3, 0.3, 100)` the left side is `21.3` and the right side `25.4`. So the proof must use the operator inequality, not
the spectrum alone. No proof path yet.

### Route through spectral subspaces of `P = Tᵀ T` (13:50)

For `P` positive symplectic, the spectrum is closed under `λ ↦ 1/λ` and `J` maps the `λ`-eigenspace onto the `1/λ` one.
On a `J`-invariant spectral subspace each pair contributes `(1+λ)/2 · (1+1/λ)/2 = 1 + t/4`, `t = λ + 1/λ - 2 ≥ 0`, so
`det ((1+P_F)/2) = ∏ (1 + tᵢ/4) ≥ 1 + tr (P_F - 1)/4` exactly (MEASURED by algebra, no operator inequality). The cost:
the subspaces are spectral, not spanned by an arbitrary Hilbert basis, so (a) the continuous spectrum needs an
interval approximation (`[r, r+δ]` paired with `[1/(r+δ), 1/r]`), and (b) the basis-independence of `∑ ⟨e, A e⟩` for
positive `A` is needed to pass from the spectral sum to `IsHilbertSchmidt` (every basis). Neither is in Mathlib as
far as checked. Open: which of (a)/(b) is the smaller piece.

### Basis independence (b): found in Physlib (13:50)

`PhyslibAlpha/ProbabilisticTheory/HilbertSpace/TraceClass/Basic.lean` has `trace_eq_of_hilbertBasis_of_nonneg`
(trace of a positive bounded operator is the same in every Hilbert basis) and `HilbertSchmidt.lean` has
`hasSum_norm_sq_apply_of_basis`, for complex-linear bounded operators `H →L[ℂ] H`. The antilinear `β` does not fit,
but `α` does: `T` is continuous, so `α f = (T f - i T (i f))/2` is a bounded complex-linear operator, and
`‖β e‖² = ‖α e‖² - ‖e‖² = ⟪e, (α†α - 1) e⟫` with `α†α - 1 ≥ 0`. So `IsHilbertSchmidt β` (every basis) follows from
the trace of the positive operator `α†α - 1` in one basis plus that lemma. Cost (b) is therefore small; cost (a), the
continuous-spectrum interval approximation, remains the open piece.

## Necessity: state at 16:20 (what compiles, what is missing)

Compiles (`ShaleAlgebra.lean`, `HilbertSchmidtBasis.lean`, `ShaleHilbertSchmidt.lean`, no `sorry`): the antilinear part
through the quadratic form `q f = ‖T f‖²`; `α` as a bounded operator, `α†α - 1 ≥ 0`, `‖√(α†α - 1) e‖ = ‖β e‖`;
basis independence of the Hilbert-Schmidt square sum (Physlib port); and
`Bogoliubov.isHilbertSchmidt_of_finite_bound`: a uniform bound `∑_{i ∈ s} (q bᵢ + q (i bᵢ) - 2) ≤ C` over finite
`s` for one Hilbert basis gives `IsHilbertSchmidt β`.

Missing step: from a vector `Ψ` with `⟪Ψ, W f Ψ⟫ = exp (-q f/4)` (`gaussian_vector_of_implements`) to that uniform
bound. This needs (i) the vacuum projection `P_F` of finitely many modes as the Gaussian average of `W f` over
`V_F` (self-adjoint, idempotent, `P_F Ω = Ω`), (ii) the finite-dimensional Gaussian integral of `exp (-(‖f‖² + q f)/4)`
against a positive quadratic form on `V_F`, and (iii) the determinant bound `det ((1 + P_F)/2) ≥ 1 + tr (P_F - 1)/4`
on `J`-invariant spectral subspaces (continuous spectrum by interval approximation). No shortcut found.

## Necessity: the route that closes it (Fable-1, 18 November 2026)

The three missing steps are replaced as follows; the files are Lightlike/OperatorAlgebras/ShaleDeterminant.lean,
Lightlike/OperatorAlgebras/FockVacuumAverage.lean and Lightlike/OperatorAlgebras/ShaleNecessity.lean.

(i) The vacuum projection `P_F` is not built as an operator. Only the inequality
`(2π)ⁿ |⟪Ω, Φ⟫|² ≤ Re ∫ exp (-‖f_x‖²/4) ⟪Φ, W f_x Φ⟫ dx` is needed, and it is proved on the dense set of finite
combinations `Φ = ∑ cⱼ W gⱼ Ω`: there the integral is a product of one-dimensional Gaussian integrals
(Mathlib's `GaussianFourier.integral_cexp_neg_mul_sum_add`) and equals `(2π)ⁿ ‖Φ'‖²` with
`Φ' = ∑ cⱼ λⱼ W gⱼ' Ω`, `gⱼ'` the part of `gⱼ` orthogonal to the modes, `λⱼ = e(gⱼ)/e(gⱼ')`; and
`⟪Ω, Φ'⟫ = ⟪Ω, Φ⟫`, so Cauchy-Schwarz gives the bound. Dominated convergence extends it to every `Φ`. No
self-adjointness, idempotence, Fubini or strong measurability of `x ↦ W f_x` is used.

(ii) `integral_exp_neg_half_quad` (the field-theory Gaussian integral, on main), transported from
`EuclideanSpace ℝ ι` to `ι → ℝ`.

(iii) The determinant bound holds for every finite orthonormal family, with no spectral subspaces: the open point
above is closed. In the real basis `eₖ, i eₖ` the matrix `A` of `f ↦ ‖T f‖²` satisfies: `A + i Ω` is the complex
Gram matrix of the vectors `T eₖ, T (i eₖ)` (real part `A`, imaginary part the symplectic form, which `T`
preserves), so `A + i Ω ≥ 0` and, by transposition, `A - i Ω ≥ 0`. Conjugating with `U = [[1, i], [1, -i]]`:
`U (1 + A) Uᴴ = [[E, B], [Bᴴ, D]]`, `U (A + i Ω) Uᴴ = [[E, B], [Bᴴ, D - 4]]`,
`U (A + i Ω)ᵀ Uᴴ = [[E - 4, B], [Bᴴ, D]]`. Hence `E - 4 ≥ 0` and the Schur complement `D - 4 - Bᴴ E⁻¹ B ≥ 0`, and
`4ⁿ det (1 + A) = det E · det (D - Bᴴ E⁻¹ B) ≥ 4ⁿ (1 + tr (E - 4)/4) · 4ⁿ`, with `tr (E - 4) = tr A - 2n`. This is
`det ((1 + A)/2) ≥ 1 + tr (A - 1)/4`, the inequality checked numerically above. The counterexample `(0.3, 0.3, 100)`
does not satisfy `A ± i Ω ≥ 0`.

## Sufficiency: the route that closes it, without a polar decomposition (Fable-1, 18 November 2026)

The files are Lightlike/OperatorAlgebras/FockContinuity.lean, Lightlike/OperatorAlgebras/VacuumProjection.lean and
Lightlike/OperatorAlgebras/ShaleSufficiency.lean. The brick plan below
(polar decomposition, finite-mode squeezed vectors, a Cauchy estimate in the Hilbert-Schmidt tail) is not used.

The argument of the section "why the polar-free route fails" shows that a vector must be produced inside `K`.
It is produced as a vacuum of the twisted representation `W_T f = W (T f)` on `K`, not as a squeezed vector:

1. `f ↦ W f ψ` is norm continuous in a Fock representation (`FockRep.continuous_W`; on coherent vectors by the
   Gram function, then by density). `CCRRep` asks for continuity along real lines only.
2. For a strongly continuous representation and a finite orthonormal family `e`, the Bochner integral
   `P ψ = (2π)⁻ⁿ ∫ exp (-‖f_x‖²/4) W f_x ψ dx` (`vacAvg`) is symmetric and satisfies
   `P W f P = exp (-‖f‖²/4) P` for `f` in the span of the modes (the Weyl relation, Fubini, the shear
   `(x, u) ↦ (x, u - x)` and one Gaussian integral, the same one as in the necessity part). So `P` is an
   orthogonal projection, `P ψ = ψ` iff `⟪ψ, W f ψ⟫ = exp (-‖f‖²/4) ‖ψ‖²` on the span of the modes, and the
   range decreases when modes are added.
3. In the twisted representation, `‖P_s Ω‖² = ⟪Ω, P_s Ω⟫ = det ((1 + A_s)/2)^(-1/2)` for the modes `bₖ`, `k ∈ s`,
   of a Hilbert basis (the Gaussian integral of the necessity part), and `det M ≤ exp (tr M - 2n)` gives
   `det ((1 + A_s)/2) ≤ exp (2 ∑_{k ∈ s} ‖β bₖ‖²)`. With the Hilbert-Schmidt hypothesis,
   `‖P_s Ω‖² ≥ exp (-∑ₖ ‖β bₖ‖²) > 0` uniformly in `s`. The two halves of the criterion use the two opposite
   bounds of the same determinant: necessity `det ≥ 1 + (1/4) tr (A - 1)`, sufficiency `det ≤ exp (tr (A - 1)/2)`.
4. `‖P_s Ω - P_t Ω‖² = ‖P_s Ω‖² - ‖P_t Ω‖²` for `s ⊆ t`, so the net `P_s Ω` is Cauchy; its limit `Ω'` is nonzero
   and fixed by every `P_s` (`exists_fixed_of_decreasing_projections`).
5. `⟪Ω', W (T f) Ω'⟫ = exp (-‖f‖²/4) ‖Ω'‖²` on the span of the basis, hence everywhere by step 1. So
   `(K, W_T, Ω'/‖Ω'‖)` is a Fock representation (cyclic by `fockRep_cyclic`), and the unitary of the uniqueness
   theorem `fockUnitary_spec` between `(K, W, Ω)` and it satisfies `U W f = W (T f) U`.

## Sufficiency (`⇐`): route (start 16:30)

Goal: `IsHilbertSchmidt β` gives `Ψ` with `⟪Ψ, W f Ψ⟫ = exp (-q f/4)`; then `implements_of_gaussian_vector` (P5).
Route by polar decomposition `T = U S`: `U` complex-unitary (implemented by the Gram-matrix unitary lemma, `Γ(U) W f Ω = W (U f) Ω`),
`S = √(Tᵀ T)` positive symplectic with `β_S` Hilbert-Schmidt. For `S`, finite-mode truncations `S_n` (spectral
projections of a `J`-invariant finite-rank part) are implemented by finite-mode squeezed vectors; Cauchy estimate
`‖Ψ_n - Ψ_m‖² ≤ C ∑_{i>m} ‖β bᵢ‖²`; the limit has the Gaussian characteristic function. Bricks: (1) real adjoint and
polar decomposition of a symplectic `T` (symplectic `S`), (2) `Γ(U)` for complex-unitary `U`, (3) finite-mode
squeezing in `K`, (4) the Cauchy estimate, (5) the limit and its characteristic function. Estimate 700 lines.

### Reuse for the necessity integral (ii) (read 16:35)

pl's FT1 stage 1 (`38d10c8`, `Lightlike/FieldTheory/Gaussian/Integral.lean`, read by `git show`, not imported):
`integral_exp_neg_half_quad (A : Matrix ι ι ℝ) (hA : A.PosDef) : ∫ x, exp (-(1/2) xᵀ A x) = (2π)^{n/2} / √(det A)`
on `EuclideanSpace ℝ ι`. This is (ii) once `1/2·(‖f‖² + q f)/2 = ½ xᵀ A x` is written in coordinates of `V_F`; to be
imported when it is on main.

## Sufficiency: brick plan, and why the polar-free route fails

Why no polar-free route: let `ω(W f) = exp (-‖T f‖²/4)` and take its GNS representation `(R', Ψ')`. The family
`f ↦ W'(T⁻¹ f)` is then a Fock representation of `h` (cyclic vector with expectation `exp (-‖f‖²/4)`), so
`FockUnique` gives a unitary `K ≅ K'`. But `Ψ'` is not a vector of `K` and the unitary intertwines `W` with
`W'∘T⁻¹` on `K'`, not `W ∘ T` on `K`; the argument proves nothing about implementability on `K`, and read as a
proof of implementability it would prove it for every `T`. Shale's hypothesis must enter through an explicit
vector `Ψ ∈ K`; the Bargmann-space (kernel domination) formulation needs the same determinants as necessity.

Bricks (estimates in Lean lines): (1) conjugation `C` from a Hilbert basis, the complex-linear `β̂ = β ∘ C` and the
block operator `M` on `h ⊕ h` (200); (2) polar decomposition of `M` by `CFC.sqrt (M† M)`, symplectic positive part
(300); (3) `Γ(U)` for a complex-unitary Bogoliubov map by the Gram-matrix unitary (200); (4) finite-mode squeezed
vectors in `K` (300); (5) the Cauchy estimate in the Hilbert-Schmidt tail (300); (6) the limit vector and its
characteristic function (300); (7) assembly with P5 (100). Total 1500-2200 lines. After OP6 (trace class, Schatten),
whose Hilbert-Schmidt API lowers bricks (2) and (5).
