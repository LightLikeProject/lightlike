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

## Sufficiency (`⇐`): route (start 16:30)

Goal: `IsHilbertSchmidt β` gives `Ψ` with `⟪Ψ, W f Ψ⟫ = exp (-q f/4)`; then `implements_of_gaussian_vector` (P5).
Route by polar decomposition `T = U S`: `U` complex-unitary (implemented by the Gram-matrix unitary lemma, `Γ(U) W f Ω = W (U f) Ω`),
`S = √(Tᵀ T)` positive symplectic with `β_S` Hilbert-Schmidt. For `S`, finite-mode truncations `S_n` (spectral
projections of a `J`-invariant finite-rank part) are implemented by finite-mode squeezed vectors; Cauchy estimate
`‖Ψ_n - Ψ_m‖² ≤ C ∑_{i>m} ‖β bᵢ‖²`; the limit has the Gaussian characteristic function. Bricks: (1) real adjoint and
polar decomposition of a symplectic `T` (symplectic `S`), (2) `Γ(U)` for complex-unitary `U`, (3) finite-mode
squeezing in `K`, (4) the Cauchy estimate, (5) the limit and its characteristic function. Estimate 700 lines.
