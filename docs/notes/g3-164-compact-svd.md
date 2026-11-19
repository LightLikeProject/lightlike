# G3-164 (compact operators): the canonical form and the singular values

Source read: G. Teschl, *Mathematical Methods in Quantum Mechanics, With Applications to Schrödinger Operators*, Graduate
Studies in Mathematics 99, American Mathematical Society (2009), online edition (source key `teschl-2009`), Section 6.2,
Theorem 6.7 with its proof and (6.7), p. 137.

| Source | Library | Check |
|---|---|---|
| Theorem 6.7: orthonormal sets `{φ̂ⱼ}`, `{φⱼ}` and positive `sⱼ` with `K = ∑ⱼ sⱼ ⟪φⱼ, ·⟫ φ̂ⱼ`, `K* = ∑ⱼ sⱼ ⟪φ̂ⱼ, ·⟫ φⱼ` (6.6) | `IsCanonicalForm K φ φ' s` (orthonormal families `φ`, `φ'`, `s > 0`, `HasSum` for `K x` and `K* x`), `exists_isCanonicalForm`, `isCanonicalForm_of_eigenbasis` | (representation) families indexed by a type; the series are stated pointwise |
| "`Kφⱼ = sⱼ φ̂ⱼ` and `K*φ̂ⱼ = sⱼ φⱼ`, and hence `K*Kφⱼ = sⱼ²φⱼ` and `KK*φ̂ⱼ = sⱼ²φ̂ⱼ`" | the same theorem | matches |
| "The numbers `sⱼ(K)² > 0` are the nonzero eigenvalues of `KK*`, respectively `K*K` (counted with multiplicity)" | `IsCanonicalForm.eigenspace_adjoint_comp`, `IsCanonicalForm.finrank_eigenspace_adjoint_comp`, `IsCanonicalForm.eigenspace_comp_adjoint`: for every `μ ≠ 0` the `μ`-eigenspace of `K*K` (of `KK*`) is the span of the `φⱼ` (the `φ̂ⱼ`) with `sⱼ² = μ`, of dimension `#{j \| sⱼ² = μ}` | matches |
| "There are either finitely many singular values (if `K` is finite rank) or they converge to zero" | `{j \| ε ≤ sⱼ}` finite for every `ε > 0` | (representation) the two cases are one statement; the finite-rank remark is not stated |
| (6.7): `‖K‖ = maxⱼ sⱼ(K)` | `IsCanonicalForm.le_opNorm` (`sⱼ ≤ ‖K‖`), `IsCanonicalForm.opNorm_le` (`‖K‖ ≤ M` when all `sⱼ ≤ M`), `IsCanonicalForm.exists_eq_opNorm` (`sⱼ = ‖K‖` for some `j` when `K ≠ 0`), for every canonical form | (representation) the maximum is stated as an upper bound that is attained; for `K = 0` there are no singular values and the maximum is read as `0` |

Proof as in the source (`isCanonicalForm_of_eigenbasis`): Theorem 6.6 (`exists_hilbertBasis_eigenvectors`) for the compact symmetric `K*K`, `sⱼ = √μⱼ` on the
eigenvectors with `μⱼ > 0`, `φ'ⱼ = sⱼ⁻¹ K φⱼ` (orthonormal since `⟪Kφᵢ, Kφⱼ⟫ = μⱼ ⟪φᵢ, φⱼ⟫`), and `K bᵢ = 0` when `μᵢ = 0`.
Finitely many `sⱼ ≥ ε`: the `sⱼ²` are eigenvalues of `K*K`, finitely many of size at least `ε²`, each with a
finite-dimensional eigenspace holding the orthonormal `φⱼ` of that eigenvalue.

The eigenspaces (`IsCanonicalForm.eigenspace_adjoint_comp`): for `K*K x = μ x`, `μ ≠ 0`,
`μ ⟪φₖ, x⟫ = ⟪φₖ, K*K x⟫ = ⟪K*K φₖ, x⟫ = sₖ² ⟪φₖ, x⟫`, so `⟪φₖ, x⟫ = 0` unless `sₖ² = μ`; then
`y = x - ∑_{sⱼ² = μ} ⟪φⱼ, x⟫ φⱼ` (a finite sum) is a `μ`-eigenvector with every `⟪φₖ, y⟫ = 0`, so
`K y = ∑ⱼ sⱼ ⟪φⱼ, y⟫ φ̂ⱼ = 0` and `μ y = K*K y = 0`. The orthonormal `φⱼ` are linearly independent, which gives the
dimension. For `KK*` the same theorem applies to the canonical form of `K*` (`IsCanonicalForm.toAdjoint`). The maximum in
(6.7) (`IsCanonicalForm.exists_eq_opNorm`): only finitely many `sⱼ ≥ ‖K‖/2`, at least one (else `‖K‖ ≤ ‖K‖/2`), and the
largest of them bounds every `sⱼ`.

Mathlib's `LinearMap.singularValues` is for finite-dimensional spaces only.

Tests (`Spectral/TestsCanonicalForm.lean`): the zero operator has no singular values; a nonzero operator has one in every
canonical form.
