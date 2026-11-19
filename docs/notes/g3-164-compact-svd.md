# G3-164 (compact operators): the canonical form and the singular values

Source read: G. Teschl, *Mathematical Methods in Quantum Mechanics, With Applications to Schrödinger Operators*, Graduate
Studies in Mathematics 99, American Mathematical Society (2009), online edition (source key `teschl-2009`), Section 6.2,
Theorem 6.7 with its proof and (6.7), p. 137.

| Source | Library | Check |
|---|---|---|
| Theorem 6.7: orthonormal sets `{φ̂ⱼ}`, `{φⱼ}` and positive `sⱼ` with `K = ∑ⱼ sⱼ ⟪φⱼ, ·⟫ φ̂ⱼ`, `K* = ∑ⱼ sⱼ ⟪φ̂ⱼ, ·⟫ φⱼ` (6.6) | `IsCanonicalForm K φ φ' s` (orthonormal families `φ`, `φ'`, `s > 0`, `HasSum` for `K x` and `K* x`), `exists_isCanonicalForm`, `isCanonicalForm_of_eigenbasis` | (representation) families indexed by a type; the series are stated pointwise |
| "`Kφⱼ = sⱼ φ̂ⱼ` and `K*φ̂ⱼ = sⱼ φⱼ`, and hence `K*Kφⱼ = sⱼ²φⱼ` and `KK*φ̂ⱼ = sⱼ²φ̂ⱼ`" | the same theorem | matches |
| "The numbers `sⱼ(K)² > 0` are the nonzero eigenvalues of `KK*`, respectively `K*K` (counted with multiplicity)" | the eigenvector relations above | (weaker) that every nonzero eigenvalue occurs, with its multiplicity, is not stated |
| "There are either finitely many singular values (if `K` is finite rank) or they converge to zero" | `{j \| ε ≤ sⱼ}` finite for every `ε > 0` | (representation) the two cases are one statement; the finite-rank remark is not stated |
| (6.7): `‖K‖ = maxⱼ sⱼ(K)` | `IsCanonicalForm.le_opNorm` (`sⱼ ≤ ‖K‖`), `IsCanonicalForm.opNorm_le` (`‖K‖ ≤ M` when all `sⱼ ≤ M`), for every canonical form | (representation) the maximum is stated as the least upper bound (that it is attained is not stated) |

Proof as in the source (`isCanonicalForm_of_eigenbasis`): Theorem 6.6 (`exists_hilbertBasis_eigenvectors`) for the compact symmetric `K*K`, `sⱼ = √μⱼ` on the
eigenvectors with `μⱼ > 0`, `φ'ⱼ = sⱼ⁻¹ K φⱼ` (orthonormal since `⟪Kφᵢ, Kφⱼ⟫ = μⱼ ⟪φᵢ, φⱼ⟫`), and `K bᵢ = 0` when `μᵢ = 0`.
Finitely many `sⱼ ≥ ε`: the `sⱼ²` are eigenvalues of `K*K`, finitely many of size at least `ε²`, each with a
finite-dimensional eigenspace holding the orthonormal `φⱼ` of that eigenvalue.

Mathlib's `LinearMap.singularValues` is for finite-dimensional spaces only.

Tests (`Spectral/TestsCanonicalForm.lean`): the zero operator has no singular values; a nonzero operator has one in every
canonical form.
