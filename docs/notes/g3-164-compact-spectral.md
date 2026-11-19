# G3-164 (compact operators): the spectral theorem for compact self-adjoint operators

Source read: G. Teschl, *Mathematical Methods in Quantum Mechanics, With Applications to Schrödinger Operators*, Graduate
Studies in Mathematics 99, American Mathematical Society (2009), online edition (source key `teschl-2009`), Section 6.2,
Theorem 6.6, p. 136, with its proof, and the canonical form, Theorem 6.7, p. 137, which uses it.

| Source | Library | Check |
|---|---|---|
| Theorem 6.6, p. 136: `K` self-adjoint and compact | `IsCompactOperator T` and `(T : E →ₗ[𝕜] E).IsSymmetric` for `T : E →L[𝕜] E` on a Hilbert space over `ℝ` or `ℂ` | matches (a bounded symmetric operator is self-adjoint) |
| p. 136: "Then the spectrum of `K` consists of an at most countable number of eigenvalues which can only cluster at `0`" | `countable_spectrum`, `countable_eigenvalues`, `hasEigenvalue_of_mem_spectrum` (`μ ≠ 0` in the spectrum is an eigenvalue, from Mathlib's Fredholm alternative) | (convention) `σ(K) \ {0}` consists of eigenvalues; read literally, the sentence fails at `0`: `invDiag_zero_mem_spectrum_not_hasEigenvalue` (`diag(1/(n+1))` on `ℓ²(ℕ)` is compact and self-adjoint, `0 ∈ σ`, and `0` is not an eigenvalue) |
| "which can only cluster at `0`" | `finite_eigenvalues_ge`: for `ε > 0` only finitely many eigenvalues have `‖μ‖ ≥ ε` | matches |
| "the eigenspace to each nonzero eigenvalue is finite dimensional" | `finiteDimensional_eigenspace` (Mathlib's `ContinuousLinearMap.finite_dimensional_eigenspace`) | matches |
| (6.5): `K = ∑_{λ ∈ σ(K)} λ P_K({λ})` | `exists_hilbertBasis_eigenvectors` (a Hilbert basis of eigenvectors, real eigenvalues) and `hasSum_eigen` (`T x = ∑ᵢ μᵢ ⟪bᵢ, x⟫ bᵢ`) | (representation) the sum over eigenvalues with the spectral projections is written over a Hilbert basis of eigenvectors; the vectors with eigenvalue `λ` span the range of `P_K({λ})` |

Tests (`Spectral/TestsCompact.lean`): the identity of `ℓ²(ℕ)` has an infinite-dimensional eigenspace and is not compact
(the hypothesis cannot be dropped); in finite dimensions the theorem gives an orthonormal eigenbasis of every symmetric
operator; `0` is in the spectrum of the compact self-adjoint `diag(1/(n+1))` and is not an eigenvalue (its compactness
from `isCompactOperator_of_isHilbertSchmidt`, Teschl p. 139, in `Spectral/HilbertSchmidtCompact.lean`).

Mathlib (in this repository's version) proves the density of the sum of the eigenspaces
(`orthogonalComplement_iSup_eigenspaces_eq_bot`), and the Hilbert basis is assembled from Hilbert bases of the
eigenspaces (`OrthogonalFamily.orthonormal_sigma_orthonormal`).

Row G3-164 ("Compact and trace-class operators, Hilbert–Schmidt, Schatten norms"): this is the compact-operator part.
The Schatten classes (Teschl (6.19)-(6.23), Lemma 6.12) need the singular values of Theorem 6.7 and are open.
