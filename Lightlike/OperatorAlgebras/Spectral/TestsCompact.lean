import Lightlike.OperatorAlgebras.Spectral.Compact
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Tests for the spectral theorem for compact self-adjoint operators

* `not_finiteDimensional_eigenspace_id`: the identity of `ℓ²(ℕ)`, symmetric but not compact, has the
  infinite-dimensional eigenspace `ℓ²(ℕ)` to the eigenvalue `1`, so the compactness hypothesis of
  `finiteDimensional_eigenspace` cannot be dropped (a wrong input);
* `not_isCompactOperator_id`: the identity of `ℓ²(ℕ)` is not compact;
* `exists_hilbertBasis_eigenvectors_of_finiteDimensional`: on a finite-dimensional space every symmetric operator is
  compact, so `exists_hilbertBasis_eigenvectors` gives the finite-dimensional spectral theorem (an orthonormal basis of
  eigenvectors with real eigenvalues).
-/

namespace Lightlike.OperatorAlgebras.CompactSpectral

open Module End

/-- The standard Hilbert basis of `ℓ²(ℕ)`. -/
noncomputable def ell2NatBasis : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

/-- `ℓ²(ℕ)` is infinite dimensional. -/
lemma not_finiteDimensional_ell2 : ¬ FiniteDimensional ℂ (lp (fun _ : ℕ => ℂ) 2) := by
  intro h
  exact Module.Finite.not_linearIndependent_of_infinite (R := ℂ) _ ell2NatBasis.orthonormal.linearIndependent

/-- **The identity of `ℓ²(ℕ)` has an infinite-dimensional eigenspace to `1`** (a wrong input for
`finiteDimensional_eigenspace`: the identity is symmetric but not compact). -/
theorem not_finiteDimensional_eigenspace_id :
    ¬ FiniteDimensional ℂ
      (eigenspace ((ContinuousLinearMap.id ℂ (lp (fun _ : ℕ => ℂ) 2) : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] _)) 1) := by
  intro h
  have htop : eigenspace ((ContinuousLinearMap.id ℂ (lp (fun _ : ℕ => ℂ) 2) : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] _)) 1 = ⊤ := by
    ext x; simp [mem_eigenspace_iff]
  rw [htop] at h
  exact not_finiteDimensional_ell2 (Submodule.topEquiv.finiteDimensional)

/-- **The identity of `ℓ²(ℕ)` is not compact.** -/
theorem not_isCompactOperator_id : ¬ IsCompactOperator (ContinuousLinearMap.id ℂ (lp (fun _ : ℕ => ℂ) 2)) := by
  intro h
  have := finiteDimensional_eigenspace h (one_ne_zero (α := ℂ))
  exact not_finiteDimensional_eigenspace_id this

/-- **The finite-dimensional spectral theorem from the compact one**: on a finite-dimensional space every symmetric
operator has an orthonormal basis of eigenvectors with real eigenvalues. -/
theorem exists_hilbertBasis_eigenvectors_of_finiteDimensional {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {T : E →L[ℂ] E} (hT' : (T : E →ₗ[ℂ] E).IsSymmetric) :
    ∃ (s : Set E) (b : HilbertBasis s ℂ E) (μ : s → ℝ), ∀ i, T (b i) = (μ i : ℂ) • b i := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  obtain ⟨s, b, μ, -, h⟩ := exists_hilbertBasis_eigenvectors (isCompactOperator_of_locallyCompactSpace_dom T) hT'
  exact ⟨s, b, μ, h⟩

end Lightlike.OperatorAlgebras.CompactSpectral
