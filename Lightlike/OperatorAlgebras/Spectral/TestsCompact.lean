import Lightlike.OperatorAlgebras.Spectral.Compact
import Lightlike.OperatorAlgebras.Spectral.HilbertSchmidtCompact
import Lightlike.OperatorAlgebras.TestsTraceClassDiag
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Tests for the spectral theorem for compact self-adjoint operators

* `not_finiteDimensional_eigenspace_id`: the identity of `ℓ²(ℕ)`, symmetric but not compact, has the
  infinite-dimensional eigenspace `ℓ²(ℕ)` to the eigenvalue `1`, so the compactness hypothesis of
  `finiteDimensional_eigenspace` cannot be dropped (a wrong input);
* `not_isCompactOperator_id`: the identity of `ℓ²(ℕ)` is not compact;
* `exists_hilbertBasis_eigenvectors_of_finiteDimensional`: on a finite-dimensional space every symmetric operator is
  compact, so `exists_hilbertBasis_eigenvectors` gives the finite-dimensional spectral theorem (an orthonormal basis of
  eigenvectors with real eigenvalues);
* `invDiag_zero_mem_spectrum_not_hasEigenvalue`: the diagonal operator `diag(1/(n+1))` on `ℓ²(ℕ)` is compact and
  self-adjoint, `0` is in its spectrum and `0` is not an eigenvalue. So Teschl's sentence "the spectrum of `K` consists of
  an at most countable number of eigenvalues" (Theorem 6.6, p. 136), read literally, fails at `0`, and the theorem is
  stated for the nonzero points of the spectrum (`hasEigenvalue_of_mem_spectrum`).
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

open TraceClass in
/-- **`0` is in the spectrum of `diag(1/(n+1))` and is not an eigenvalue**, while the operator is compact and
self-adjoint: the literal reading of "the spectrum consists of eigenvalues" (Teschl, Theorem 6.6, p. 136) fails at `0`. -/
theorem invDiag_zero_mem_spectrum_not_hasEigenvalue :
    IsCompactOperator invDiag ∧ IsSelfAdjoint invDiag ∧ (0 : ℂ) ∈ spectrum ℂ invDiag ∧
      ¬ HasEigenvalue (invDiag : Module.End ℂ L2N) 0 := by
  have hw : ∀ n : ℕ, ‖invWeight n‖ = ((n : ℝ) + 1)⁻¹ := fun n => by
    rw [invWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hstd : ∀ n, ‖stdVec n‖ = 1 := fun n => by
    rw [stdVec, lp.norm_single (by norm_num), norm_one]
  refine ⟨isCompactOperator_of_isHilbertSchmidt invDiag_isHilbertSchmidt, IsSelfAdjoint.of_nonneg invDiag_nonneg,
    ?_, ?_⟩
  · -- `D` is not invertible: `‖D eₙ‖ = 1/(n+1) → 0`
    rw [spectrum.zero_mem_iff]
    rintro ⟨u, hu⟩
    obtain ⟨n, hn⟩ := exists_nat_gt ‖(↑u⁻¹ : L2N →L[ℂ] L2N)‖
    have h1 : stdVec n = (↑u⁻¹ : L2N →L[ℂ] L2N) (invDiag (stdVec n)) := by
      rw [← hu, ← ContinuousLinearMap.mul_apply, Units.inv_mul, ContinuousLinearMap.one_apply]
    have h2 : invDiag (stdVec n) = invWeight n • stdVec n := diagOp_stdVec invWeight norm_invWeight_le n
    have h3 : (1 : ℝ) ≤ ‖(↑u⁻¹ : L2N →L[ℂ] L2N)‖ * ((n : ℝ) + 1)⁻¹ := by
      calc (1 : ℝ) = ‖stdVec n‖ := (hstd n).symm
        _ = ‖(↑u⁻¹ : L2N →L[ℂ] L2N) (invWeight n • stdVec n)‖ := by rw [← h2, ← h1]
        _ ≤ ‖(↑u⁻¹ : L2N →L[ℂ] L2N)‖ * ‖invWeight n • stdVec n‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖(↑u⁻¹ : L2N →L[ℂ] L2N)‖ * ((n : ℝ) + 1)⁻¹ := by rw [norm_smul, hw, hstd, mul_one]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul] at h3
    linarith
  · -- `D` is injective
    intro h0
    obtain ⟨v, hv, hv0⟩ := h0.exists_hasEigenvector
    have hDv : invDiag v = 0 := by simpa using hv
    apply hv0
    ext n
    have hn := congrArg (fun F : L2N => F n) hDv
    simp only [diagOp_apply, invDiag] at hn
    have hne : invWeight n ≠ 0 := by
      rw [← norm_ne_zero_iff, hw]; positivity
    simpa [hne] using hn

end Lightlike.OperatorAlgebras.CompactSpectral
