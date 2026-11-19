import Lightlike.OperatorAlgebras.QuasiFree

/-!
# Checks of the quasi-free vectors

The Fock vacuum is quasi-free with `η = Re⟪·,·⟫`, and its two-point function is `½⟪f, g⟫`, the check of the corrected
form of Dereziński, Theorem 39 (1).
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras

attribute [local instance] InnerProductSpace.complexToReal

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The two-point function of the Fock vacuum is `½⟪f, g⟫` (Theorem 39 (1) for `η = Re⟪·,·⟫`). -/
theorem FockRep.inner_field_field_vacuum (R : FockRep h K) (f g : h) :
    ⟪R.toCCRRep.field f ⟨R.Ω, R.isQuasiFree_vacuum.mem_domain f⟩,
      R.toCCRRep.field g ⟨R.Ω, R.isQuasiFree_vacuum.mem_domain g⟩⟫_ℂ = (1 / 2 : ℂ) * ⟪f, g⟫_ℂ := by
  rw [R.isQuasiFree_vacuum.inner_field_field]
  apply Complex.ext
  · simp [symp, innerₗ]; rfl
  · simp [symp, innerₗ] <;> ring

/-- The sharp bound of Theorem 39 (2) is attained by the Fock vacuum: `σ(f, i f) = ‖f‖²`. -/
example (f : h) : symp h f (Complex.I • f) = ‖f‖ ^ 2 := by
  simp [symp, inner_smul_right, ← Complex.ofReal_pow, Complex.mul_im]

end Lightlike.OperatorAlgebras
