import Lightlike.OperatorAlgebras.SecondQuantization

/-!
# Checks of the second quantization of unitaries
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `Γ(U) Γ(U⁻¹) = 1`. -/
theorem FockRep.secondQuant_trans_symm (R : FockRep h K) (U : h ≃ₗᵢ[ℂ] h) :
    (R.secondQuant U).trans (R.secondQuant U.symm) = LinearIsometryEquiv.refl ℂ K := by
  rw [← R.secondQuant_trans, LinearIsometryEquiv.self_trans_symm, R.secondQuant_refl]

/-- `Γ(U)` preserves the Fock expectation: `⟪Ω, Γ(U)* W(f) Γ(U) Ω⟫ = ⟪Ω, W(U f) Ω⟫`. -/
example (R : FockRep h K) (U : h ≃ₗᵢ[ℂ] h) (f : h) :
    ⟪R.secondQuant U R.Ω, R.secondQuant U (R.W f R.Ω)⟫_ℂ = ⟪R.Ω, R.W (U f) R.Ω⟫_ℂ := by
  rw [R.secondQuant_W, R.secondQuant_vacuum]

/-- `Γ(0)` is the projection onto the vacuum, `ψ ↦ ⟪Ω, ψ⟫ Ω`. -/
theorem FockRep.gamma_zero (R : FockRep h K) : R.gamma 0 = (innerSL ℂ R.Ω).smulRight R.Ω :=
  R.clm_ext_W_Ω fun f => by
    rw [R.gamma_W_Ω (by simp), ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, R.vacuum_expectation,
      ContinuousLinearMap.zero_apply, R.toCCRRep.W_zero_apply]
    congr 1
    simp only [cohFactor, ContinuousLinearMap.zero_apply, norm_zero]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring

end Lightlike.OperatorAlgebras
