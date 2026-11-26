import Lightlike.OperatorAlgebras.TraceClass.TracePairingSurjectivity

/-!
# The dual of the trace class is the bounded operators

`(S₁)* ≅ B(H)`: the trace pairing `A ↦ Tr (A ·)` is an isometric linear isomorphism from the bounded
operators onto the continuous dual of the trace-class operators, on every complex Hilbert space.

* `TraceClass.tracePairingLinearIsometryEquiv`: the isometric isomorphism (isometry:
  `TracePairingNorm.lean`, surjectivity: `TracePairingSurjectivity.lean`).
* `traceClass_dual_eq_bounded`: every continuous functional `φ` on the trace class is `Tr (A ·)` for a
  unique bounded operator `A`, of norm `‖φ‖`.

The compact-operator companion is `compact_dual_eq_traceClass_proof` (`CompactDualIso.lean`): `K* ≅ S₁`.
-/

noncomputable section

namespace Lightlike.OperatorAlgebras.TraceClass

namespace TraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The trace pairing as an isometric isomorphism** `B(H) ≃ₗᵢ (S₁)*`. -/
def tracePairingLinearIsometryEquiv : (H →L[ℂ] H) ≃ₗᵢ[ℂ] (TraceClass H →L[ℂ] ℂ) :=
  LinearIsometryEquiv.ofSurjective tracePairingLinearIsometry tracePairing_surjective_concrete

/-- The isometric isomorphism is the trace pairing. -/
@[simp] lemma tracePairingLinearIsometryEquiv_apply (A : H →L[ℂ] H) :
    tracePairingLinearIsometryEquiv A = tracePairing A := rfl

/-- **`(S₁)* ≅ B(H)`**: every continuous functional on the trace-class operators is the trace
pairing with a unique bounded operator `A`, and `‖A‖ = ‖φ‖`. -/
theorem traceClass_dual_eq_bounded (φ : TraceClass H →L[ℂ] ℂ) :
    ∃ A : H →L[ℂ] H, tracePairing A = φ ∧ ‖A‖ = ‖φ‖ ∧
      ∀ A' : H →L[ℂ] H, tracePairing A' = φ → A' = A := by
  refine ⟨tracePairingLinearIsometryEquiv.symm φ, ?_, ?_, ?_⟩
  · rw [← tracePairingLinearIsometryEquiv_apply]
    exact tracePairingLinearIsometryEquiv.apply_symm_apply φ
  · exact (tracePairingLinearIsometryEquiv.symm.norm_map φ)
  · intro A' hA'
    apply tracePairingLinearIsometryEquiv.injective
    rw [tracePairingLinearIsometryEquiv_apply, hA']
    exact (tracePairingLinearIsometryEquiv.apply_symm_apply φ).symm

end TraceClass

end Lightlike.OperatorAlgebras.TraceClass
