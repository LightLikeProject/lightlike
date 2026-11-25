import Lightlike.OperatorAlgebras.CARShale

/-!
# Tests for the fermionic Shale sufficiency

The identity map has antilinear part `0`, so the small-`β` hypothesis holds with `h = 0` and the theorem gives an
implementer (the identity is one, but the statement is checked as an instance).
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras.CARShale

variable {ι : Type*} [LinearOrder ι] {Γ : Type*} [NormedAddCommGroup Γ] [InnerProductSpace ℂ Γ] [CompleteSpace Γ]
  {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]

/-- The antilinear part of the identity vanishes. -/
example (w : Z) : betaPart (LinearMap.id : Z →ₗ[ℝ] Z) w = 0 := by
  simp [betaPart, smul_smul]

/-- The identity is implemented, by the theorem under the bound `h = 0 < 1`. -/
example [DecidableEq ι] (B : HilbertBasis (Finset ι) ℂ Γ) (b : HilbertBasis ι ℂ Z) :
    ∃ U : Γ ≃ₗᵢ[ℂ] Γ, ∀ w x, U (fockField B b w x) = fockField B b ((LinearMap.id : Z →ₗ[ℝ] Z) w) (U x) :=
  fermionic_shale_of_small B b LinearMap.id (fun _ _ => rfl) Function.surjective_id 0 zero_lt_one
    (fun F => by simp [betaPart, smul_smul])

end Lightlike.OperatorAlgebras.CARShale
