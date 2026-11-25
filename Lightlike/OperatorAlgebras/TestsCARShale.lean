import Lightlike.OperatorAlgebras.CARShale
import Lightlike.OperatorAlgebras.CARShaleMain
import Lightlike.OperatorAlgebras.CARShaleNec

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

/-- The criterion for the identity: the antilinear part vanishes, so the square sum converges. -/
example {ι : Type*} [LinearOrder ι] {Γ : Type*} [NormedAddCommGroup Γ] [InnerProductSpace ℂ Γ] [CompleteSpace Γ]
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z] (B : HilbertBasis (Finset ι) ℂ Γ)
    (b : HilbertBasis ι ℂ Z) :
    (∃ U : Γ ≃ₗᵢ[ℂ] Γ, ∀ v x, U (fockField B b v x) = fockField B b ((LinearMap.id : Z →ₗ[ℝ] Z) v) (U x)) ↔
      Summable fun j : ι => ‖betaPart (LinearMap.id : Z →ₗ[ℝ] Z) (b j)‖ ^ 2 :=
  fermionic_shale_iff B b LinearMap.id (fun _ _ => rfl) Function.surjective_id

end Lightlike.OperatorAlgebras.CARShale

namespace Lightlike.OperatorAlgebras.CARShale

/-- The identity map has Hilbert-Schmidt antilinear part for every Hilbert basis (it is `0`), so the general theorem
applies to it. -/
example {ι : Type*} [LinearOrder ι] {Γ : Type*} [NormedAddCommGroup Γ] [InnerProductSpace ℂ Γ] [CompleteSpace Γ]
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z] (B : HilbertBasis (Finset ι) ℂ Γ)
    (b : HilbertBasis ι ℂ Z) (w : Set Z) (c : HilbertBasis w ℂ Z) :
    ∃ U : Γ ≃ₗᵢ[ℂ] Γ, ∀ v x, U (fockField B b v x) = fockField B b ((LinearMap.id : Z →ₗ[ℝ] Z) v) (U x) :=
  fermionic_shale_of_HS B b LinearMap.id (fun _ _ => rfl) Function.surjective_id
    ⟨w, c, by simp [betaPart, smul_smul, summable_zero]⟩

end Lightlike.OperatorAlgebras.CARShale
