import Lightlike.OperatorAlgebras.Resolvent
import Lightlike.OperatorAlgebras.TestsUnitaryGroup
import Lightlike.OperatorAlgebras.StoneGenerator

/-!
# Trust checks for the resolvent

The generator of the phase group `exp (i λ t)` is `λ • 1`, a bounded self-adjoint operator, and its resolvent at
a non-real `z` is `(λ - z)⁻¹ • 1`. This tests the sign of `A - z` (not `z - A`) and the bound `1 / |Im z|`.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The resolvent of the phase-group generator is `(λ - z)⁻¹`.** -/
theorem resolvent_phaseGroup (l : ℝ) {z : ℂ} (hz : z.im ≠ 0) (y : H) :
    resolventCLM (UnitaryGroup.generator_isSelfAdjoint (phaseGroup l : UnitaryGroup H)) hz y =
      ((l : ℂ) - z)⁻¹ • y := by
  have hsa := UnitaryGroup.generator_isSelfAdjoint (phaseGroup l : UnitaryGroup H)
  have hspec := resolvent_spec hsa hz y
  set x := resolventCLM hsa hz y
  have hx := phaseGroup_generator (H := H) l x
  have hne : (l : ℂ) - z ≠ 0 := by
    intro h
    apply hz
    have := congrArg Complex.im h
    simpa using this.symm
  rw [hx, ← sub_smul] at hspec
  rw [← hspec, smul_smul, inv_mul_cancel₀ hne, one_smul]

end Lightlike.OperatorAlgebras
