import Lightlike.OperatorAlgebras.VonNeumann
import Lightlike.OperatorAlgebras.StoneGenerator
import Lightlike.OperatorAlgebras.TestsUnitaryGroup

/-!
# Trust checks for von Neumann's criterion

Non-vacuity: the generator of the phase group `t ↦ exp (i l t)` on `ℂ` (multiplication by `l`) is closed symmetric, and its deficiency
spaces at `± i` are trivial, so the hypotheses of `isSelfAdjoint_of_deficiency_bot` are met by a concrete operator.
-/

namespace Lightlike.OperatorAlgebras

/-- **Non-vacuity**: the generator of the phase group on `ℂ` is closed symmetric with trivial deficiency spaces at `± i`. -/
theorem phaseGroup_generator_closedSymm_deficiency (l : ℝ) :
    ClosedSymm (phaseGroup l : UnitaryGroup ℂ).generator ∧
      deficiencySpace (phaseGroup l : UnitaryGroup ℂ).generator Complex.I = ⊥ ∧
      deficiencySpace (phaseGroup l : UnitaryGroup ℂ).generator (-Complex.I) = ⊥ := by
  have hsa := (phaseGroup l : UnitaryGroup ℂ).generator_isSelfAdjoint
  exact ⟨ClosedSymm.of_isSelfAdjoint hsa, ((isSelfAdjoint_iff_deficiency_bot (ClosedSymm.of_isSelfAdjoint hsa)).mp hsa)⟩

end Lightlike.OperatorAlgebras
