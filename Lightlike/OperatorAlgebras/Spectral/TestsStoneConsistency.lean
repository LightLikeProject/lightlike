import Lightlike.OperatorAlgebras.Spectral.StoneConsistency
import Lightlike.OperatorAlgebras.TestsUnitaryGroup

/-!
# Trust checks of the spectral exponential group

For the phase group `t ↦ e^{iλt}`, whose generator is `λ • 1`, the group built from the spectral theorem is the phase group
itself, and it is not the phase group of another frequency. So `spectralGroup` is not a placeholder and the hypotheses of the
spectral theorem are met by a concrete operator.
-/

namespace Lightlike.OperatorAlgebras.Spectral.Stone

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The spectral group of the phase generator is the phase group.** -/
theorem spectralGroup_phaseGroup (l : ℝ) :
    spectralGroup (phaseGroup_generator_isSelfAdjoint (H := H) l) = phaseGroup l :=
  UnitaryGroup.eq_of_generator_eq (by rw [spectralGroup_generator])

end Lightlike.OperatorAlgebras.Spectral.Stone
