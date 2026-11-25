import Lightlike.OperatorAlgebras.StoneMomentum.MomentumCapstone
import Lightlike.OperatorAlgebras.TestsTranslationCore
import Lightlike.OperatorAlgebras.TestsUnitaryGroup

/-!
# Tests for the OP1 capstone

Non-vacuity: the domain of `momentumSmoothR` contains a nonzero vector, so the essential
self-adjointness statement is not about the zero operator; Stone's theorem applies to the phase
group of a one-dimensional space and returns that group; the hypotheses of the deficiency theorem
are non-empty (the space `L²(0, 1)` has a dense domain of `momentumMin`).
-/

namespace Lightlike.OperatorAlgebras.OPRow154

/-- The domain of the momentum operator on `C_c^∞(ℝ)` has a nonzero vector. -/
theorem momentumSmoothR_domain_ne_bot : ∃ f ∈ momentumSmoothR.domain, f ≠ 0 := by
  rw [momentumSmoothR_domain]
  exact smoothCS_exists_ne_zero

/-- Stone's theorem on `ℂ` returns the phase group of its generator. -/
theorem stone_phaseGroup (l : ℝ) :
    ∃! U : UnitaryGroup ℂ, U.generator = (phaseGroup l : UnitaryGroup ℂ).generator :=
  stone_theorem.2 _ (phaseGroup l : UnitaryGroup ℂ).generator_isSelfAdjoint

end Lightlike.OperatorAlgebras.OPRow154
