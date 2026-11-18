import Lightlike.OperatorAlgebras.YosidaLimit
import Lightlike.OperatorAlgebras.StoneUnique
import Lightlike.OperatorAlgebras.TestsUnitaryGroup

/-!
# Trust checks for the existence part of Stone's theorem

For the generator `A` of the phase group `exp (i λ t)` (the bounded self-adjoint operator `λ • 1`), the unitary
group constructed from `A` by the Yosida approximation is the phase group: existence (`stoneGroup`) and
uniqueness (`UnitaryGroup.eq_of_generator_eq`) agree. So the construction has the sign convention
`U t = exp (i t A)` and is not a different group with the same generator.
-/

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The Yosida group of the phase-group generator is the phase group.** -/
theorem stoneGroup_phaseGroup (l : ℝ) :
    stoneGroup (UnitaryGroup.generator_isSelfAdjoint (phaseGroup l : UnitaryGroup H)) =
      phaseGroup l :=
  UnitaryGroup.eq_of_generator_eq
    (generator_stoneGroup (UnitaryGroup.generator_isSelfAdjoint (phaseGroup l : UnitaryGroup H)))

end Lightlike.OperatorAlgebras
