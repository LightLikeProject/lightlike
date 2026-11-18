import Lightlike.OperatorAlgebras.Spectral.StoneBridge
import Lightlike.OperatorAlgebras.StoneUnique
import Lightlike.OperatorAlgebras.YosidaLimit

/-!
# The two constructions of `e^{itA}` agree

For a self-adjoint `A`, the group `Spectral.Stone.spectralGroup hA` comes from the spectral theorem (the ported development),
and `OperatorAlgebras.stoneGroup hA` is the strong limit of the Yosida approximations. Both are `UnitaryGroup`s with generator
`A` (`spectralGroup_generator`, `generator_stoneGroup`), and a `UnitaryGroup` is determined by its generator
(`UnitaryGroup.eq_of_generator_eq`), so they are equal.
-/

namespace Lightlike.OperatorAlgebras.Spectral.Stone

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The group built from the spectral theorem equals the group built from the Yosida approximations. -/
theorem spectralGroup_eq_stoneGroup {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    spectralGroup hA = stoneGroup hA :=
  UnitaryGroup.eq_of_generator_eq (by rw [spectralGroup_generator, generator_stoneGroup])

end Lightlike.OperatorAlgebras.Spectral.Stone
