import Lightlike.OperatorAlgebras.VonNeumannClassify
import Lightlike.OperatorAlgebras.StoneGenerator
import Lightlike.OperatorAlgebras.TestsUnitaryGroup

/-!
# Trust checks for von Neumann's criterion

Non-vacuity: the generator of the phase group `t ↦ exp (i l t)` on `ℂ` (multiplication by `l`) is closed symmetric, and its deficiency
spaces at `± i` are trivial, so the hypotheses of `isSelfAdjoint_of_deficiency_bot` are met by a concrete operator; and it is its own
self-adjoint extension, so the classification `eq_extU_of_selfAdjoint` and the index equality apply to it (with `n₊ = n₋ = 0`). A check
with `n₊ = n₋ = 1` (the momentum on an interval) is open.
-/

namespace Lightlike.OperatorAlgebras

/-- **Non-vacuity**: the generator of the phase group on `ℂ` is closed symmetric with trivial deficiency spaces at `± i`. -/
theorem phaseGroup_generator_closedSymm_deficiency (l : ℝ) :
    ClosedSymm (phaseGroup l : UnitaryGroup ℂ).generator ∧
      deficiencySpace (phaseGroup l : UnitaryGroup ℂ).generator Complex.I = ⊥ ∧
      deficiencySpace (phaseGroup l : UnitaryGroup ℂ).generator (-Complex.I) = ⊥ := by
  have hsa := (phaseGroup l : UnitaryGroup ℂ).generator_isSelfAdjoint
  exact ⟨ClosedSymm.of_isSelfAdjoint hsa, ((isSelfAdjoint_iff_deficiency_bot (ClosedSymm.of_isSelfAdjoint hsa)).mp hsa)⟩

/-- **Non-vacuity of the classification**: the phase-group generator, a self-adjoint extension of itself, is `A_U` for its unitary `U`,
and its deficiency indices agree. -/
theorem phaseGroup_generator_classification (l : ℝ) :
    (phaseGroup l : UnitaryGroup ℂ).generator =
        extU (phaseGroup l : UnitaryGroup ℂ).generator
          (unitaryOfExt (ClosedSymm.of_isSelfAdjoint (phaseGroup l : UnitaryGroup ℂ).generator_isSelfAdjoint) le_rfl
            (phaseGroup l : UnitaryGroup ℂ).generator_isSelfAdjoint) ∧
      deficiencyDim (phaseGroup l : UnitaryGroup ℂ).generator Complex.I =
        deficiencyDim (phaseGroup l : UnitaryGroup ℂ).generator (-Complex.I) :=
  ⟨eq_extU_of_selfAdjoint _ le_rfl _, deficiencyDim_eq_of_selfAdjoint_ext
    (ClosedSymm.of_isSelfAdjoint (phaseGroup l : UnitaryGroup ℂ).generator_isSelfAdjoint) le_rfl
    (phaseGroup l : UnitaryGroup ℂ).generator_isSelfAdjoint⟩

end Lightlike.OperatorAlgebras
