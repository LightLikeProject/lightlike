import Lightlike.OperatorAlgebras.MomentumDeficiency

/-!
# Trust checks for the deficiency spaces of `momentumMin`

The deficiency spaces are not trivial and the exponentials sit at the right sign: `exp (-x)` is in the
deficiency space at `i` and `exp (x)` at `-i`, and both are nonzero vectors of `L²(0, 1)`. So the
dimension-one statement of `T-OP1-P5` is about nonzero spaces.
-/

namespace Lightlike.OperatorAlgebras

/-- `exp (-x)` is a nonzero vector of the deficiency space of `momentumMin` at `i`. -/
theorem expL2_neg_mem_deficiency_I :
    expL2 (-1) ∈ deficiencySpace momentumMin Complex.I ∧ expL2 (-1) ≠ 0 :=
  ⟨expL2_mem_deficiency (by simp), expL2_ne_zero _⟩

/-- `exp (x)` is a nonzero vector of the deficiency space of `momentumMin` at `-i`. -/
theorem expL2_mem_deficiency_negI :
    expL2 1 ∈ deficiencySpace momentumMin (-Complex.I) ∧ expL2 1 ≠ 0 :=
  ⟨expL2_mem_deficiency (by simp), expL2_ne_zero _⟩

end Lightlike.OperatorAlgebras
