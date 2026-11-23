import Mathlib
import Lightlike.Rows.G1_062.SphereExpansion
import Lightlike.Rows.G1_062.Product

/-!
# Tests for row G1-062 (heat-trace trust checks of T-GE8)

Statement-shape checks: the sphere check has `a₀ = 1`, `a₁ = 1/3`, `a₂ = 1/15` in dimension 2,
and the torus check has no constant term.
-/

open Lightlike.Rows.G1_062

example : HasHeatExpansion sphereTrace 2 sphereCoeff 3 := sphereTrace_hasHeatExpansion
example : sphereCoeff 0 = 1 ∧ sphereCoeff 1 = 1 / 3 ∧ sphereCoeff 2 = 1 / 15 := by
  simp [sphereCoeff]
example : (4 * Real.pi)⁻¹ * ((2 / 6) * (4 * Real.pi)) = sphereCoeff 1 := by
  simpa [sphereCoeff] using sphere_a1_check

#print axioms sphereTrace_hasHeatExpansion
#check @torusTrace_hasHeatExpansion
#check @torusTrace_no_constant_term
