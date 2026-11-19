import Lightlike.OperatorAlgebras.MomentumTheta

/-!
# Checks for the self-adjoint extensions of the momentum

Non-vacuity and negative controls: the constant `1` lies in the periodic domain `D_0` and not in the antiperiodic domain `D_π`, so
`P_0 ≠ P_π`; and the closure of the momentum is not `P_0` (it is not self-adjoint).
-/

open MeasureTheory Set intervalIntegral
open scoped InnerProductSpace LinearPMap

namespace Lightlike.OperatorAlgebras

/-- Non-vacuity: the constant function `1` lies in the periodic domain `D₀` (`θ = 0`). -/
theorem linVec_one_mem_domTheta_zero : linVec 1 1 ∈ domTheta 0 := by
  refine mem_domTheta.mpr ⟨linVec_mem 1 1, ?_⟩
  obtain ⟨h0, h1⟩ := bv_linVec 1 1
  rw [h0, h1]
  simp

/-- Negative control: the constant function `1` is not in the antiperiodic domain (`θ = π`). -/
theorem linVec_one_not_mem_domTheta_pi : linVec 1 1 ∉ domTheta Real.pi := by
  intro hmem
  obtain ⟨h, hb⟩ := mem_domTheta.mp hmem
  obtain ⟨h0, h1⟩ := bv_linVec 1 1
  have e0 : bv0 ⟨linVec 1 1, h⟩ = 1 := h0
  have e1 : bv1 ⟨linVec 1 1, h⟩ = 1 := h1
  rw [e0, e1, Complex.exp_pi_mul_I] at hb
  norm_num at hb

/-- The family `P_θ` is not constant: the periodic and the antiperiodic extensions differ. -/
theorem momentumTheta_zero_ne_pi : momentumTheta 0 ≠ momentumTheta Real.pi := by
  intro h
  have hd := congrArg LinearPMap.domain h
  rw [momentumTheta_domain, momentumTheta_domain] at hd
  exact linVec_one_not_mem_domTheta_pi (hd ▸ linVec_one_mem_domTheta_zero)

/-- The closure of the momentum is not self-adjoint: it lies strictly inside `P_0`. -/
theorem closure_ne_momentumTheta : momentumMin.closure ≠ momentumTheta 0 := by
  intro h
  have hmem : linVec 1 1 ∈ momentumMin.closure.domain := by
    rw [h, momentumTheta_domain]; exact linVec_one_mem_domTheta_zero
  obtain ⟨b0, -⟩ := bv_closure ⟨linVec 1 1, hmem⟩
  obtain ⟨h0, -⟩ := bv_linVec 1 1
  have e0 : bv0 ⟨linVec 1 1, closure_le_adjoint.1 hmem⟩ = 1 := h0
  have b0' : bv0 ⟨linVec 1 1, closure_le_adjoint.1 hmem⟩ = 0 := b0
  rw [e0] at b0'
  exact one_ne_zero b0'

end Lightlike.OperatorAlgebras
