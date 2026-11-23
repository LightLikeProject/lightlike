import Mathlib

/-!
# Proper-time cutoff integrals (monomials)

For the one-loop effective action `Γ = -(1/2) ∫_ε^1 dt/t Tr e^{-tD}` in dimension 4 the heat
expansion `Tr e^{-tD} ~ a₀ t^{-2} + a₁ t^{-1} + a₂ + …` produces the monomial integrals
`∫_ε^1 t^{-3}`, `∫_ε^1 t^{-2}`, `∫_ε^1 t^{-1}`, computed here.
-/

open intervalIntegral MeasureTheory

noncomputable section

namespace Lightlike.HeatKernel

private lemma zero_notMem_uIcc {ε : ℝ} (hε : 0 < ε) : (0 : ℝ) ∉ Set.uIcc ε 1 := by
  rw [Set.mem_uIcc]
  rintro (h | h) <;> linarith [h.1, h.2]

/-- `∫_ε^1 t^{-3} dt = (ε^{-2} - 1)/2`. -/
theorem cutoff_integral_inv_cube {ε : ℝ} (hε : 0 < ε) :
    ∫ t in ε..1, t ^ (-3 : ℤ) = (ε ^ (-2 : ℤ) - 1) / 2 := by
  rw [integral_zpow (Or.inr ⟨by norm_num, zero_notMem_uIcc hε⟩)]
  norm_num
  ring

/-- `∫_ε^1 t^{-2} dt = ε^{-1} - 1`. -/
theorem cutoff_integral_inv_sq {ε : ℝ} (hε : 0 < ε) :
    ∫ t in ε..1, t ^ (-2 : ℤ) = ε⁻¹ - 1 := by
  rw [integral_zpow (Or.inr ⟨by norm_num, zero_notMem_uIcc hε⟩)]
  norm_num
  ring

/-- `∫_ε^1 t^{-1} dt = -log ε`. -/
theorem cutoff_integral_inv {ε : ℝ} (hε : 0 < ε) :
    ∫ t in ε..1, t⁻¹ = -Real.log ε := by
  rw [integral_inv_of_pos hε one_pos]
  simp

end Lightlike.HeatKernel
