import Mathlib
import Lightlike.Geometry.HeatKernel.ChartOperatorBound
import Lightlike.Geometry.HeatKernel.ChartParametrixTests

/-!
# Tests: the parametrix operators are bounded on `C^ℓ`

Non-vacuity of `Lightlike.IsChartParametrix.exists_operator_bound` for the flat metric of the line, at every order and
every derivative order, with the zero test function (all hypotheses hold, `M = 0`). Trust checks of
`one_add_pow_mul_exp_neg_le` at `u = 0` and of `exists_integral_poly_gauss_le`.
-/

open Set Real Nat MeasureTheory
open scoped ContDiff
noncomputable section
namespace Lightlike.ChartOperatorBoundTests

open Lightlike.LaplaceBeltramiTests Lightlike.ChartParametrixTests

example (ℓ : ℕ) : (1 + 0) ^ ℓ * Real.exp (-(1 * 0)) ≤ 2 ^ ℓ * (1 + ℓ ! * (2 / 1) ^ ℓ) * Real.exp (-(1 * 0) / 2) :=
  one_add_pow_mul_exp_neg_le one_pos le_rfl ℓ

example (ℓ : ℕ) : ∃ J : ℝ, Integrable (fun v : Fin 2 → ℝ => (1 + ‖v‖ ^ 2) ^ ℓ * Real.exp (-(1 * ‖v‖ ^ 2))) ∧
    ∫ v : Fin 2 → ℝ, (1 + ‖v‖ ^ 2) ^ ℓ * Real.exp (-(1 * ‖v‖ ^ 2)) ≤ J :=
  exists_integral_poly_gauss_le ℓ one_pos

example (N ℓ : ℕ) : ∃ H : ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ, ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1,
    ContDiff ℝ ∞ (fun w => ∫ p, H t p w * (0 : ℝ)) ∧
      ∀ w, ‖iteratedFDeriv ℝ ℓ (fun w => ∫ p, H t p w * (0 : ℝ)) w‖ ≤ C * 0 := by
  obtain ⟨r, u, H, Ω, θ, σ, V, h⟩ := exists_isChartParametrix isRiemMetric_gLine (mem_univ 0) N
  obtain ⟨ρ, -, -, hb⟩ := h.exists_operator_bound isCoordMetric_gLine
  obtain ⟨C, -, hC⟩ := hb ℓ
  exact ⟨H, C, fun t ht => hC t ht (fun _ => 0) contDiff_const (fun _ _ => rfl) 0 fun i _ p => by
    rw [iteratedFDeriv_fun_zero]; simp⟩

end Lightlike.ChartOperatorBoundTests
