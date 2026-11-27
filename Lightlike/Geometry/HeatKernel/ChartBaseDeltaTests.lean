import Mathlib
import Lightlike.Geometry.HeatKernel.ChartBaseDelta
import Lightlike.Geometry.HeatKernel.ChartParametrixTests

/-!
# Tests: the delta property of the chart parametrix in the base point

Non-vacuity of `Lightlike.IsChartParametrix.base_delta` for the flat metric of the line, with the zero test function
(the hypotheses hold and the limit is `0`). Trust check of `gauss_sub_gauss_le` with `a = b` (the left side is `0`),
and of `IsCoordMetric.exists_quad_lipschitz` for the constant metric (the bound holds).
-/

open Set Real Matrix
noncomputable section
namespace Lightlike.ChartBaseDeltaTests

open Lightlike.LaplaceBeltramiTests Lightlike.ChartParametrixTests

example (N : ℕ) : ∃ H : ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ, ∃ ρ > 0, ∀ ε > 0, ∃ t₀ > 0, ∀ t ∈ Ioo (0 : ℝ) t₀,
    ∀ y : Fin 1 → ℝ, ‖y‖ < ρ → |(∫ p, H t p y * 0) - 0 / √(gLine y).det| ≤ ε := by
  obtain ⟨r, u, H, Ω, θ, σ, V, h⟩ := exists_isChartParametrix isRiemMetric_gLine (mem_univ 0) N
  obtain ⟨ρ, hρ, -, hd⟩ := h.base_delta isRiemMetric_gLine
  refine ⟨H, ρ, hρ, fun ε hε => ?_⟩
  obtain ⟨t₀, ht₀, ht⟩ := hd (fun _ => 0) continuous_const (fun _ _ => rfl) ε hε
  exact ⟨t₀, ht₀, fun t htt y hy => ht t htt y (by simpa using hy)⟩

example {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (z : Fin 2 → ℝ) :
    |Real.exp (-‖z‖ ^ 2 / (4 * t)) - Real.exp (-‖z‖ ^ 2 / (4 * t))| ≤
      (0 * 2 * √(4 / 1) ^ 3 + 64 / (1 ^ 2 * 1)) * √t * Real.exp (-(1 * ‖z‖ ^ 2 / (4 * t)) / 2) :=
  gauss_sub_gauss_le ht ht1 one_pos one_pos le_rfl (by simp) (by simp) (fun _ => by simp)

example : ∃ ρ L : ℝ, 0 < ρ ∧ 0 ≤ L ∧ ∀ p y : Fin 1 → ℝ, ‖p - 0‖ < ρ → ‖y - 0‖ < ρ → ∀ w : Fin 1 → ℝ,
    |w ⬝ᵥ (gLine p *ᵥ w) - w ⬝ᵥ (gLine y *ᵥ w)| ≤ L * ‖p - y‖ * ‖w‖ ^ 2 :=
  isCoordMetric_gLine.exists_quad_lipschitz (mem_univ 0)

end Lightlike.ChartBaseDeltaTests
