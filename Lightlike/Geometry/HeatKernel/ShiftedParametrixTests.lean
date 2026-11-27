import Mathlib
import Lightlike.Geometry.HeatKernel.ShiftedParametrix
import Lightlike.Geometry.HeatKernel.ChartParametrixTests

/-!
# Tests: the chart parametrix after the substitution `p = w − s v`

Non-vacuity of `Lightlike.IsChartParametrix.exists_shifted` for the flat metric of the line at every order: the
shifted parametrix exists, agrees with `s H(s², w − s v, w)` at the centre and has the Gaussian derivative bound
there. Trust check of `norm_iteratedFDeriv_exp_comp_le` at order `0`.
-/

open Set Real Nat
open scoped ContDiff
noncomputable section
namespace Lightlike.ShiftedParametrixTests

open Lightlike.LaplaceBeltramiTests Lightlike.ChartParametrixTests

example (x : ℝ) : ‖iteratedFDeriv ℝ 0 (fun y : ℝ => Real.exp (y ^ 2)) x‖ ≤ 0 ! * Real.exp (x ^ 2) * 1 ^ 0 :=
  norm_iteratedFDeriv_exp_comp_le (f := fun y : ℝ => y ^ 2) (by fun_prop) x 0 le_rfl fun i hi1 hi0 => by omega

example (N ℓ : ℕ) : ∃ (H : ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ) (Gx : ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ) (c C : ℝ),
    0 < c ∧ 1 ^ 1 * H (1 ^ 2) (0 - (1 : ℝ) • 0) 0 = Gx 1 0 0 ∧
      ‖iteratedFDeriv ℝ ℓ (fun w' => Gx 1 w' 0) 0‖ ≤ C * (1 + ‖(0 : Fin 1 → ℝ)‖ ^ 2) ^ ℓ *
        Real.exp (-(c * ‖(0 : Fin 1 → ℝ)‖ ^ 2)) := by
  obtain ⟨r, u, H, Ω, θ, σ, V, h⟩ := exists_isChartParametrix isRiemMetric_gLine (mem_univ 0) N
  obtain ⟨ρ, hρ, -, Gx, -, -, hag, c, hc, hb⟩ := h.exists_shifted isCoordMetric_gLine
  obtain ⟨C, -, hC⟩ := hb ℓ
  have h0 : ‖(0 : Fin 1 → ℝ) - (1 : ℝ) • 0 - 0‖ ≤ ρ := by simpa using hρ.le
  exact ⟨H, Gx, c, C, hc, hag 1 ⟨one_pos, le_rfl⟩ 0 0 h0, hC 1 ⟨one_pos, le_rfl⟩ 0 0 h0⟩

end Lightlike.ShiftedParametrixTests
