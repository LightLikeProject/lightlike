import Mathlib
import Lightlike.Geometry.HeatKernel.ChartParametrixDelta
import Lightlike.Geometry.HeatKernel.ChartParametrixTests

/-!
# Tests: the delta property of the chart parametrix

Non-vacuity of `Lightlike.exists_chart_parametrix_delta` for the flat metric of the line at the centre: with `F = 1`
the total mass `∫ H(t, 0, y) dy` tends to `1/√det 1 = 1`. Trust checks of the helpers: `quad_lower_of_ball` for the
identity matrix, `exp_neg_le_of_far` at a point, `cutoffGauss_sub_frozen_le₂` at `z = 0` with the frozen Gaussian
itself.
-/

open Set Real Matrix
noncomputable section
namespace Lightlike.ChartParametrixDeltaTests

open Lightlike.LaplaceBeltramiTests Lightlike.ChartParametrixTests

/-- Non-vacuity: on the line the parametrix has total mass tending to `1`, uniformly near `0`, at every order. -/
example (N : ℕ) : ∃ H : ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ, ∀ ε > 0, ∃ t₀ > 0, ∀ t ∈ Ioo (0 : ℝ) t₀,
    |(∫ y, H t 0 y * 1) - 1| ≤ ε := by
  obtain ⟨r, u, H, hr, -, -, -, -, -, r', hr', -, hδ⟩ :=
    exists_chart_parametrix_delta isRiemMetric_gLine (mem_univ 0) N
  refine ⟨H, fun ε hε => ?_⟩
  obtain ⟨t₀, ht₀, h⟩ := hδ (fun _ => 1) 1 (fun _ => by simp) uniformContinuous_const ε hε
  refine ⟨t₀, ht₀, fun t ht => ?_⟩
  have := h t ht 0 (by simpa using hr')
  simpa [gLine] using this

/-- The identity matrix satisfies the lower bound on every ball, hence everywhere. -/
example (w : Fin 2 → ℝ) : (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ w ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ w) :=
  quad_lower_of_ball one_pos (fun v _ => by
    rw [Matrix.one_mulVec]
    have h1 := Lightlike.norm_sq_le_sum_sq v
    simp only [dotProduct]
    nlinarith [sq_nonneg ‖v‖, Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg (v i),
      show ∑ i, v i * v i = ∑ i, v i ^ 2 from Finset.sum_congr rfl fun i _ => by ring]) w

/-- At distance `1` the far bound holds with `c = 1`, `r' = 1`, `t = 1`. -/
example : Real.exp (-(1 * ‖(fun _ => 1 : Fin 1 → ℝ)‖ ^ 2 / (4 * 1))) ≤
    32 / (1 ^ 2 * 1) * √1 * Real.exp (-(1 * ‖(fun _ => 1 : Fin 1 → ℝ)‖ ^ 2 / (4 * 1)) / 2) :=
  exp_neg_le_of_far one_pos le_rfl one_pos one_pos (by simp)

/-- At `z = 0` with `θ = 1`, `σ = q = 0`, `U = 1` the two-radius bound applies. -/
example {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |1 * Real.exp (-0 / (4 * t)) * 1 - Real.exp (-0 / (4 * t))| ≤
      (((1 + 1 * (1 + 1)) * 1 * 2 * √(4 / 1) ^ 3 + 1 * (√(4 / 1) + 1) + 64 / (1 ^ 2 * 1)) +
        (1 + 1) * (32 / (1 ^ 2 * 1))) * √t * Real.exp (-(1 * ‖(0 : Fin 2 → ℝ)‖ ^ 2 / (4 * t)) / 2) :=
  cutoffGauss_sub_frozen_le₂ (n := 2) (z := 0) (r := 2) ht ht1 one_pos one_pos (by norm_num) zero_le_one
    zero_le_one zero_le_one ⟨zero_le_one, le_rfl⟩ (fun _ => rfl) (fun h => by simp at h; linarith)
    (fun _ => by simp) (by simp) (fun _ => by simp) (fun _ => by simp; positivity) (fun _ => by simp)

end Lightlike.ChartParametrixDeltaTests
