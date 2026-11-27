import Mathlib
import Lightlike.Geometry.HeatKernel.ChartDelta

/-!
# Tests: the pointwise comparison with the frozen Gaussian

`abs_exp_sub_exp_le` at `x = 0`, `y = 1`: `e − 1 ≤ e · 1`. Non-vacuity of `cutoffGauss_sub_frozen_le` when the
parametrix is the frozen Gaussian itself (`θ = 1`, `σ = q`, `U = 1` at `z = 0`): the left side is `0`.
-/

open Real
noncomputable section
namespace Lightlike.ChartDeltaTests

example : |Real.exp 0 - Real.exp 1| ≤ Real.exp (max 0 1) * |0 - 1| := abs_exp_sub_exp_le 0 1

/-- At `z = 0` with `θ = 1`, `σ = q = 0`, `U = 1` the hypotheses hold and the bound applies. -/
example {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |1 * Real.exp (-0 / (4 * t)) * 1 - Real.exp (-0 / (4 * t))| ≤
      ((1 + 1 * (1 + 1)) * 1 * 2 * √(4 / 1) ^ 3 + 1 * (√(4 / 1) + 1) + 64 / (1 ^ 2 * 1)) * √t *
        Real.exp (-(1 * ‖(0 : Fin 2 → ℝ)‖ ^ 2 / (4 * t)) / 2) :=
  cutoffGauss_sub_frozen_le (n := 2) (z := 0) ht ht1 one_pos one_pos zero_le_one zero_le_one (by simp)
    (fun _ => rfl) (fun h => by simp at h; linarith) (fun _ => by simp) (by simp)
    (fun _ => by simp) (fun _ => by simp; positivity)

end Lightlike.ChartDeltaTests
