import Mathlib
import Lightlike.Geometry.HeatKernel.ChartParametrix
import Lightlike.Geometry.HeatKernel.ChartDelta
import Lightlike.Geometry.HeatKernel.WorldFunctionTaylor

/-!
# The delta property of the parametrix in a chart

Helpers, then `chart_delta_of_structure`: for the cut-off parametrix of `exists_chart_parametrix`, with its structure
(cutoff `θ`, world function `σ = g_p(V, V)`, coefficients `u_k`), the integral `∫ H(t, p, y) F(y) dy` tends to
`F(p)/√det g(p)` as `t → 0⁺`, uniformly for `p` near `x`, for every bounded uniformly continuous `F`. With
`F = f · √det g` (the chart density of the volume measure) the limit is `f(p)`.
-/

open Set Filter Metric MeasureTheory Real Matrix
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- **A quadratic lower bound on a ball extends to all vectors** by homogeneity. -/
theorem quad_lower_of_ball {G : Matrix (Fin n) (Fin n) ℝ} {l ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ w : Fin n → ℝ, ‖w‖ ≤ ρ → l * ‖w‖ ^ 2 ≤ w ⬝ᵥ (G *ᵥ w)) (w : Fin n → ℝ) :
    l * ‖w‖ ^ 2 ≤ w ⬝ᵥ (G *ᵥ w) := by
  by_cases hw : w = 0
  · simp [hw]
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  set s := ρ / ‖w‖ with hs
  have hs0 : 0 < s := by positivity
  have h1 := h (s • w) (by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0, hs, div_mul_cancel₀ _ hwn.ne'])
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, smul_eq_mul] at h1
  have hss : 0 < s * s := by positivity
  nlinarith

end Lightlike
