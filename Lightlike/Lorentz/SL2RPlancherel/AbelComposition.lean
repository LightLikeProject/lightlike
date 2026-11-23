module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.ArcsinIntegral

/-!
# The Beta(1/2, 1/2) integral on an interval

`integral_inv_sqrt_mul_sub`: `∫_v^u da / √((a - v)(u - a)) = π`.  It is the identity behind the
composition of two Abel transforms (each of order 1/2 gives the half-order integral, two give
the identity up to `π`), used to invert the Abel transform on the hyperbolic plane, milestone HA3.
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- `∫_{-R}^{R} du / √(R² - u²) = π` as a real integral. -/
lemma integral_inv_sqrt_sub_sq {R : ℝ} (hR : 0 < R) :
    ∫ u in Ioo (-R) R, 1 / √(R ^ 2 - u ^ 2) = π := by
  rw [integral_eq_lintegral_of_nonneg_ae]
  · have := lintegral_inv_sqrt_sub_sq hR
    simp only [this]
    exact ENNReal.toReal_ofReal pi_pos.le
  · exact Filter.Eventually.of_forall (fun u => by positivity)
  · exact Measurable.aestronglyMeasurable (by fun_prop)

/-- **The Beta(1/2, 1/2) integral**: for `v < u`, `∫_{v}^{u} da / √((a - v)(u - a)) = π`. -/
theorem integral_inv_sqrt_mul_sub {v u : ℝ} (h : v < u) :
    ∫ a in Ioo v u, 1 / √((a - v) * (u - a)) = π := by
  have hR : 0 < (u - v) / 2 := by linarith
  have h1 := integral_inv_sqrt_sub_sq hR
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)] at h1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h.le]
  have key := intervalIntegral.integral_comp_add_right
    (fun a => 1 / √((a - v) * (u - a))) (a := -((u - v) / 2)) (b := (u - v) / 2) ((u + v) / 2)
  have e1 : -((u - v) / 2) + (u + v) / 2 = v := by ring
  have e2 : (u - v) / 2 + (u + v) / 2 = u := by ring
  rw [e1, e2] at key
  rw [← key, ← h1]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  have : (x + (u + v) / 2 - v) * (u - (x + (u + v) / 2)) = ((u - v) / 2) ^ 2 - x ^ 2 := by ring
  simp only [this]

end Lightlike.Lorentz.SL2R
