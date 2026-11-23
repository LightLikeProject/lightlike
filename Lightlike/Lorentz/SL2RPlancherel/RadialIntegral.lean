module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.ArcsinIntegral
public import Lightlike.Lorentz.SL2RPlancherel.CoshSubstitution
public import Lightlike.Lorentz.SL2RPlancherel.UpperHalfPlaneSubstitution

/-!
# Step (iv) of the radial integral formula on the hyperbolic plane

For measurable `Φ : ℝ → [0,∞]`,
`∫_u ∫_s Φ(√(1+u²) cosh s) ds du = 2π ∫_{t>1} Φ(t) dt`,
by the substitution `t = c cosh s` (`lintegral_comp_cosh`), Tonelli, and the arcsine integral
(`lintegral_inv_sqrt_sub_sq`).  Together with `lintegral_radial_step` this gives
`∫_{y>0} ∫_x Φ((x²+y²+1)/(2y)) dx dy/y² = 2π ∫_{t>1} Φ(t) dt`.  Milestone HA3.
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- **Step (iv)**: for measurable `Φ : ℝ → [0,∞]`,
`∫_u ∫_s Φ(√(1+u²) cosh s) = 2π ∫_{t>1} Φ(t) dt`. -/
lemma lintegral_radial_cosh {Φ : ℝ → ENNReal} (hΦ : Measurable Φ) :
    ∫⁻ u : ℝ, ∫⁻ s : ℝ, Φ (√(1 + u ^ 2) * Real.cosh s) =
      2 * ENNReal.ofReal π * ∫⁻ t in Ioi (1 : ℝ), Φ t := by
  set G : ℝ → ℝ → ENNReal := fun u t =>
    if √(1 + u ^ 2) < t then Φ t * ENNReal.ofReal (1 / √(t ^ 2 - (1 + u ^ 2))) else 0
    with hG
  have hGm : Measurable (Function.uncurry G) := by
    have h1 : Measurable fun p : ℝ × ℝ =>
        Φ p.2 * ENNReal.ofReal (1 / √(p.2 ^ 2 - (1 + p.1 ^ 2))) := by
      fun_prop
    exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) h1 measurable_const
  -- inner step
  have h1 : ∀ u : ℝ, ∫⁻ s : ℝ, Φ (√(1 + u ^ 2) * Real.cosh s) = 2 * ∫⁻ t, G u t := by
    intro u
    have hc : 0 < √(1 + u ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hc2 : √(1 + u ^ 2) ^ 2 = 1 + u ^ 2 := Real.sq_sqrt (by positivity)
    rw [lintegral_comp_cosh hc, ← lintegral_indicator measurableSet_Ioi]
    congr 1
    refine lintegral_congr (fun t => ?_)
    simp only [indicator, mem_Ioi, hG, hc2]
  simp_rw [h1]
  have hm : Measurable fun u => ∫⁻ t, G u t := hGm.lintegral_prod_right'
  rw [lintegral_const_mul _ hm]
  rw [lintegral_lintegral_swap hGm.aemeasurable]
  -- fixed t
  have h2 : ∀ t : ℝ, ∫⁻ u, G u t = (Ioi (1 : ℝ)).indicator (fun t => Φ t * ENNReal.ofReal π) t := by
    intro t
    by_cases ht : 1 < t
    · have hR : 0 < √(t ^ 2 - 1) := Real.sqrt_pos.2 (by nlinarith)
      have hR2 : √(t ^ 2 - 1) ^ 2 = t ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
      have hset : ∀ u : ℝ, √(1 + u ^ 2) < t ↔ u ∈ Ioo (-√(t ^ 2 - 1)) (√(t ^ 2 - 1)) := by
        intro u
        rw [Real.sqrt_lt' (by linarith), mem_Ioo, ← abs_lt, ← sq_lt_sq₀ (abs_nonneg u) hR.le,
          sq_abs, hR2]
        constructor <;> intro h <;> linarith
      have : (fun u => G u t) = (Ioo (-√(t ^ 2 - 1)) (√(t ^ 2 - 1))).indicator
          (fun u => Φ t * ENNReal.ofReal (1 / √(√(t ^ 2 - 1) ^ 2 - u ^ 2))) := by
        ext u
        simp only [hG, indicator, hset, hR2]
        rw [show t ^ 2 - (1 + u ^ 2) = t ^ 2 - 1 - u ^ 2 by ring]
      rw [this, lintegral_indicator measurableSet_Ioo, lintegral_const_mul _ (by fun_prop),
        lintegral_inv_sqrt_sub_sq hR]
      simp [indicator, ht]
    · have : (fun u => G u t) = fun _ => 0 := by
        ext u
        have : 1 ≤ √(1 + u ^ 2) := by
          rw [Real.one_le_sqrt]; nlinarith [sq_nonneg u]
        simp only [hG]
        exact ite_eq_right_iff.2 (fun h => absurd h (by linarith))
      simp [this, indicator, ht]
  simp_rw [h2]
  rw [lintegral_indicator measurableSet_Ioi, lintegral_mul_const _ hΦ]
  ring

end Lightlike.Lorentz.SL2R
