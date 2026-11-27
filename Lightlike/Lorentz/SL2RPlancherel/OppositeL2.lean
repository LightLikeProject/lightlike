import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.OppositeIdent

/-!
# The principal-series transform of an opposite-sign test function is square integrable

For `χ` smooth with compact support in `(0, ∞)`, the transform `T χ` of the opposite-sign block
`(l, -s)` (`oppTrans`) is continuous (`continuous_oppTrans`) and lies in `L²(0, ∞)`
(`memLp_oppTrans`): by `norm_oppTrans` and the decay of the pairing (`norm_pairing_le_div`),
`|T χ (ρ)|² ≤ ρ W² / (4ρ² + 1)² ≤ W² / (1 + ρ²)` with `W = 4 C ∫ |L χ| sinh`.
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (opposite-sign blocks), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

lemma continuous_oppConst (s l : ℕ) : Continuous fun ρ : ℝ => oppConst s l (2 * ρ) := by
  unfold oppConst wP
  refine (continuous_finsetProd _ fun j _ => ?_).mul
    (continuous_const.mul (continuous_finsetProd _ fun j _ => ?_)) <;>
  exact Complex.continuous_conj.comp (by fun_prop)

/-- The transform of a test function is continuous. -/
theorem continuous_oppTrans (s l : ℕ) {χ : ℝ → ℂ} (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    Continuous (oppTrans s l χ) := by
  unfold oppTrans
  refine ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp ?_)).div
    (continuous_oppConst s l) fun ρ => oppConst_ne_zero s l ρ).mul
    ((continuous_oppPairing s l hχ hc).comp (continuous_const.mul continuous_id))
  exact ((continuous_id.mul continuous_tanh_pi_mul).mul
    (continuous_wl l)).mul (continuous_wl s)

/-- **The transform of an opposite-sign test function is in `L²(0, ∞)`.** -/
theorem memLp_oppTrans (s l : ℕ) {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hsub : tsupport χ ⊆ Ioi 0) :
    MemLp (oppTrans s l χ) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hcont := continuous_oppTrans s l hχ.continuous hc
  set W := 4 * pairingWeight (radialCasimir l (-(s : ℝ)) χ) with hW
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (W ^ 2)).restrict)
    (hcont.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
  have hρ0 : (0 : ℝ) < ρ := hρ
  have ht0 : 0 ≤ Real.tanh (Real.pi * ρ) := tanh_nonneg_of_nonneg (by positivity)
  have ht1 : Real.tanh (Real.pi * ρ) ≤ 1 := (Real.tanh_lt_one _).le
  have hP := norm_pairing_le_div s l (2 * ρ) hχ hc hsub
  rw [← hW] at hP
  set A := ‖oppPairing s l χ (2 * ρ)‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  set d := (2 * ρ) ^ 2 + 1 with hd
  have hd0 : 0 < d := by positivity
  have hAd : A * d ≤ W := (le_div_iff₀ hd0).1 hP
  have hA2 : A ^ 2 * d ^ 2 ≤ W ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (mul_nonneg hA0 hd0.le) hAd 2
  have hrd : ρ * (1 + ρ ^ 2) ≤ d ^ 2 := by
    rw [hd]; nlinarith [sq_nonneg (ρ - 1 / 2), sq_nonneg (ρ ^ 2 - ρ / 2), sq_nonneg ρ, hρ0.le]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_oppTrans s l χ hρ0.le, mul_pow,
    Real.sq_sqrt (mul_nonneg hρ0.le ht0), ← hA, le_mul_inv_iff₀ (by positivity)]
  calc ρ * Real.tanh (Real.pi * ρ) * A ^ 2 * (1 + ρ ^ 2) ≤ ρ * 1 * A ^ 2 * (1 + ρ ^ 2) := by
        gcongr
    _ = A ^ 2 * (ρ * (1 + ρ ^ 2)) := by ring
    _ ≤ A ^ 2 * d ^ 2 := by gcongr
    _ ≤ W ^ 2 := hA2

end Lightlike.Lorentz.SL2RPlancherel
