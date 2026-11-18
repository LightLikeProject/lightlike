import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exponentially negligible terms

For `a, ε > 0`: `Δ^{3/4} e^{-ε √(a Δ)} → 0` as `Δ → ∞` (`tendsto_rpow_mul_exp_neg_sqrt`), so any term of
the size `e^{(2 - ε) √(a Δ)}` is eventually at most `Δ^{-3/4} e^{2 √(a Δ)}`
(`eventually_le_rpow_neg_mul_exp`).
-/

open Filter Topology Real

noncomputable section

namespace Lightlike.Tauberian

lemma tendsto_rpow_mul_exp_neg_sqrt {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    Tendsto (fun Δ : ℝ => Δ ^ (3 / 4 : ℝ) * Real.exp (-(ε * Real.sqrt (a * Δ)))) atTop (𝓝 0) := by
  -- substitute `u = √Δ`: `Δ^{3/4} = u^{3/2}` and `√(aΔ) = √a u`
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 / 2 : ℝ) (ε * Real.sqrt a)
    (by positivity)
  have h2 := h1.comp Real.tendsto_sqrt_atTop
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Δ hΔ
  simp only [Function.comp]
  have hs : Real.sqrt (a * Δ) = Real.sqrt a * Real.sqrt Δ := Real.sqrt_mul ha.le Δ
  have e1 : Real.sqrt Δ ^ (3 / 2 : ℝ) = Δ ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hΔ.le]; norm_num
  rw [e1, hs]
  congr 2
  ring

/-- **Negligible terms.** If `ε > 0`, then eventually `e^{(2 - ε) √(a Δ)} ≤ Δ^{-3/4} e^{2 √(a Δ)}`. -/
lemma eventually_le_rpow_neg_mul_exp {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ Δ : ℝ in atTop,
      Real.exp ((2 - ε) * Real.sqrt (a * Δ)) ≤ Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Real.sqrt (a * Δ)) := by
  have h := (tendsto_rpow_mul_exp_neg_sqrt ha hε).eventually (gt_mem_nhds (zero_lt_one))
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with Δ hΔ hΔ0
  have hpos : 0 < Δ ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hΔ0 _
  have e1 : Δ ^ (-(3 / 4 : ℝ)) = (Δ ^ (3 / 4 : ℝ))⁻¹ := Real.rpow_neg hΔ0.le _
  rw [e1]
  have e2 : Real.exp (2 * Real.sqrt (a * Δ)) =
      Real.exp ((2 - ε) * Real.sqrt (a * Δ)) * Real.exp (ε * Real.sqrt (a * Δ)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e2]
  have hE : 0 < Real.exp (ε * Real.sqrt (a * Δ)) := Real.exp_pos _
  have hX : 0 < Real.exp ((2 - ε) * Real.sqrt (a * Δ)) := Real.exp_pos _
  have h3 : Δ ^ (3 / 4 : ℝ) * Real.exp (-(ε * Real.sqrt (a * Δ))) < 1 := hΔ
  rw [Real.exp_neg] at h3
  -- `Δ^{3/4} < e^{ε√}` hence `1 ≤ (Δ^{3/4})⁻¹ e^{ε√}`
  have h4 : Δ ^ (3 / 4 : ℝ) < Real.exp (ε * Real.sqrt (a * Δ)) := by
    have := (mul_inv_lt_iff₀ hE).1 h3
    linarith [this]
  calc Real.exp ((2 - ε) * Real.sqrt (a * Δ)) = (Δ ^ (3 / 4 : ℝ))⁻¹ * Δ ^ (3 / 4 : ℝ) *
        Real.exp ((2 - ε) * Real.sqrt (a * Δ)) := by field_simp
    _ ≤ (Δ ^ (3 / 4 : ℝ))⁻¹ * (Real.exp (ε * Real.sqrt (a * Δ)) *
        Real.exp ((2 - ε) * Real.sqrt (a * Δ))) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith [h4.le, hX]
    _ = _ := by ring

end Lightlike.Tauberian
