import Lightlike.GFT.Borel.Nevanlinna
import Lightlike.FieldTheory.ZeroDim.QuarticComplex

/-!
# The quartic partition function is Borel summable (task T-GF7-P7)

`quarticZ_borel_summable` (Rivasseau–Wang, arXiv:1003.1037, Theorem IV.1 with `k = 2`): the Borel transform of the
Taylor series of `Z(λ) = ∫ e^{-λφ⁴ - φ²/2} dφ` continues to a strip and `Z` is its Laplace transform on every `C_R`.

Proof: `quarticZ_sokalHyp` turns `quarticZ_nevanlinna` into the hypotheses of the Nevanlinna–Sokal theorem with
`ρ = 1/32`; the continuation `B` is taken once, for `R = 1`, and for any `R` the representation of T-GF7-P5 on a line
`Re w = c > max(1, 1/R)` is the one for `B`, because `b₀` is the same function whatever `R` (`B = b₀` on `(0,∞)`).
-/

open MeasureTheory Set Filter Complex Finset
open scoped Topology Real Nat

namespace Lightlike.FieldTheory

open Borel

/-- The quartic partition function satisfies the Nevanlinna–Sokal hypotheses on every `C_R`, with `ρ = 1/32`. -/
theorem quarticZ_sokalHyp {R : ℝ} (hR : 0 < R) :
    SokalHyp quarticZ quarticCoeff R (16 * √(2 * Real.pi)) (1 / 32) := by
  have hK : 0 ≤ 16 * √(2 * Real.pi) := by positivity
  refine ⟨hR, hK, by norm_num, (quarticZ_nevanlinna hR).1, fun q z hz => ?_⟩
  cases q with
  | zero =>
    have h0 := norm_quarticZ_sub_le 0 (re_pos_of_mem_diskC hR hz).le
    simp at h0 ⊢
    nlinarith [mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg Real.pi)]
  | succ N =>
    refine ((quarticZ_nevanlinna hR).2 N z hz).trans ?_
    have hden : 16 * √(2 * Real.pi) * (((N + 1) ! : ℕ) : ℝ) / (1 / 32 : ℝ) ^ (N + 1) =
        16 * √(2 * Real.pi) * (((N + 1) ! : ℕ) : ℝ) * 32 ^ (N + 1) := by
      rw [one_div, inv_pow, div_inv_eq_mul]
    rw [hden]
    have h1 : (N ! : ℝ) ≤ (((N + 1) ! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_le (Nat.le_succ N)
    have h2 : (32 : ℝ) ^ N ≤ 32 ^ (N + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ N)
    have h3 : (1 : ℝ) ≤ (((N + 1) ! : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    have h4 : (1 : ℝ) ≤ (32 : ℝ) ^ (N + 1) := one_le_pow₀ (by norm_num)
    have h5 : (32 : ℝ) ^ N * (N ! : ℝ) ≤ (((N + 1) ! : ℕ) : ℝ) * 32 ^ (N + 1) := by
      calc (32 : ℝ) ^ N * (N ! : ℝ) ≤ 32 ^ (N + 1) * (((N + 1) ! : ℕ) : ℝ) := by gcongr
        _ = _ := by ring
    have hz' : 0 ≤ ‖z‖ ^ (N + 1) := by positivity
    calc 16 * √(2 * Real.pi) * 32 ^ N * (N ! : ℝ) * ‖z‖ ^ (N + 1)
        = 16 * √(2 * Real.pi) * (32 ^ N * (N ! : ℝ)) * ‖z‖ ^ (N + 1) := by ring
      _ ≤ 16 * √(2 * Real.pi) * ((((N + 1) ! : ℕ) : ℝ) * 32 ^ (N + 1)) * ‖z‖ ^ (N + 1) := by gcongr
      _ = _ := by ring

/-- **The quartic partition function is Borel summable** (task T-GF7-P7; Rivasseau–Wang, arXiv:1003.1037,
Theorem IV.1 with `k = 2`): statement copied word for word from `Tasks/GF/T_GF7_P7.lean`. -/
theorem quarticZ_borel_summable :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ B : ℂ → ℂ, AnalyticOnNhd ℂ B (sokalStrip ρ) ∧
      (∀ t : ℂ, ‖t‖ < ρ → HasSum (fun n => quarticCoeff n * t ^ n / (n ! : ℂ)) (B t)) ∧
      ∀ R : ℝ, 0 < R → ∀ z ∈ diskC R, quarticZ z = z⁻¹ * ∫ x in Ioi (0 : ℝ), cexp (-(x / z)) * B x := by
  have h1 := quarticZ_sokalHyp (R := 1) one_pos
  obtain ⟨B, hBan, hBt, hBx, -⟩ := h1.exists_continuation
  refine ⟨1 / 32, by norm_num, B, hBan, fun t ht => ?_, fun R hR z hz => ?_⟩
  · rw [hBt t ht]
    exact h1.hasSum_borelT ht
  · have hRR := quarticZ_sokalHyp hR
    have hc1 : 1 / R < max 1 (1 / R) + 1 := by linarith [le_max_right 1 (1 / R)]
    have hc2 : 1 / (1 : ℝ) < max 1 (1 / R) + 1 := by
      have := le_max_left 1 (1 / R)
      rw [div_one]; linarith
    rw [hRR.eq_laplace_borelZero hc1 hz]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [hBx _ hc2 x hx]

end Lightlike.FieldTheory
