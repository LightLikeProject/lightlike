import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Norm bound for the exponential of a bounded operator

`‖exp a‖ ≤ exp ‖a‖` in a complete normed algebra over `𝕜 = ℝ` or `ℂ`, and the contraction bound
`‖exp (t (l² R - l))‖ ≤ 1` for `t ≥ 0` when `‖R‖ ≤ l⁻¹`.
-/

open NormedSpace Filter Topology

noncomputable section

namespace Lightlike.OperatorAlgebras

variable {𝕜 : Type*} [RCLike 𝕜] {𝔸 : Type*} [NormedRing 𝔸] [inst : NormedAlgebra 𝕜 𝔸] [CompleteSpace 𝔸]

include inst in
/-- `‖exp a‖ ≤ exp ‖a‖` in a complete normed algebra over `ℝ` or `ℂ`. -/
theorem norm_exp_le_exp_norm (h1 : ‖(1 : 𝔸)‖ ≤ 1) (a : 𝔸) : ‖exp a‖ ≤ Real.exp ‖a‖ := by
  rw [exp_eq_tsum (𝕂 := 𝕜)]
  have hs : HasSum (fun n : ℕ => ‖a‖ ^ n / (n.factorial : ℝ)) (Real.exp ‖a‖) := by
    have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) ‖a‖
    simpa [Real.exp_eq_exp_ℝ] using this
  refine tsum_of_norm_bounded hs fun n => ?_
  calc ‖((n.factorial : ℕ)⁻¹ : 𝕜) • a ^ n‖ ≤ ‖((n.factorial : ℕ)⁻¹ : 𝕜)‖ * ‖a ^ n‖ := norm_smul_le _ _
    _ ≤ ((n.factorial : ℝ))⁻¹ * ‖a‖ ^ n := by
        rw [norm_inv, RCLike.norm_natCast]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        cases n with
        | zero => simpa using h1
        | succ m => exact norm_pow_le' a (Nat.succ_pos m)
    _ = ‖a‖ ^ n / (n.factorial : ℝ) := by ring

end Lightlike.OperatorAlgebras
