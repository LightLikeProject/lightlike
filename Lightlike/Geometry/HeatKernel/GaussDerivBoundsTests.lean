import Mathlib
import Lightlike.Geometry.HeatKernel.GaussDerivBounds

/-!
# Tests: derivative bounds for the Gaussian factor

`norm_iteratedFDerivWithin_exp_univ` at order `0`; `inv_pow_mul_exp_neg_le` at `δ = s = 4`, `t = 1`, `m = 1`
(`e^{-1} ≤ 1`); non-vacuity of `norm_iteratedFDerivWithin_gauss_le` and `norm_iteratedFDerivWithin_mul_gauss_le` for
`σ(q) = q²` on the line, at every order.
-/

open Set Real Nat
open scoped ContDiff
noncomputable section
namespace Lightlike.GaussDerivBoundsTests

example (x : ℝ) : ‖iteratedFDerivWithin ℝ 0 Real.exp univ x‖ = Real.exp x := norm_iteratedFDerivWithin_exp_univ 0 x

example : (1 : ℝ)⁻¹ ^ 1 * Real.exp (-4 / (4 * 1)) ≤ (1 ! : ℝ) * (4 / 4) ^ 1 :=
  inv_pow_mul_exp_neg_le (by norm_num) le_rfl one_pos 1

/-- At order `ℓ`, the derivatives of `e^{-q²/4t}` on `[-1, 1]` are `O(t^{-ℓ}) e^{-q²/4t}`. -/
example (ℓ : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) 1, ∀ q ∈ Icc (-1 : ℝ) 1,
    ‖iteratedFDerivWithin ℝ ℓ (fun q : ℝ => Real.exp (-(q ^ 2) / (4 * t))) univ q‖ ≤
      C * t⁻¹ ^ ℓ * Real.exp (-(q ^ 2) / (4 * t)) :=
  norm_iteratedFDerivWithin_gauss_le uniqueDiffOn_univ (σ := fun q : ℝ => q ^ 2) (by fun_prop)
    isCompact_Icc (subset_univ _) ℓ

/-- The same with the smooth factor `a(q) = q`. -/
example (ℓ : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) 1, ∀ q ∈ Icc (-1 : ℝ) 1,
    ‖iteratedFDerivWithin ℝ ℓ (fun q : ℝ => q * Real.exp (-(q ^ 2) / (4 * t))) univ q‖ ≤
      C * t⁻¹ ^ ℓ * Real.exp (-(q ^ 2) / (4 * t)) :=
  norm_iteratedFDerivWithin_mul_gauss_le uniqueDiffOn_univ (a := fun q : ℝ => q) (σ := fun q : ℝ => q ^ 2)
    (by fun_prop) (by fun_prop) isCompact_Icc (subset_univ _) ℓ

end Lightlike.GaussDerivBoundsTests
