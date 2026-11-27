import Mathlib
import Lightlike.Geometry.HeatKernel.FrozenGaussian

/-!
# Tests: the frozen Gaussian as an approximate identity

Non-vacuity of `frozenGaussian_approx` for the identity form (`G = 1`, `λ₀ = 1`: `‖z‖² ≤ z·z` for the sup norm,
`norm_sq_le_sum_sq`) and `F ≡ 1`: the heat Gaussian integrates to within any `ε` of `1/√det 1 = 1` for small `t`, as
`integral_frozenGauss` says exactly. Trust check of `mul_exp_neg_le` at `u = 2`: `2e^{-2} ≤ 2e^{-1}`.
-/

open MeasureTheory Real Matrix Set
noncomputable section
namespace Lightlike.FrozenGaussianTests

/-- The identity form has the lower bound `‖z‖² ≤ z·z`. -/
theorem one_lower (n : ℕ) (z : Fin n → ℝ) : 1 * ‖z‖ ^ 2 ≤ z ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ z) := by
  rw [one_mul, Matrix.one_mulVec]
  have := norm_sq_le_sum_sq z
  simpa [dotProduct, sq] using this

/-- Non-vacuity: the hypotheses hold for `G = 1` and `F ≡ 1`. -/
example (n : ℕ) (ε : ℝ) (hε : 0 < ε) : ∃ t₀ > 0, ∀ t ∈ Ioo (0 : ℝ) t₀, ∀ p ∈ (univ : Set (Fin n → ℝ)),
    |(∫ y : Fin n → ℝ, (4 * π * t) ^ (-(n : ℝ) / 2) *
        Real.exp (-((y - p) ⬝ᵥ ((fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) p *ᵥ (y - p))) / (4 * t)) *
          (fun _ => (1 : ℝ)) y) - (fun _ => (1 : ℝ)) p / √((fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) p).det| ≤ ε :=
  frozenGaussian_approx (fun _ _ => PosDef.one) one_pos (fun _ _ z => one_lower n z) (B := 1)
    (fun _ => by simp) uniformContinuous_const ε hε

/-- `u e^{-u} ≤ 2 e^{-u/2}` at `u = 2`. -/
example : 2 * Real.exp (-2) ≤ 2 * Real.exp (-2 / 2) := mul_exp_neg_le 2 (by norm_num)

end Lightlike.FrozenGaussianTests
