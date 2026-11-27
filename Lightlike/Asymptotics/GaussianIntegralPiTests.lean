import Mathlib
import Lightlike.Asymptotics.GaussianIntegralPi

/-!
# Tests: Gaussian integrals on `ℝⁿ`

For `G = 1` the quadratic-form Gaussian `integral_exp_neg_mul_quadForm` gives `(π/b)^{n/2}`, the value of the
independently proved `integral_exp_neg_mul_sum_sq_sub` (spectral route against product route). With `G = 4` on the
line it gives `√(π/b)/2`; a formula with `det G` in place of `√det G` would give `√(π/b)/4`: caught.
-/

open MeasureTheory Real Matrix
noncomputable section
namespace Lightlike.GaussianIntegralPiTests

/-- The two routes agree for the identity form. -/
example (n : ℕ) {b : ℝ} (hb : 0 < b) (p : Fin n → ℝ) :
    ∫ y : Fin n → ℝ, Real.exp (-b * ((y - p) ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ (y - p)))) =
      ∫ y : Fin n → ℝ, Real.exp (-b * ∑ i, (y i - p i) ^ 2) := by
  rw [integral_exp_neg_mul_quadForm PosDef.one hb p, integral_exp_neg_mul_sum_sq_sub n hb p]
  simp

/-- `√(det 4) = 2` on the line, not `det 4 = 4`. -/
example : √((4 : Matrix (Fin 1) (Fin 1) ℝ).det) = 2 ∧ (4 : Matrix (Fin 1) (Fin 1) ℝ).det ≠ 2 := by
  have h : (4 : Matrix (Fin 1) (Fin 1) ℝ).det = 4 := by
    rw [show (4 : Matrix (Fin 1) (Fin 1) ℝ) = Matrix.diagonal fun _ => 4 by
      ext i j; fin_cases i; fin_cases j; rfl]
    simp [Matrix.det_diagonal]
  rw [h]
  refine ⟨?_, by norm_num⟩
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

end Lightlike.GaussianIntegralPiTests
