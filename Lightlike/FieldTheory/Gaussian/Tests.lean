import Lightlike.FieldTheory.Gaussian.Moments

/-!
# Checks of the Gaussian integral

* Against Mathlib's independent computation `GaussianFourier.integral_rexp_neg_mul_sq_norm`: for
  `A = 1` the formula gives `(2π)^{n/2}`.
* Isserlis for two points against Mathlib's covariance of the multivariate Gaussian
  (`covariance_eval_multivariateGaussian`), an independent computation; the four-point function with
  one variable and variance `1` is `3`, not `1`.
* The determinant matters: for one variable the integrals for `A = 1` and `A = 2` differ.
-/

open MeasureTheory ProbabilityTheory Matrix Real

namespace Lightlike.FieldTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Known value: for `A = 1` the integral is `(2π)^{n/2}` (Mathlib's Gaussian integral). -/
example : ∫ x : EuclideanSpace ℝ ι, Real.exp (-(1 / 2) * (x ⬝ᵥ (1 : Matrix ι ι ℝ) *ᵥ x)) =
    (2 * Real.pi) ^ ((Fintype.card ι : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ ι)
    (b := 1 / 2) (by norm_num)
  have e : ∀ x : EuclideanSpace ℝ ι, x.ofLp ⬝ᵥ (1 : Matrix ι ι ℝ) *ᵥ x.ofLp = ‖x‖ ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, sq]
  simp_rw [e]
  rw [h, finrank_euclideanSpace, show Real.pi / (1 / 2) = 2 * Real.pi by ring]

/-- The determinant matters: the integrals for `A = 1` and `A = 2` over one variable differ. -/
example : ∫ x : EuclideanSpace ℝ Unit,
      Real.exp (-(1 / 2) * (x ⬝ᵥ ((2 : ℝ) • (1 : Matrix Unit Unit ℝ)) *ᵥ x)) ≠
    ∫ x : EuclideanSpace ℝ Unit, Real.exp (-(1 / 2) * (x ⬝ᵥ (1 : Matrix Unit Unit ℝ) *ᵥ x)) := by
  have h2 : ((2 : ℝ) • (1 : Matrix Unit Unit ℝ)).PosDef :=
    (Matrix.PosDef.one (n := Unit) (R := ℝ)).smul (show (0 : ℝ) < 2 by norm_num)
  have h1 : (1 : Matrix Unit Unit ℝ).PosDef := Matrix.PosDef.one
  rw [integral_exp_neg_half_quad _ h2, integral_exp_neg_half_quad _ h1]
  simp only [Matrix.det_smul, Matrix.det_one, Fintype.card_unit, pow_one, mul_one]
  intro h
  have hp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  rw [Real.sqrt_one, div_one] at h
  have : Real.sqrt 2 = 1 := by
    field_simp at h
    exact h.symm
  have h22 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- The Isserlis two-point function agrees with Mathlib's covariance. -/
example {S : Matrix ι ι ℝ} (hS : S.PosDef) (i j : ι) :
    moment S [i, j] = cov[fun x : EuclideanSpace ℝ ι => x i, fun x => x j; multivariateGaussian 0 S] := by
  rw [moment_two hS, covariance_eval_multivariateGaussian hS.posSemidef]

/-- The four-point function for one variable of variance `1` is `3`. -/
example : moment (1 : Matrix Unit Unit ℝ) [(), (), (), ()] = 3 := by
  rw [moment_four Matrix.PosDef.one]
  norm_num

end Lightlike.FieldTheory
