import Lightlike.FieldTheory.Gaussian.Integral

/-!
# The multivariate Gaussian measure is a measure with density

For a positive definite `S` the centred Gaussian measure `multivariateGaussian 0 S` of Mathlib equals
Lebesgue measure with density `gaussDensity S x = (√(2π))⁻ⁿ (det S)^{-1/2} exp (-(1/2) xᵀ S⁻¹ x)`
(`multivariateGaussian_eq_withDensity`), and a function integrable for the Gaussian measure becomes
integrable against the unnormalised density (`integrable_mul_exp_of_integrable`).
-/

open MeasureTheory ProbabilityTheory Matrix Real
open scoped MatrixOrder

noncomputable section

namespace Lightlike.FieldTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unnormalised Gaussian weight `exp (-(1/2) xᵀ A x)`. -/
def weight (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x))

/-- The normalisation constant `(√(2π))⁻ⁿ (det S)^{-1/2}`. -/
def normConst (S : Matrix ι ι ℝ) : ℝ :=
  ((Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card ι / Real.sqrt S.det

omit [DecidableEq ι] in
lemma measurable_weight (A : Matrix ι ι ℝ) : Measurable (weight A) := by
  unfold weight; fun_prop

omit [DecidableEq ι] in
lemma weight_nonneg (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : 0 ≤ weight A x :=
  (Real.exp_pos _).le

lemma normConst_pos {S : Matrix ι ι ℝ} (hS : S.PosDef) : 0 < normConst S := by
  unfold normConst
  have := hS.det_pos
  positivity

lemma integral_weight {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    normConst S * ∫ x, weight S⁻¹ x = 1 := by
  have h := integral_multivariateGaussian S hS (fun _ => 1)
  simp only [mul_one, integral_const, probReal_univ, one_smul] at h
  exact h.symm

lemma integrable_weight {S : Matrix ι ι ℝ} (hS : S.PosDef) : Integrable (weight S⁻¹) := by
  by_contra h
  have := integral_weight hS
  rw [integral_undef h, mul_zero] at this
  exact zero_ne_one this

/-- **The centred Gaussian measure is Lebesgue measure with the Gaussian density.** -/
theorem multivariateGaussian_eq_withDensity {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    multivariateGaussian 0 S =
      (volume : Measure (EuclideanSpace ℝ ι)).withDensity
        (fun x => ENNReal.ofReal (normConst S * weight S⁻¹ x)) := by
  have hint := (integrable_weight hS).const_mul (normConst S)
  have : IsProbabilityMeasure ((volume : Measure (EuclideanSpace ℝ ι)).withDensity
        (fun x => ENNReal.ofReal (normConst S * weight S⁻¹ x))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun x => mul_nonneg (normConst_pos hS).le (weight_nonneg _ x)),
      integral_const_mul, integral_weight hS, ENNReal.ofReal_one]
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_withDensity_eq_integral_toReal_smul (by
      exact ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_weight _)))
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_multivariateGaussian S hS]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg (normConst_pos hS).le (weight_nonneg _ _)), smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [weight, normConst]
  ring

/-- A function integrable for the Gaussian measure is integrable against the Gaussian weight. -/
theorem integrable_weight_mul {S : Matrix ι ι ℝ} (hS : S.PosDef) {g : EuclideanSpace ℝ ι → ℝ}
    (hg : Integrable g (multivariateGaussian 0 S)) : Integrable (fun x => weight S⁻¹ x * g x) := by
  rw [multivariateGaussian_eq_withDensity hS,
    integrable_withDensity_iff_integrable_smul' (by
      exact ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_weight _)))
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hg
  have h := hg.const_mul (normConst S)⁻¹
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (mul_nonneg (normConst_pos hS).le (weight_nonneg _ _)), smul_eq_mul]
  have := (normConst_pos hS).ne'
  field_simp

end Lightlike.FieldTheory
