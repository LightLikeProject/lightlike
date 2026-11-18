import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Lightlike.FieldTheory.Gaussian.Density

/-!
# The finite-dimensional Gaussian integral

For a positive definite real matrix `A` the integral of `exp (-(1/2) xᵀ A x)` over `ℝⁿ`
(`EuclideanSpace ℝ ι`) is `(2π)^{n/2} / √(det A)` (`integral_exp_neg_half_quad`).
-/

open MeasureTheory ProbabilityTheory Matrix Real
open scoped MatrixOrder

noncomputable section

namespace Lightlike.FieldTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Change of variables by an invertible matrix. -/
lemma integral_comp_toEuclideanLin (R : Matrix ι ι ℝ) (hR : R.det ≠ 0) (f : EuclideanSpace ℝ ι → ℝ) :
    ∫ x, f (Matrix.toEuclideanLin R x) = |R.det|⁻¹ * ∫ x, f x := by
  have hdet : LinearMap.det (Matrix.toEuclideanLin R) = R.det := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hne : LinearMap.det (Matrix.toEuclideanLin R) ≠ 0 := by rw [hdet]; exact hR
  let e : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι := LinearMap.equivOfDetNeZero _ hne
  have hemb : MeasurableEmbedding (Matrix.toEuclideanLin R) :=
    (e.toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
  have h1 := hemb.integral_map (μ := volume) f
  rw [← h1, MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, integral_smul_measure, hdet,
    ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul, abs_inv]

/-- The matrix square root of a positive definite matrix: facts used below. -/
lemma sqrt_facts {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    CFC.sqrt S * CFC.sqrt S = S ∧ (CFC.sqrt S).det = Real.sqrt S.det ∧ (CFC.sqrt S).IsHermitian ∧
      (CFC.sqrt S).det ≠ 0 := by
  have hs : S.PosSemidef := hS.posSemidef
  have h1 := CFC.sqrt_mul_sqrt_self S hs.nonneg
  have h2 : (CFC.sqrt S).det = Real.sqrt S.det := by
    have := hs.det_sqrt
    simpa using this
  refine ⟨h1, h2, (CFC.sqrt_nonneg S).isSelfAdjoint, ?_⟩
  rw [h2]
  exact (Real.sqrt_pos.2 hS.det_pos).ne'

/-- `R S⁻¹ R = 1` for `R = √S`. -/
lemma sqrt_mul_inv_mul_sqrt {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    CFC.sqrt S * (S⁻¹ * CFC.sqrt S) = 1 := by
  obtain ⟨hRR, hdet, hherm, hne⟩ := sqrt_facts hS
  have hu : IsUnit (CFC.sqrt S).det := isUnit_iff_ne_zero.2 hne
  have h1 : S⁻¹ = (CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹ := by
    conv_lhs => rw [← hRR]
    rw [Matrix.mul_inv_rev]
  rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ ((CFC.sqrt S)⁻¹),
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.nonsing_inv_mul _ hu]

/-- The quadratic form is transported to the norm. -/
lemma quad_sqrt {S : Matrix ι ι ℝ} (hS : S.PosDef) (y : ι → ℝ) :
    (CFC.sqrt S *ᵥ y) ⬝ᵥ (S⁻¹ *ᵥ (CFC.sqrt S *ᵥ y)) = y ⬝ᵥ y := by
  obtain ⟨hRR, hdet, hherm, hne⟩ := sqrt_facts hS
  have hT : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hherm.eq
  have h1 : CFC.sqrt S *ᵥ y = y ᵥ* CFC.sqrt S := by rw [← hT, Matrix.mulVec_transpose, hT]
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, h1, Matrix.vecMul_vecMul,
    sqrt_mul_inv_mul_sqrt hS, Matrix.vecMul_one]

lemma measurableEmbedding_toEuclideanLin (R : Matrix ι ι ℝ) (hR : R.det ≠ 0) :
    MeasurableEmbedding (Matrix.toEuclideanLin R) := by
  have hdet : LinearMap.det (Matrix.toEuclideanLin R) = R.det := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hne : LinearMap.det (Matrix.toEuclideanLin R) ≠ 0 := by rw [hdet]; exact hR
  let e : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι := LinearMap.equivOfDetNeZero _ hne
  exact (e.toContinuousLinearEquiv.toHomeomorph).measurableEmbedding

/-- **The centred multivariate Gaussian measure with covariance `S` has the density
`exp (-(1/2) xᵀ S⁻¹ x)` with respect to Lebesgue measure, with the normalisation
`(2π)^{-n/2} (det S)^{-1/2}`.** -/
theorem integral_multivariateGaussian (S : Matrix ι ι ℝ) (hS : S.PosDef) (f : EuclideanSpace ℝ ι → ℝ) :
    ∫ x, f x ∂(multivariateGaussian 0 S) =
      (((Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card ι / Real.sqrt S.det) *
        ∫ x : EuclideanSpace ℝ ι, Real.exp (-(1 / 2) * (x ⬝ᵥ S⁻¹ *ᵥ x)) * f x := by
  obtain ⟨hRR, hdet, hherm, hne⟩ := sqrt_facts hS
  set R := CFC.sqrt S with hR
  have hemb := measurableEmbedding_toEuclideanLin R hne
  have h1 : multivariateGaussian 0 S = Measure.map (Matrix.toEuclideanLin R)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    simp [multivariateGaussian, hR]
    rfl
  rw [h1, hemb.integral_map, integral_stdGaussian]
  have h2 := integral_comp_toEuclideanLin R hne
    (fun x : EuclideanSpace ℝ ι => Real.exp (-(1 / 2) * (x ⬝ᵥ S⁻¹ *ᵥ x)) * f x)
  have h3 : ∀ y : EuclideanSpace ℝ ι, Real.exp (-(1 / 2) * ((Matrix.toEuclideanLin R y) ⬝ᵥ
      S⁻¹ *ᵥ (Matrix.toEuclideanLin R y))) * f (Matrix.toEuclideanLin R y) =
      Real.exp (-(1 / 2) * ‖y‖ ^ 2) * f (Matrix.toEuclideanLin R y) := by
    intro y
    have hy : ‖y‖ ^ 2 = WithLp.ofLp y ⬝ᵥ WithLp.ofLp y := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [dotProduct, sq]
    have hl : WithLp.ofLp (Matrix.toEuclideanLin R y) = R *ᵥ WithLp.ofLp y := rfl
    rw [hy]
    congr 3
    simp only [hl]
    exact quad_sqrt hS (WithLp.ofLp y)
  simp_rw [h3] at h2
  simp_rw [mul_assoc]
  rw [integral_const_mul, h2, hdet, abs_of_pos (Real.sqrt_pos.2 hS.det_pos)]
  ring

/-- **The Gaussian integral.** For a positive definite matrix `A`,
`∫ exp (-(1/2) xᵀ A x) dx = (√(2π))^n / √(det A)`. -/
theorem integral_exp_neg_half_quad (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    ∫ x : EuclideanSpace ℝ ι, Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x)) =
      (Real.sqrt (2 * Real.pi)) ^ Fintype.card ι / Real.sqrt A.det := by
  have hS : (A⁻¹).PosDef := hA.inv
  have h := integral_multivariateGaussian A⁻¹ hS (fun _ => 1)
  rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 hA.det_pos.ne')] at h
  simp only [mul_one, integral_const, probReal_univ, one_smul] at h
  rw [Matrix.det_nonsing_inv] at h
  rw [Ring.inverse_eq_inv', Real.sqrt_inv] at h
  have ha : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hd : 0 < Real.sqrt A.det := Real.sqrt_pos.2 hA.det_pos
  have hca : ((Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card ι * (Real.sqrt (2 * Real.pi)) ^ Fintype.card ι = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ ha.ne', one_pow]
  generalize ((Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card ι = c at hca h
  generalize (∫ (x : EuclideanSpace ℝ ι), Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x))) = I at h ⊢
  rw [div_inv_eq_mul] at h
  rw [eq_div_iff hd.ne']
  calc I * Real.sqrt A.det = (c * (Real.sqrt (2 * Real.pi)) ^ Fintype.card ι) * (I * Real.sqrt A.det) := by
        rw [hca, one_mul]
    _ = (Real.sqrt (2 * Real.pi)) ^ Fintype.card ι * (c * Real.sqrt A.det * I) := by ring
    _ = _ := by rw [← h, mul_one]

end Lightlike.FieldTheory
