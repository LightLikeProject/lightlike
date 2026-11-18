# Field theory in finite dimensions

## Abstract (Alpha)

This API treats Gaussian integrals on `ℝⁿ`, the starting point of zero-dimensional field theory. It proves that the standard Gaussian measure is Lebesgue measure with the standard density, that the centred multivariate Gaussian measure with covariance `S` has the density `exp(-(1/2) xᵀ S⁻¹ x)` with its normalisation, and the Gaussian integral `∫ exp(-(1/2) xᵀ A x) dx = (√(2π))ⁿ / √(det A)` for positive definite `A`. Moments, Wick's theorem as a sum over pairings and Feynman graphs are open.

## Content (Alpha)

Mathlib defines the multivariate Gaussian measure by its covariance, as the image of the standard Gaussian measure under the matrix square root of the covariance {1}. Mathlib has no density for it and no moment theorem. Here the standard Gaussian measure on `ℝⁿ` is shown to be the product of the one-dimensional densities with respect to Lebesgue measure [1] {1}. A change of variables by an invertible matrix gives the factor `|det R|⁻¹` [2]. With the square root `R` of `S` one has `R S⁻¹ R = 1`, hence `(R y)ᵀ S⁻¹ (R y) = yᵀ y`, and the centred Gaussian measure with covariance `S` integrates a function `f` as `(√(2π))⁻ⁿ (det S)^{-1/2} ∫ exp(-(1/2) xᵀ S⁻¹ x) f(x) dx` [2] {1}. Taking `f = 1` and `S = A⁻¹` gives the Gaussian integral of a positive definite `A` [2]. Checks: for `A = 1` the value is `(2π)^{n/2}`, which agrees with Mathlib's separate computation of `∫ exp(-b ‖x‖²)`, and the integrals for `A = 1` and `A = 2` in one variable differ, so the determinant is needed.

**Missing.** Moments of the Gaussian measure and Wick's theorem as a sum over pairings, the zero-dimensional field theory as a formal power series and Feynman graphs with their symmetry factors are open [TODO]. The comparison of the statements with a source is pending: no source other than Mathlib was opened at a cited location.

## Lean References

1. Lightlike/FieldTheory/Gaussian/Density.lean - `FieldTheory.pi_gaussianReal_eq_withDensity`, `FieldTheory.integral_stdGaussian`
2. Lightlike/FieldTheory/Gaussian/Integral.lean - `FieldTheory.integral_comp_toEuclideanLin`, `FieldTheory.integral_multivariateGaussian`, `FieldTheory.integral_exp_neg_half_quad`

## References

1. Mathlib, `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean` (`multivariateGaussian`, `stdGaussian`).
