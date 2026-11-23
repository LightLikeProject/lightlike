import Mathlib
import Lightlike.Lorentz.SL2RCasimir
import Lightlike.Lorentz.SL2RPlancherel.SphericalClean

/-!
# Label conventions for the `SL(2,ℝ)` Plancherel density

The code labels the principal series `principalSeries ε ν` by `ν`, with `mult = |t|^{iν-1}`
and Casimir `-(1+ν²)/4` (`casimir_principal`). The spherical Plancherel formula
`norm_sq_eq_sph` is written in the variable `ρ` of the radial eigenfunction `y^{1/2+iρ}`
of the hyperbolic Laplacian `y²(∂ₓ² + ∂ᵧ²)`, whose eigenvalue is `-(1/4+ρ²)`.
Matching the two Casimir values gives the dictionary `ρ = ν/2` (`|ν| = 2ρ`).
The complementary series is `ν = iτ`, `s = (1+τ)/2`, and is unitary exactly for `|τ| < 1`,
that is `σ = |τ|/2 ∈ (0, 1/2)`; its Casimir value `(τ²-1)/4` is `σ² - 1/4`.

Sources: `kitaev-2017` (Section 4), `knapp-1986` (Chapter II), `ggv-1966`; no equation number
is claimed.
-/

open Complex

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **Dictionary `ρ = ν/2`**: the Casimir value `-(1+ν²)/4` of the principal series with label `ν`
is `-(1/4 + ρ²)` for `ρ = ν/2`. -/
theorem casimir_principal_eq_rho (ν : ℝ) :
    (-(1 + (ν : ℂ) ^ 2) / 4) = -(1 / 4 + (((ν / 2 : ℝ)) : ℂ) ^ 2) := by
  push_cast; ring

/-- The hyperbolic Laplacian `y²(∂ₓ²+∂ᵧ²)` has `y^s` as eigenfunction with eigenvalue `s(s-1)`;
for `s = 1/2 + iρ` this is `-(1/4+ρ²)`. -/
theorem eigenvalue_half_line (ρ : ℝ) :
    ((1 / 2 : ℂ) + I * ρ) * ((1 / 2 : ℂ) + I * ρ - 1) = -(1 / 4 + (ρ : ℂ) ^ 2) := by
  linear_combination (ρ : ℂ) ^ 2 * Complex.I_sq

/-- **The Casimir value of the principal series is the hyperbolic eigenvalue** at
`s = 1/2 + i ν/2`. -/
theorem casimir_principal_eq_eigenvalue (ν : ℝ) :
    (-(1 + (ν : ℂ) ^ 2) / 4) =
      ((1 / 2 : ℂ) + I * ((ν / 2 : ℝ) : ℂ)) * ((1 / 2 : ℂ) + I * ((ν / 2 : ℝ) : ℂ) - 1) := by
  rw [eigenvalue_half_line, casimir_principal_eq_rho]

/-- The Plancherel density `ρ ↦ ρ tanh(πρ)` of the spherical principal series is even. -/
theorem density_even (ρ : ℝ) :
    (-ρ) * Real.tanh (Real.pi * -ρ) = ρ * Real.tanh (Real.pi * ρ) := by
  rw [mul_neg, Real.tanh_neg]; ring

/-- The Plancherel density `ρ tanh(πρ)` is strictly positive for `ρ ≠ 0`. -/
theorem density_pos {ρ : ℝ} (hρ : ρ ≠ 0) : 0 < ρ * Real.tanh (Real.pi * ρ) := by
  rcases lt_or_gt_of_ne hρ with h | h
  · have : Real.tanh (Real.pi * ρ) < 0 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_neg_of_neg_of_pos (Real.sinh_neg_iff.2 (by nlinarith [Real.pi_pos]))
        (Real.cosh_pos _)
    exact mul_pos_of_neg_of_neg h this
  · have : 0 < Real.tanh (Real.pi * ρ) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.2 (by positivity)) (Real.cosh_pos _)
    exact mul_pos h this

/-- The Casimir value of the complementary series `ν = iτ`, `τ` real, is `(τ²-1)/4`. -/
theorem casimir_complementary (τ : ℝ) :
    (-(1 + (I * (τ : ℂ)) ^ 2) / 4) = (((τ ^ 2 - 1) / 4 : ℝ) : ℂ) := by
  push_cast
  linear_combination (-(τ : ℂ) ^ 2 / 4) * Complex.I_sq

/-- The Casimir value of the complementary series is `σ² - 1/4` with `σ = τ/2`; it lies in
`(-1/4, 0)` iff `|τ| < 1`, and is positive iff `|τ| > 1` (the range excluded by
`no_invariant_form`). -/
theorem casimir_complementary_pos_iff (τ : ℝ) :
    0 < (τ ^ 2 - 1) / 4 ↔ 1 < |τ| := by
  rw [← one_lt_sq_iff_one_lt_abs]
  constructor <;> intro h <;> linarith

end Lightlike.Lorentz.SL2RPlancherel
