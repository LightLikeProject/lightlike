import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalCoeff

/-!
# The Harish-Chandra majorant of the principal-series matrix coefficients

Every matrix coefficient of the even principal series is dominated by the `ν`- and
`K`-type-independent function
`Ξ(ξ) = e^{ξ/2} ∫ (1 + x²)^{-1/2} (1 + e^{2ξ} x²)^{-1/2} dx` (`norm_mcoefP_le`): the integrand of
`Φ^ν_{m,n}(ξ)` has exactly this modulus, since `|e_k(x)| = (1 + x²)^{-1/2}` and `|e^{-wξ}| = e^{ξ/2}`.
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (decay of the matrix coefficients, for the
opposite-sign blocks), milestone HA3.
-/

open MeasureTheory Set Complex

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The majorant `Ξ(ξ) = e^{ξ/2} ∫ (1 + x²)^{-1/2} (1 + (e^ξ x)²)^{-1/2} dx`. -/
def hcXi (ξ : ℝ) : ℝ :=
  ∫ x : ℝ, (1 + x ^ 2) ^ (-(1 : ℝ) / 2) * (Real.exp (ξ / 2) *
    (1 + (Real.exp ξ * x) ^ 2) ^ (-(1 : ℝ) / 2))

/-- **The Harish-Chandra majorant**: `|Φ^ν_{m,n}(ξ)| ≤ Ξ(ξ)` for every `ν, m, n`. -/
theorem norm_mcoefP_le (ν ξ : ℝ) (m n : ℤ) : ‖mcoefP ν m n ξ‖ ≤ hcXi ξ := by
  rw [mcoefP_eq_integral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext x
  rw [norm_mul, norm_mul, RCLike.norm_conj, norm_kVecP, norm_exp_neg_wP, norm_kVecP]

end Lightlike.Lorentz.SL2RPlancherel
