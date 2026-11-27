import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalCoeff
import Lightlike.Lorentz.SL2RPlancherel.AbelTransform

/-!
# The spherical matrix coefficient of the even principal series

For the `K`-fixed vector `e_0(x) = (1 + x²)^w`, `w = (iν - 1)/2`, the matrix coefficient
`Φ^ν_{0,0}(ξ) = ⟪e_0, π(a(ξ)) e_0⟫` is an average of `u^w` with
`u_ξ(x) = (e^{-ξ} + e^ξ x²)/(1 + x²)` against `dx/(1 + x²)` (`mcoefP_zero_zero`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (the spherical base of the identification of
the block transforms with matrix coefficients), milestone HA3.
-/

open MeasureTheory Set Complex Lightlike.Lorentz.SL2R

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `u_ξ(x) = (e^{-ξ} + e^ξ x²)/(1 + x²)`, which runs over `[e^{-ξ}, e^ξ)`. -/
def sphU (ξ x : ℝ) : ℝ := (Real.exp (-ξ) + Real.exp ξ * x ^ 2) / (1 + x ^ 2)

lemma sphU_pos (ξ x : ℝ) : 0 < sphU ξ x := by
  unfold sphU; positivity

/-- `conj w = -w - 1`. -/
lemma conj_wP (ν : ℝ) : (starRingEnd ℂ) (wP ν) = -wP ν - 1 := by
  simp only [wP, map_div₀, map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal, map_one,
    map_ofNat]
  ring

/-- `r^z = exp(z log r)` for `r > 0`. -/
lemma ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (r : ℂ) ^ z = Complex.exp (z * Real.log r) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), Complex.ofReal_log hr.le, mul_comm]

/-- **The spherical matrix coefficient**:
`Φ^ν_{0,0}(ξ) = ∫ u_ξ(x)^w dx/(1 + x²)`. -/
theorem mcoefP_zero_zero (ν ξ : ℝ) :
    mcoefP ν 0 0 ξ =
      ∫ x, Complex.exp (wP ν * Real.log (sphU ξ x)) / ((1 + x ^ 2 : ℝ) : ℂ) := by
  rw [mcoefP_eq_integral]
  congr 1
  funext x
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h2 : (0 : ℝ) < 1 + (Real.exp ξ * x) ^ 2 := by positivity
  have h3 : (0 : ℝ) < Real.exp (-ξ) + Real.exp ξ * x ^ 2 := by positivity
  simp only [kVecP, zpow_zero, mul_one]
  rw [show ((I * ν - 1) / 2 : ℂ) = wP ν from rfl, ofReal_cpow_eq_exp h1, ofReal_cpow_eq_exp h2,
    ← Complex.exp_conj, map_mul, conj_wP, Complex.conj_ofReal]
  have hr2 : 1 + (Real.exp ξ * x) ^ 2 = Real.exp ξ * (Real.exp (-ξ) + Real.exp ξ * x ^ 2) := by
    rw [mul_add, ← Real.exp_add, add_neg_cancel, Real.exp_zero]; ring
  have hlog2 : Real.log (1 + (Real.exp ξ * x) ^ 2) =
      ξ + Real.log (Real.exp (-ξ) + Real.exp ξ * x ^ 2) := by
    rw [hr2, Real.log_mul (Real.exp_pos _).ne' h3.ne', Real.log_exp]
  have hlogu : Real.log (sphU ξ x) =
      Real.log (Real.exp (-ξ) + Real.exp ξ * x ^ 2) - Real.log (1 + x ^ 2) := by
    rw [sphU, Real.log_div h3.ne' h1.ne']
  have he : ((1 + x ^ 2 : ℝ) : ℂ) = Complex.exp (Real.log (1 + x ^ 2)) := by
    rw [← Complex.ofReal_exp, Real.exp_log h1]
  rw [he, ← Complex.exp_sub, ← Complex.exp_add, ← Complex.exp_add, hlog2, hlogu]
  congr 1
  push_cast
  ring

end Lightlike.Lorentz.SL2RPlancherel
