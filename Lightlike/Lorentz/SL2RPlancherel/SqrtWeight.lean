import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.WeightIntegrable

/-!
# The square-root-weighted spherical transform as an `L²(0, ∞)` function

Absorbing the Plancherel density into the function, `Ŝ F (ρ) = √(ρ tanh(πρ)) f̂(ρ) / (2π)`, the
identity `norm_sq_eq_sph` becomes the isometry `‖Ŝ F‖²_{L²(0,∞)} = ‖F‖²_{L²(1,∞)}` on
`C_c^∞` (milestone HA3). Here we show `Ŝ F ∈ L²(0, ∞)` and compute its norm; the extension
by density is in `SphericalL2`.
-/

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `ρ ↦ tanh(πρ)` is continuous. -/
theorem continuous_tanh_pi_mul : Continuous fun ρ : ℝ => Real.tanh (Real.pi * ρ) := by
  simp only [Real.tanh_eq_sinh_div_cosh]
  exact (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).div
    (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
    (fun x => (Real.cosh_pos _).ne')

/-- `ρ tanh(πρ) ≥ 0` for every real `ρ`. -/
theorem mul_tanh_pi_mul_nonneg (ρ : ℝ) : 0 ≤ ρ * Real.tanh (Real.pi * ρ) := by
  rcases le_total 0 ρ with h | h
  · refine mul_nonneg h ?_
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.2 (by positivity)) (Real.cosh_pos _).le
  · refine mul_nonneg_of_nonpos_of_nonpos h ?_
    rw [Real.tanh_eq_sinh_div_cosh]
    have : Real.sinh (Real.pi * ρ) ≤ 0 :=
      (Real.sinh_nonpos_iff).2 (mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le h)
    exact div_nonpos_of_nonpos_of_nonneg this (Real.cosh_pos _).le

/-- The square-root-weighted spherical transform `√(ρ tanh(πρ)) f̂(ρ) / (2π)`. -/
def sphL2fun (F : ℝ → ℂ) (ρ : ℝ) : ℂ :=
  ((Real.sqrt (ρ * Real.tanh (Real.pi * ρ)) / (2 * Real.pi) : ℝ) : ℂ) * sphTransformH F ρ

/-- The squared norm of `sphL2fun` is the Plancherel-weighted square of `f̂`. -/
theorem norm_sq_sphL2fun (F : ℝ → ℂ) (ρ : ℝ) :
    ‖sphL2fun F ρ‖ ^ 2 =
      (ρ * Real.tanh (Real.pi * ρ) * ‖sphTransformH F ρ‖ ^ 2) / (4 * Real.pi ^ 2) := by
  unfold sphL2fun
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt (mul_tanh_pi_mul_nonneg ρ)]
  field_simp
  ring

/-- `sphL2fun F` is continuous for `F` smooth with compact support. -/
theorem continuous_sphL2fun (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    Continuous (sphL2fun F) := by
  have hmeas : Continuous (fun ρ : ℝ => sphTransformH F ρ) := by
    have : (fun ρ : ℝ => sphTransformH F ρ) = fun ρ =>
        (SchwartzMap.fourierTransformCLM ℂ (abelSchwartz F hF hc)) (ρ / (2 * Real.pi)) :=
      funext (sphTransformH_eq_schwartz F hF hc)
    rw [this]
    exact (SchwartzMap.fourierTransformCLM ℂ (abelSchwartz F hF hc)).continuous.comp
      (continuous_id.div_const _)
  have h1 : Continuous fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) :=
    continuous_id.mul continuous_tanh_pi_mul
  unfold sphL2fun
  exact (Complex.continuous_ofReal.comp
    ((Real.continuous_sqrt.comp h1).div_const _)).mul hmeas

/-- `sphL2fun F ∈ L²(0, ∞)` for `F` smooth with compact support. -/
theorem memLp_sphL2fun (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    MemLp (sphL2fun F) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  rw [memLp_two_iff_integrable_sq_norm
    (continuous_sphL2fun F hF hc).aestronglyMeasurable]
  have h := (integrableOn_sph_weight F hF hc).div_const (4 * Real.pi ^ 2)
  refine h.congr (Filter.Eventually.of_forall fun ρ => ?_)
  exact (norm_sq_sphL2fun F ρ).symm

/-- **Isometry on test functions**: `∫_{ρ>0} ‖Ŝ F ρ‖² dρ = ∫_{v>1} ‖F v‖² dv`. -/
theorem integral_norm_sq_sphL2fun (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ∫ ρ in Ioi (0 : ℝ), ‖sphL2fun F ρ‖ ^ 2 = ∫ v in Ioi (1 : ℝ), ‖F v‖ ^ 2 := by
  simp_rw [norm_sq_sphL2fun]
  rw [integral_div]
  have h := norm_sq_eq_sph F hF hc
  have hp : (Real.pi : ℝ) ^ 2 ≠ 0 := by positivity
  have hJ : ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) * ‖sphTransformH F ρ‖ ^ 2 =
      4 * Real.pi ^ 2 * ∫ v in Ioi (1 : ℝ), ‖F v‖ ^ 2 := by linarith
  rw [hJ]
  field_simp

end Lightlike.Lorentz.SL2RPlancherel
