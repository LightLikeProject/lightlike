import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.Linearity
import Lightlike.Lorentz.SL2RPlancherel.SphericalClean

/-!
# Integrability of the Plancherel-weighted spherical transform

For `F` smooth with compact support, `f̂ = sphTransformH F` is (a rescaling of) the Fourier transform
of the Schwartz function `𝒜F`, hence a Schwartz function in `ρ`; the weighted square
`ρ tanh(πρ) |f̂(ρ)|²` is therefore integrable on `(0, ∞)` (milestone HA3). This makes the right-hand
side of `norm_sq_eq_sph` a genuine `L²` norm, the first step toward its `L²` extension.
-/

open MeasureTheory Set Real
open scoped FourierTransform ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `f̂(ρ)` is the Schwartz function `𝓕 (𝒜F)` evaluated at `ρ / (2π)`. -/
theorem sphTransformH_eq_schwartz (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (ρ : ℝ) : sphTransformH F ρ =
      (SchwartzMap.fourierTransformCLM ℂ (abelSchwartz F hF hc)) (ρ / (2 * Real.pi)) := by
  have h := fourier_abelTransform F (ρ / (2 * Real.pi))
  have h2 : 2 * Real.pi * (ρ / (2 * Real.pi)) = ρ := by
    field_simp
  rw [h2] at h
  rw [← h]
  rfl

/-- `f̂` is bounded for `F` smooth with compact support. -/
theorem norm_sphTransformH_le (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ∃ C : ℝ, ∀ ρ : ℝ, ‖sphTransformH F ρ‖ ≤ C := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0
    (SchwartzMap.fourierTransformCLM ℂ (abelSchwartz F hF hc)), fun ρ => ?_⟩
  rw [sphTransformH_eq_schwartz F hF hc]
  exact SchwartzMap.norm_le_seminorm ℝ _ _

/-- The Plancherel-weighted square `ρ tanh(πρ) |f̂(ρ)|²` is integrable on `(0, ∞)`. -/
theorem integrableOn_sph_weight (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    IntegrableOn (fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) * ‖sphTransformH F ρ‖ ^ 2)
      (Ioi (0 : ℝ)) := by
  set h := SchwartzMap.fourierTransformCLM ℂ (abelSchwartz F hF hc) with hh
  obtain ⟨C, hC⟩ := norm_sphTransformH_le F hF hc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hint : Integrable (fun ρ : ℝ => ‖ρ / (2 * Real.pi)‖ ^ 1 * ‖h (ρ / (2 * Real.pi))‖) :=
    (h.integrable_pow_mul volume 1).comp_mul_left' (R := (2 * Real.pi)⁻¹) (by positivity) |>.congr
      (Filter.Eventually.of_forall fun ρ => by simp [div_eq_inv_mul])
  have hmeas : Continuous (fun ρ : ℝ => sphTransformH F ρ) := by
    have : (fun ρ : ℝ => sphTransformH F ρ) = fun ρ => h (ρ / (2 * Real.pi)) :=
      funext (sphTransformH_eq_schwartz F hF hc)
    rw [this]
    exact h.continuous.comp (continuous_id.div_const _)
  refine Integrable.mono' ((hint.const_mul (2 * Real.pi * C)).integrableOn)
    (by
      have : Continuous fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) * ‖sphTransformH F ρ‖ ^ 2 := by
        have h1 := hmeas.norm
        have h2 : Continuous fun ρ : ℝ => Real.tanh (Real.pi * ρ) := by
          simp only [Real.tanh_eq_sinh_div_cosh]
          exact (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).div
            (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
            (fun x => (Real.cosh_pos _).ne')
        exact (continuous_id.mul h2).mul (h1.pow 2)
      exact this.aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun ρ hρ => ?_
  have hρ' : 0 < ρ := hρ
  have ht0 : 0 ≤ Real.tanh (Real.pi * ρ) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact (div_pos (Real.sinh_pos_iff.2 (by positivity)) (Real.cosh_pos _)).le
  have ht1 : Real.tanh (Real.pi * ρ) ≤ 1 := (Real.tanh_lt_one _).le
  have hnn : 0 ≤ ρ * Real.tanh (Real.pi * ρ) * ‖sphTransformH F ρ‖ ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have hs : ‖sphTransformH F ρ‖ = ‖h (ρ / (2 * Real.pi))‖ := by
    rw [sphTransformH_eq_schwartz F hF hc]
  have hb : ‖sphTransformH F ρ‖ ≤ C := hC ρ
  have hn : ‖ρ / (2 * Real.pi)‖ = ρ / (2 * Real.pi) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  simp only [pow_one, hn]
  rw [← hs]
  have e1 : ρ = 2 * Real.pi * (ρ / (2 * Real.pi)) := by field_simp
  have e2 : ρ * Real.tanh (Real.pi * ρ) * ‖sphTransformH F ρ‖ ^ 2 ≤
      ρ * ‖sphTransformH F ρ‖ ^ 2 := by
    have : 0 ≤ ρ * ‖sphTransformH F ρ‖ ^ 2 := by positivity
    nlinarith
  have e3 : ρ * ‖sphTransformH F ρ‖ ^ 2 ≤ ρ * (C * ‖sphTransformH F ρ‖) := by
    gcongr
    rw [sq]
    gcongr
  calc ρ * Real.tanh (Real.pi * ρ) * ‖sphTransformH F ρ‖ ^ 2
      ≤ ρ * (C * ‖sphTransformH F ρ‖) := e2.trans e3
    _ = 2 * Real.pi * C * (ρ / (2 * Real.pi) * ‖sphTransformH F ρ‖) := by
        field_simp

end Lightlike.Lorentz.SL2RPlancherel
