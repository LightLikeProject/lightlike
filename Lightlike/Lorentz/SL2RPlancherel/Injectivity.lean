import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.SphericalClean

/-!
# Injectivity of the spherical transform of the hyperbolic plane

A consequence of the spherical Plancherel identity `norm_sq_eq_sph` (density `ρ tanh(πρ)`,
milestone HA3): a radial test function whose spherical transform vanishes on `ρ > 0` vanishes
(on `v > 1`, i.e. away from the base point). Sources: `kitaev-2017` (Section 4), `knapp-1986`
(Chapter II); no equation number is claimed.
-/

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The `L²(1,∞)` norm of a test function is zero when its spherical transform vanishes on
`ρ > 0`. -/
theorem integral_norm_sq_eq_zero_of_sph_zero (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (h : ∀ ρ : ℝ, 0 < ρ → sphTransformH F ρ = 0) :
    ∫ v in Ioi (1 : ℝ), ‖F v‖ ^ 2 = 0 := by
  have h1 := norm_sq_eq_sph F hF hc
  have h2 : ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) * ‖sphTransformH F ρ‖ ^ 2 = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ))]
    · simp
    · intro ρ hρ
      simp [h ρ hρ]
  rw [h2] at h1
  have hp : Real.pi ^ 2 ≠ 0 := by positivity
  simpa [hp] using h1

/-- **Injectivity of the spherical transform** on radial test functions: if `f̂(ρ) = 0` for all
`ρ > 0` then `F v = 0` for all `v > 1`. -/
theorem eqOn_zero_of_sph_zero (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (h : ∀ ρ : ℝ, 0 < ρ → sphTransformH F ρ = 0) :
    ∀ v : ℝ, 1 < v → F v = 0 := by
  have h0 := integral_norm_sq_eq_zero_of_sph_zero F hF hc h
  have hcont : Continuous fun v => ‖F v‖ ^ 2 := (hF.continuous.norm).pow 2
  have hint : Integrable (fun v => ‖F v‖ ^ 2) :=
    hcont.integrable_of_hasCompactSupport (hc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))
  have hae := (integral_eq_zero_iff_of_nonneg (μ := volume.restrict (Ioi (1 : ℝ)))
    (fun v => by positivity) hint.integrableOn).1 h0
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hcont.continuousOn
    continuousOn_const
  intro v hv
  have := heq hv
  simpa using this

end Lightlike.Lorentz.SL2RPlancherel
