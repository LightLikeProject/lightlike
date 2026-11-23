import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.AbelSchwartz

/-!
# Linearity of the Abel and spherical transforms on test functions

`abelTransform` and `sphTransformH` are defined by (iterated) integrals, so their linearity in `F`
needs integrability. For `F` continuous with compact support the horocycle integrand
`w ↦ F (cosh t + w²/2)` is continuous with compact support, and for `F` smooth with compact support
`𝒜F` is continuous with compact support, which gives the linearity of `sphTransformH` on
`C_c^∞`. This is the groundwork for extending the spherical Plancherel identity
`norm_sq_eq_sph` from test functions to `L²` (milestone HA3).
-/

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- A compactly supported function vanishes to the right of some point. -/
theorem exists_eq_zero_of_hasCompactSupport {F : ℝ → ℂ} (hc : HasCompactSupport F) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, R ≤ x → F x = 0 := by
  obtain ⟨R, hR⟩ := hc.isCompact.bddAbove
  refine ⟨max R 0 + 1, by positivity, fun x hx => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have := hR hmem
  have := le_max_left R 0
  linarith

/-- The horocycle integrand `w ↦ F (cosh t + w²/2)` is integrable for `F` continuous with compact
support. -/
theorem integrable_abel_integrand {F : ℝ → ℂ} (hF : Continuous F) (hc : HasCompactSupport F)
    (t : ℝ) : Integrable (fun w : ℝ => F (Real.cosh t + w ^ 2 / 2)) := by
  obtain ⟨R, hR0, hR⟩ := exists_eq_zero_of_hasCompactSupport hc
  have hcont : Continuous (fun w : ℝ => F (Real.cosh t + w ^ 2 / 2)) := by fun_prop
  refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro
    (isCompact_closedBall (0 : ℝ) (R + 2)) fun w hw => ?_)
  have hw' : R + 2 < |w| := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hw
  apply hR
  have h1 : 1 ≤ Real.cosh t := Real.one_le_cosh t
  have h2 : (R + 2) ^ 2 < |w| ^ 2 := by gcongr
  rw [sq_abs] at h2
  nlinarith

/-- The Abel transform is additive on continuous compactly supported functions. -/
theorem abelTransform_add {F G : ℝ → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hG : Continuous G) (hGc : HasCompactSupport G) (t : ℝ) :
    abelTransform (F + G) t = abelTransform F t + abelTransform G t := by
  unfold abelTransform
  rw [← integral_add (integrable_abel_integrand hF hFc t) (integrable_abel_integrand hG hGc t)]
  rfl

/-- The Abel transform is homogeneous. -/
theorem abelTransform_smul (c : ℂ) (F : ℝ → ℂ) (t : ℝ) :
    abelTransform (c • F) t = c * abelTransform F t := by
  unfold abelTransform
  rw [← integral_const_mul]
  rfl

/-- The Abel transform is subtractive on continuous compactly supported functions. -/
theorem abelTransform_sub {F G : ℝ → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hG : Continuous G) (hGc : HasCompactSupport G) (t : ℝ) :
    abelTransform (F - G) t = abelTransform F t - abelTransform G t := by
  unfold abelTransform
  rw [← integral_sub (integrable_abel_integrand hF hFc t) (integrable_abel_integrand hG hGc t)]
  rfl

/-- The Fourier integrand `e^{iρt} 𝒜F(t)` is integrable for `F` smooth with compact support. -/
theorem integrable_exp_abelTransform {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (ρ : ℝ) : Integrable (fun t : ℝ => Complex.exp (ρ * t * Complex.I) * abelTransform F t) := by
  have hcont : Continuous (fun t : ℝ => Complex.exp (ρ * t * Complex.I) * abelTransform F t) :=
    (by fun_prop : Continuous fun t : ℝ => Complex.exp (ρ * t * Complex.I)).mul
      (contDiff_abelTransform F hF hc).continuous
  exact hcont.integrable_of_hasCompactSupport
    ((hasCompactSupport_abelTransform F hc).mul_left)

/-- The spherical transform is additive on smooth compactly supported functions. -/
theorem sphTransformH_add {F G : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) (ρ : ℝ) :
    sphTransformH (F + G) ρ = sphTransformH F ρ + sphTransformH G ρ := by
  simp only [sphTransformH_eq_integral_abel]
  rw [← integral_add (integrable_exp_abelTransform hF hFc ρ) (integrable_exp_abelTransform hG hGc ρ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [abelTransform_add hF.continuous hFc hG.continuous hGc, mul_add]

/-- The spherical transform is homogeneous. -/
theorem sphTransformH_smul (c : ℂ) (F : ℝ → ℂ) (ρ : ℝ) :
    sphTransformH (c • F) ρ = c * sphTransformH F ρ := by
  simp only [sphTransformH_eq_integral_abel]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [abelTransform_smul]
  ring

/-- The spherical transform is subtractive on smooth compactly supported functions. -/
theorem sphTransformH_sub {F G : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) (ρ : ℝ) :
    sphTransformH (F - G) ρ = sphTransformH F ρ - sphTransformH G ρ := by
  simp only [sphTransformH_eq_integral_abel]
  rw [← integral_sub (integrable_exp_abelTransform hF hFc ρ) (integrable_exp_abelTransform hG hGc ρ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [abelTransform_sub hF.continuous hFc hG.continuous hGc, mul_sub]

end Lightlike.Lorentz.SL2RPlancherel
