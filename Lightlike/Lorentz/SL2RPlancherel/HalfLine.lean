import Lightlike.Lorentz.SL2RPlancherel.Autocorrelation
import Lightlike.Lorentz.SL2RPlancherel.LogTanhKernel

/-!
# The autocorrelation identity folded onto the half line

For an even integrable kernel `L` and a Schwartz function `h`,
`integral_kernel_autocorr` is an integral over `ℝ` of `𝓕 L ξ · |𝓕 h (-ξ)|²`.  Since `𝓕 L` is even
this folds onto `ξ > 0`, where `fourier_logTanhKernel` gives `𝓕 L ξ = (π/ρ) tanh (π ρ)`,
`ρ = 2π ξ`: this is the form in which the density `ρ tanh (π ρ)` of the SL(2,ℝ) Plancherel
formula for the spherical principal series appears.
-/

namespace Lightlike.Lorentz.SL2RPlancherel

open MeasureTheory Set
open scoped FourierTransform

/-- The Fourier transform of an even function is even. -/
theorem fourier_even {L : ℝ → ℂ} (hL : ∀ x, L (-x) = L x) (ξ : ℝ) :
    𝓕 L (-ξ) = 𝓕 L ξ := by
  simp only [Real.fourier_real_eq]
  have h1 := integral_neg_eq_self (fun v : ℝ => (Real.fourierChar (-(v * -ξ)) • L v : ℂ)) volume
  rw [← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp [hL v]

/-- Folding an integrable integral over `ℝ` onto `(0, ∞)`. -/
theorem integral_eq_Ioi_add_neg {G : ℝ → ℂ} (hG : Integrable G) :
    ∫ ξ, G ξ = ∫ ξ in Ioi (0:ℝ), (G ξ + G (-ξ)) := by
  have h1 : IntegrableOn (fun ξ => G (-ξ)) (Ioi (0:ℝ)) :=
    (hG.comp_neg).integrableOn
  rw [integral_add hG.integrableOn h1, integral_comp_neg_Ioi, neg_zero,
    add_comm, intervalIntegral.integral_Iic_add_Ioi hG.integrableOn hG.integrableOn]

/-- The Fourier transform of an integrable function is continuous. -/
theorem continuous_fourier_of_integrable {L : ℝ → ℂ} (hL : Integrable L) : Continuous (𝓕 L) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hL

/-- `integral_kernel_autocorr` for an even kernel, folded onto `ξ > 0`:
`∫ L(x) ∫ conj h(y) h(y+x) dy dx = ∫_{ξ>0} 𝓕 L ξ · (|𝓕 h ξ|² + |𝓕 h (-ξ)|²) dξ`. -/
theorem integral_kernel_autocorr_half {L : ℝ → ℂ} (hL : Integrable L) (hLe : ∀ x, L (-x) = L x)
    (h : SchwartzMap ℝ ℂ) :
    ∫ x, L x * ∫ y, starRingEnd ℂ (h y) * h (y + x) =
      ∫ ξ in Ioi (0:ℝ), 𝓕 L ξ * (starRingEnd ℂ (𝓕 (h : ℝ → ℂ) (-ξ)) * 𝓕 (h : ℝ → ℂ) (-ξ)
        + starRingEnd ℂ (𝓕 (h : ℝ → ℂ) ξ) * 𝓕 (h : ℝ → ℂ) ξ) := by
  rw [integral_kernel_autocorr hL h]
  have hint : Integrable (fun ξ : ℝ => 𝓕 L ξ *
      (starRingEnd ℂ (𝓕 (h : ℝ → ℂ) (-ξ)) * 𝓕 (h : ℝ → ℂ) (-ξ))) := by
    have hS : Integrable (fun ξ : ℝ => (starRingEnd ℂ (𝓕 (h : ℝ → ℂ) (-ξ)) *
        𝓕 (h : ℝ → ℂ) (-ξ))) := by
      have := (SchwartzMap.integrable (μ := volume)
        (𝓕 (autocorr h : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)).comp_neg
      simpa [SchwartzMap.fourier_coe, fourier_autocorr] using this
    refine hS.bdd_mul (continuous_fourier_of_integrable hL).aestronglyMeasurable
      (c := ∫ v, ‖L v‖) (Filter.Eventually.of_forall fun ξ => ?_)
    exact Real.norm_fourier_le_integral_norm L ξ
  rw [integral_eq_Ioi_add_neg hint]
  refine setIntegral_congr_fun measurableSet_Ioi (fun ξ _ => ?_)
  simp only [neg_neg, fourier_even hLe ξ]
  ring

/-- The quadratic form of the kernel `−log tanh (|x|/4)` on a Schwartz function, on the Fourier side:
with `ρ = 2π ξ`, the weight is `(π/ρ) tanh (π ρ)`. -/
theorem integral_logTanhKernel_autocorr (h : SchwartzMap ℝ ℂ) :
    ∫ x, ((logTanhKernel x : ℝ) : ℂ) * ∫ y, starRingEnd ℂ (h y) * h (y + x) =
      ∫ ξ in Ioi (0:ℝ),
        ((Real.pi / (2 * Real.pi * ξ) * Real.tanh (Real.pi * (2 * Real.pi * ξ)) : ℝ) : ℂ) *
        (starRingEnd ℂ (𝓕 (h : ℝ → ℂ) (-ξ)) * 𝓕 (h : ℝ → ℂ) (-ξ)
          + starRingEnd ℂ (𝓕 (h : ℝ → ℂ) ξ) * 𝓕 (h : ℝ → ℂ) ξ) := by
  rw [integral_kernel_autocorr_half
    (L := fun x : ℝ => ((logTanhKernel x : ℝ) : ℂ))
    (integrable_logTanhKernel.ofReal)
    (fun x => by simp [logTanhKernel_neg]) h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun ξ hξ => ?_)
  rw [fourier_logTanhKernel hξ]

end Lightlike.Lorentz.SL2RPlancherel
