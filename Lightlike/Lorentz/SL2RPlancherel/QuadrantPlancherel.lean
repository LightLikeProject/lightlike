import Lightlike.Lorentz.SL2RPlancherel.DoubleIntegral

/-!
# The quadrant quadratic form of an odd Schwartz function on the Fourier side

For an odd Schwartz function `h` the quadrant form
`2 ∫_{y>0} conj h(y) ∫_{z>0} (L(z-y) - L(z+y)) h(z)` with `L = -log tanh (|x|/4)` equals
`2 ∫_{ξ>0} (π/ρ) tanh (π ρ) |𝓕 h ξ|²`, `ρ = 2π ξ`.  With `h = g'` this is the radial form of the
SL(2,ℝ) Plancherel formula for the spherical principal series, density `ρ tanh (π ρ)`.
-/

namespace Lightlike.Lorentz.SL2RPlancherel

open MeasureTheory Set
open scoped FourierTransform

/-- The Fourier transform of an odd function is odd. -/
theorem fourier_odd {h : ℝ → ℂ} (hh : ∀ x, h (-x) = - h x) (ξ : ℝ) :
    𝓕 h (-ξ) = - 𝓕 h ξ := by
  simp only [Real.fourier_real_eq]
  have h1 := integral_neg_eq_self (fun v : ℝ => (Real.fourierChar (-(v * -ξ)) • h v : ℂ)) volume
  rw [← h1, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp [hh v]

/-- The quadrant quadratic form of an odd Schwartz function on the Fourier side. -/
theorem integral_logTanhKernel_odd_quadrant (h : SchwartzMap ℝ ℂ) (hodd : ∀ x, h (-x) = - h x) :
    2 * ∫ y in Ioi (0:ℝ), starRingEnd ℂ (h y) *
        ∫ z in Ioi (0:ℝ), (((logTanhKernel (z - y) : ℝ) : ℂ) - ((logTanhKernel (z + y) : ℝ) : ℂ)) * h z =
      ∫ ξ in Ioi (0:ℝ),
        ((Real.pi / (2 * Real.pi * ξ) * Real.tanh (Real.pi * (2 * Real.pi * ξ)) : ℝ) : ℂ) *
        (2 * (starRingEnd ℂ (𝓕 (h : ℝ → ℂ) ξ) * 𝓕 (h : ℝ → ℂ) ξ)) := by
  have hL : Integrable (fun x : ℝ => ((logTanhKernel x : ℝ) : ℂ)) := integrable_logTanhKernel.ofReal
  rw [← integral_kernel_odd_quadrant hL (fun x => by simp [logTanhKernel_neg]) h hodd,
    ← integral_kernel_autocorr_eq hL h, integral_logTanhKernel_autocorr h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun ξ hξ => ?_)
  have : 𝓕 (h : ℝ → ℂ) (-ξ) = - 𝓕 (h : ℝ → ℂ) ξ := fourier_odd (fun x => hodd x) ξ
  simp only [this, map_neg, neg_mul_neg]
  ring

end Lightlike.Lorentz.SL2RPlancherel
