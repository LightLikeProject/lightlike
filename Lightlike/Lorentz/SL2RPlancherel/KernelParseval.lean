import Mathlib

/-!
# Parseval for an integrable kernel

For `L ∈ L¹(ℝ)` and a continuous integrable `A` whose Fourier transforms `𝓕 A`, `𝓕⁻ A` are
integrable, `∫ 𝓕 L(ξ) · 𝓕⁻ A(ξ) dξ = ∫ L(x) · A(x) dx` (Mathlib normalisation `e^{∓2πi xξ}`).

This is the glue of the SL(2,ℝ) Plancherel route: `L(x) = -log tanh (|x|/4)` is integrable with
known transform (`integral_cos_mul_neg_log_tanh`), and `A` is the autocorrelation of the derivative
of the Abel transform; the identity moves the quadratic form `∫∫ h(t) h(s) L(s-t)` to the Fourier
side without needing integrability of `𝓕 L` (which decays only like `1/ρ`).
-/

namespace Lightlike.Lorentz.SL2RPlancherel

open MeasureTheory
open scoped FourierTransform

/-- Multiplication formula plus Fourier inversion: `∫ 𝓕 L · 𝓕⁻ A = ∫ L · A`. -/
theorem integral_fourier_mul_fourierInv {L A : ℝ → ℂ} (hL : Integrable L) (hA : Continuous A)
    (hAi : Integrable A) (hFA : Integrable (𝓕 A)) (hFiA : Integrable (𝓕⁻ A)) :
    ∫ ξ, 𝓕 L ξ * 𝓕⁻ A ξ = ∫ x, L x * A x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
    (e := Real.fourierChar) (L := innerₗ ℝ) (f := L) (g := 𝓕⁻ A)
    Real.continuous_fourierChar continuous_inner hL hFiA
  have hinv : 𝓕 (𝓕⁻ A) = A := hA.fourier_fourierInv_eq hAi hFA
  simp only [smul_eq_mul] at h
  have h2 : ∫ ξ, 𝓕 L ξ * 𝓕⁻ A ξ = ∫ x, L x * 𝓕 (𝓕⁻ A) x := by
    simpa using! h
  rw [h2, hinv]

/-- The same for a Schwartz function `A`: all the regularity hypotheses hold automatically. -/
theorem integral_fourier_mul_fourierInv_schwartz {L : ℝ → ℂ} (hL : Integrable L)
    (A : SchwartzMap ℝ ℂ) :
    ∫ ξ, 𝓕 L ξ * 𝓕⁻ (A : ℝ → ℂ) ξ = ∫ x, L x * A x :=
  integral_fourier_mul_fourierInv hL A.continuous A.integrable
    (by
      have := SchwartzMap.integrable (μ := volume) (𝓕 A : SchwartzMap ℝ ℂ)
      rwa [SchwartzMap.fourier_coe] at this)
    (by
      have := SchwartzMap.integrable (μ := volume) (𝓕⁻ A : SchwartzMap ℝ ℂ)
      rwa [SchwartzMap.fourierInv_coe] at this)

end Lightlike.Lorentz.SL2RPlancherel
