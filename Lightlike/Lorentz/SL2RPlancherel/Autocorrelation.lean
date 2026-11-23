import Lightlike.Lorentz.SL2RPlancherel.KernelParseval

/-!
# The autocorrelation of a Schwartz function

For a Schwartz function `h`, `reflConj h (x) = conj (h (-x))` is Schwartz, its Fourier transform is
`conj (𝓕 h)`, and the convolution `A = reflConj h ⋆ h` (the autocorrelation of `h`) has
`𝓕 A = |𝓕 h|²`.  Together with `integral_fourier_mul_fourierInv_schwartz` this moves the quadratic
form `∫∫ L(y - x) conj h(x) h(y)` to the Fourier side (step 3 of the SL(2,ℝ) Plancherel route).
-/

namespace Lightlike.Lorentz.SL2RPlancherel

open MeasureTheory
open scoped FourierTransform

/-- `x ↦ conj (h (-x))` as a Schwartz function. -/
noncomputable def reflConj (h : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) (Complex.conjCLE.toContinuousLinearMap)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (ContinuousLinearEquiv.neg ℝ) h)

@[simp] theorem reflConj_apply (h : SchwartzMap ℝ ℂ) (x : ℝ) :
    reflConj h x = starRingEnd ℂ (h (-x)) := rfl

/-- The Fourier transform of `reflConj h` is the conjugate of `𝓕 h`. -/
theorem fourier_reflConj (h : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (reflConj h : ℝ → ℂ) ξ = starRingEnd ℂ (𝓕 (h : ℝ → ℂ) ξ) := by
  simp only [Real.fourier_eq, reflConj_apply]
  rw [← integral_conj]
  have key := integral_neg_eq_self (fun v : ℝ =>
    (Real.fourierChar (-(inner ℝ v ξ)) • starRingEnd ℂ (h (-v)) : ℂ)) volume
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [neg_neg, Circle.smul_def, smul_eq_mul, map_mul, inner_neg_left,
    Real.fourierChar_apply]
  congr 1
  rw [← Complex.exp_conj]
  simp [Complex.conj_ofReal, map_ofNat]

/-- The autocorrelation `x ↦ ∫ conj (h (y - x)) h y dy` of a Schwartz function, as a Schwartz
function: the convolution of `reflConj h` with `h`. -/
noncomputable def autocorr (h : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (reflConj h) h

/-- `𝓕 (autocorr h) = |𝓕 h|²`. -/
theorem fourier_autocorr (h : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (autocorr h : ℝ → ℂ) ξ = starRingEnd ℂ (𝓕 (h : ℝ → ℂ) ξ) * 𝓕 (h : ℝ → ℂ) ξ := by
  have := congrArg (fun F : SchwartzMap ℝ ℂ => F ξ)
    (SchwartzMap.fourier_convolution (ContinuousLinearMap.mul ℂ ℂ) (reflConj h) h)
  simp only [SchwartzMap.fourier_coe] at this
  simp only [autocorr]
  rw [this]
  simp [SchwartzMap.pairing_apply_apply, SchwartzMap.fourier_coe, fourier_reflConj]

/-- The autocorrelation at `x`: `∫ conj (h y) · h (y + x) dy`. -/
theorem autocorr_apply (h : SchwartzMap ℝ ℂ) (x : ℝ) :
    autocorr h x = ∫ y, starRingEnd ℂ (h y) * h (y + x) := by
  rw [autocorr, SchwartzMap.convolution_apply, MeasureTheory.convolution_def]
  rw [← integral_neg_eq_self (fun y : ℝ => starRingEnd ℂ (h y) * h (y + x)) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [sub_eq_add_neg, add_comm]

/-- The quadratic form of an integrable kernel `L` on a Schwartz function, on the Fourier side:
`∫ L(x) ∫ conj h(y) h(y + x) dy dx = ∫ 𝓕 L(ξ) |𝓕 h(-ξ)|² dξ` (Mathlib normalisation
`e^{-2πi xξ}`). -/
theorem integral_kernel_autocorr {L : ℝ → ℂ} (hL : Integrable L) (h : SchwartzMap ℝ ℂ) :
    ∫ x, L x * ∫ y, starRingEnd ℂ (h y) * h (y + x) =
      ∫ ξ, 𝓕 L ξ * (starRingEnd ℂ (𝓕 (h : ℝ → ℂ) (-ξ)) * 𝓕 (h : ℝ → ℂ) (-ξ)) := by
  have := integral_fourier_mul_fourierInv_schwartz hL (autocorr h)
  simp only [Real.fourierInv_eq_fourier_neg, fourier_autocorr, autocorr_apply] at this
  exact this.symm

end Lightlike.Lorentz.SL2RPlancherel
