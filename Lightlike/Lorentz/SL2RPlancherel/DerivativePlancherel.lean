import Lightlike.Lorentz.SL2RPlancherel.QuadrantPlancherel
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# The quadrant form of the derivative of an even Schwartz function

For an even Schwartz function `g`, its derivative `g'` is odd and `𝓕 g' ξ = 2π i ξ 𝓕 g ξ`.  The
quadrant form of `g'` against the kernel `-log tanh (|x|/4)` therefore has, on the Fourier side,
the weight `(π/ρ) tanh (π ρ) · ρ² = π ρ tanh (π ρ)`, `ρ = 2π ξ`: the Plancherel density of the
spherical principal series of SL(2,ℝ).
-/

namespace Lightlike.Lorentz.SL2RPlancherel

open MeasureTheory Set
open scoped FourierTransform

/-- The derivative of an even function is odd. -/
theorem deriv_odd_of_even {g : ℝ → ℂ} (hg : ∀ x, g (-x) = g x) (x : ℝ) :
    deriv g (-x) = - deriv g x := by
  have h : (fun y => g (-y)) = g := funext hg
  have := deriv_comp_neg (f := g) (x := x)
  rw [h] at this
  rw [this]; ring

/-- The Fourier transform of the derivative of a Schwartz function: `𝓕 g' ξ = 2π i ξ 𝓕 g ξ`. -/
theorem fourier_deriv_schwartz (g : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (SchwartzMap.derivCLM ℂ ℂ g : ℝ → ℂ) ξ
      = (2 * Real.pi * Complex.I * ξ) * 𝓕 (g : ℝ → ℂ) ξ := by
  have h1 : (SchwartzMap.derivCLM ℂ ℂ g : ℝ → ℂ) = deriv (g : ℝ → ℂ) :=
    funext fun x => SchwartzMap.derivCLM_apply ℂ g x
  rw [h1, Real.fourier_deriv g.integrable g.differentiable
    (by rw [← h1]; exact (SchwartzMap.derivCLM ℂ ℂ g).integrable)]
  simp [smul_eq_mul]

/-- The quadrant form of the derivative of an even Schwartz function `g` on the Fourier side, with
weight `π ρ tanh (π ρ)`, `ρ = 2π ξ`. -/
theorem integral_logTanhKernel_deriv_quadrant (g : SchwartzMap ℝ ℂ) (hg : ∀ x, g (-x) = g x) :
    2 * ∫ y in Ioi (0:ℝ), starRingEnd ℂ (deriv (g : ℝ → ℂ) y) *
        ∫ z in Ioi (0:ℝ), (((logTanhKernel (z - y) : ℝ) : ℂ) - ((logTanhKernel (z + y) : ℝ) : ℂ)) *
          deriv (g : ℝ → ℂ) z =
      ∫ ξ in Ioi (0:ℝ),
        (((2 * Real.pi * ξ) * Real.pi * Real.tanh (Real.pi * (2 * Real.pi * ξ)) : ℝ) : ℂ) *
        (2 * (starRingEnd ℂ (𝓕 (g : ℝ → ℂ) ξ) * 𝓕 (g : ℝ → ℂ) ξ)) := by
  set h := SchwartzMap.derivCLM ℂ ℂ g with hh
  have hcoe : (h : ℝ → ℂ) = deriv (g : ℝ → ℂ) :=
    funext fun x => SchwartzMap.derivCLM_apply ℂ g x
  have hodd : ∀ x, h (-x) = - h x := fun x => by
    simp only [hcoe]; exact deriv_odd_of_even hg x
  have key := integral_logTanhKernel_odd_quadrant h hodd
  simp only [hcoe] at key
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioi (fun ξ hξ => ?_)
  have hξ0 : (0:ℝ) < ξ := hξ
  have e := fourier_deriv_schwartz g ξ
  simp only [hh] at *
  rw [hcoe] at e
  simp only [e, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  have hne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hne2 : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ0.ne'
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]

end Lightlike.Lorentz.SL2RPlancherel
