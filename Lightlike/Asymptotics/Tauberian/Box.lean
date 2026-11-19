import Lightlike.Asymptotics.Tauberian.Majorant
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Fourier transform of a box

`∫_{-b}^{b} e^{-i t x} dt = 2 b sinc (b x)`: the first step in showing that `sinc⁴` is the Fourier
transform of a compactly supported nonnegative function (the four-fold convolution of a box).
-/

open MeasureTheory Set Complex

noncomputable section

namespace Lightlike.Tauberian

/-- The box `1_{[-b, b]}` as a complex function. -/
def box (b : ℝ) (t : ℝ) : ℂ := (Icc (-b) b).indicator (fun _ => (1 : ℂ)) t

lemma integral_box_exp {b : ℝ} (hb : 0 < b) (x : ℝ) :
    ∫ t, box b t * Complex.exp (-(t * x * Complex.I)) = 2 * b * (Real.sinc (b * x) : ℂ) := by
  have e1 : ∀ t : ℝ, box b t * Complex.exp (-(t * x * Complex.I)) =
      (Icc (-b) b).indicator (fun t : ℝ => Complex.exp (-(x * Complex.I) * t)) t := by
    intro t
    by_cases ht : t ∈ Icc (-b) b
    · simp only [box, Set.indicator_of_mem ht, one_mul]
      congr 1; ring
    · simp [box, Set.indicator_of_notMem ht]
  simp_rw [e1]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  by_cases hx : x = 0
  · subst hx; simp; ring
  · have hc : (-(x * Complex.I) : ℂ) ≠ 0 := by
      simp [hx, Complex.I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have hbx : b * x ≠ 0 := mul_ne_zero hb.ne' hx
    rw [Real.sinc_of_ne_zero hbx]
    have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    have e2 : Complex.exp (-(↑x * Complex.I) * ↑b) = Complex.exp (-(↑b * ↑x * Complex.I)) := by
      congr 1; ring
    have e3 : Complex.exp (-(↑x * Complex.I) * ↑(-b)) = Complex.exp (↑b * ↑x * Complex.I) := by
      congr 1; push_cast; ring
    rw [e2, e3]
    have h4 : Complex.exp (-(↑b * ↑x * Complex.I)) = Complex.cos (b * x) - Complex.sin (b * x) * Complex.I := by
      rw [show -(↑b * ↑x * Complex.I) = (-(↑b * ↑x) : ℂ) * Complex.I by ring, Complex.exp_mul_I,
        Complex.cos_neg, Complex.sin_neg]; ring
    have h5 : Complex.exp (↑b * ↑x * Complex.I) = Complex.cos (b * x) + Complex.sin (b * x) * Complex.I := by
      rw [Complex.exp_mul_I]
    rw [h4, h5]
    have hs : (Complex.sin (↑b * ↑x)) = ((Real.sin (b * x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sin]; push_cast; ring_nf
    rw [hs]
    have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    have hbx' : (b : ℂ) * (x : ℂ) ≠ 0 := by exact_mod_cast hbx
    have hone : (b : ℂ) * x * (b : ℂ)⁻¹ * (x : ℂ)⁻¹ = 1 := by field_simp
    field_simp
    push_cast
    linear_combination (-(Complex.sin (↑b * ↑x) * Complex.I * 2)) * hone

end Lightlike.Tauberian
