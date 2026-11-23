import Mathlib

/-!
# The Laplace transform of the sine

`∫_0^∞ sin (ρ t) e^{-a t} dt = ρ/(ρ² + a²)` for `a > 0`, the building block of the sine transform
`∫_0^∞ sin (ρ t)/sinh t dt = (π/2) tanh (πρ/2)` (with `1/sinh t = 2 ∑ e^{-(2m+1)t}`).
-/

namespace Lightlike.Lorentz.SL2RPlancherel

open MeasureTheory Set

private lemma re_neg_lt (a : ℝ) (ha : 0 < a) (ρ : ℝ) :
    (-(a : ℂ) + ρ * Complex.I).re < 0 := by simp [ha]

/-- `∫_0^∞ e^{(-a + iρ) t} dt = 1/(a - iρ)`. -/
private lemma integral_cexp (a : ℝ) (ha : 0 < a) (ρ : ℝ) :
    ∫ t : ℝ in Ioi 0, Complex.exp ((-(a : ℂ) + ρ * Complex.I) * t) = 1 / (a - ρ * Complex.I) := by
  rw [integral_exp_mul_complex_Ioi (re_neg_lt a ha ρ)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have : (a : ℂ) - ρ * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2 : -(a : ℂ) + ρ * Complex.I ≠ 0 := by
    intro h
    apply this
    linear_combination -h
  rw [div_eq_div_iff h2 this]
  ring

/-- Laplace transform of the sine: `∫_{t>0} sin (ρ t) e^{-a t} = ρ/(ρ² + a²)` for `a > 0`. -/
theorem integral_sin_mul_exp (a : ℝ) (ha : 0 < a) (ρ : ℝ) :
    ∫ t : ℝ in Ioi 0, Real.sin (ρ * t) * Real.exp (-(a * t)) = ρ / (ρ ^ 2 + a ^ 2) := by
  have hint : IntegrableOn (fun t : ℝ => Complex.exp ((-(a : ℂ) + ρ * Complex.I) * t)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (re_neg_lt a ha ρ) 0
  have hfun : ∀ t : ℝ, (Complex.exp ((-(a : ℂ) + ρ * Complex.I) * t)).im
      = Real.sin (ρ * t) * Real.exp (-(a * t)) := by
    intro t
    have : (-(a : ℂ) + ρ * Complex.I) * t = ((-(a * t) : ℝ) : ℂ) + ((ρ * t : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_add, ← Complex.ofReal_exp, Complex.im_ofReal_mul,
      Complex.exp_ofReal_mul_I_im, mul_comm]
  have h : ∫ t : ℝ in Ioi 0, (Complex.exp ((-(a : ℂ) + ρ * Complex.I) * t)).im
      = (∫ t : ℝ in Ioi 0, Complex.exp ((-(a : ℂ) + ρ * Complex.I) * t)).im := integral_im hint
  have h2 : ∫ t : ℝ in Ioi 0, Real.sin (ρ * t) * Real.exp (-(a * t))
      = ∫ t : ℝ in Ioi 0, (Complex.exp ((-(a : ℂ) + ρ * Complex.I) * t)).im := by
    congr 1; funext t; exact (hfun t).symm
  rw [h2, h, integral_cexp a ha ρ]
  have : (1 : ℂ) / (a - ρ * Complex.I) = ((a : ℂ) + ρ * Complex.I) / ((ρ ^ 2 + a ^ 2 : ℝ) : ℂ) := by
    have hpos : ((ρ ^ 2 + a ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : (0:ℝ) < ρ ^ 2 + a ^ 2 := by positivity
      exact_mod_cast this.ne'
    have hne : (a : ℂ) - ρ * Complex.I ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    rw [div_eq_div_iff hne hpos]
    push_cast
    linear_combination ((ρ : ℂ) ^ 2) * Complex.I_sq
  rw [this, Complex.div_ofReal_im]
  simp

end Lightlike.Lorentz.SL2RPlancherel
