import Mathlib
import Lightlike.Dirac.AngularModes
import Lightlike.Dirac.ModeClassify

/-!
# Completeness for `C¹` chart spinors with decay at the pole

A `C¹` pair `(g₁, g₂)` on the plane with `(1+|x|²) i (∂₀ g₁ + i ∂₁ g₁) = 2λ g₂`, `(1+|x|²) i (∂₀ g₂ − i ∂₁ g₂) = 2λ g₁`
and `|g_i(x)| ≤ C/|x|` for `|x| ≥ 1` is zero unless `λ = ±k` for an integer `k ≥ 1`.
-/

namespace Lightlike.Dirac

open Complex

/-- The Fourier coefficients are bounded by `2π` times the sup norm. -/
lemma fcoef_norm_le (G : ℝ → ℝ → ℂ) (m : ℤ) (r M : ℝ) (h : ∀ θ : ℝ, ‖G r θ‖ ≤ M) :
    ‖fcoef G m r‖ ≤ M * (2 * Real.pi) := by
  unfold fcoef
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (f := fun θ : ℝ => Complex.exp (-(m : ℂ) * θ * Complex.I) * G r θ) (C := M) (fun θ _ => by
      rw [norm_mul]
      have : ‖Complex.exp (-(m : ℂ) * θ * Complex.I)‖ = 1 := by
        have : -(m : ℂ) * θ * Complex.I = ((-(m : ℝ) * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rw [this, one_mul]; exact h θ)
  have h2 : |2 * Real.pi - 0| = 2 * Real.pi := by rw [sub_zero]; exact abs_of_pos (by positivity)
  rw [h2] at this
  exact this

/-- **The Fourier modes of a `C¹` eigenspinor solve the radial mode system.** -/
theorem fourier_modes_isModeSol {g₁ g₂ : E 2 → ℂ} (h₁ : ContDiff ℝ 1 g₁) (h₂ : ContDiff ℝ 1 g₂) (lam : ℂ)
    (hA : ∀ x : E 2, (1 + (‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I *
      (fderiv ℝ g₁ x (e (0 : Fin 2)) + Complex.I * fderiv ℝ g₁ x (e (1 : Fin 2))) = 2 * lam * g₂ x)
    (hB : ∀ x : E 2, (1 + (‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I *
      (fderiv ℝ g₂ x (e (0 : Fin 2)) - Complex.I * fderiv ℝ g₂ x (e (1 : Fin 2))) = 2 * lam * g₁ x)
    (m : ℤ) :
    IsModeSol (2 * lam / Complex.I) m (fun r => fcoef (polarFn g₁) m r) (fun r => fcoef (polarFn g₂) (m + 1) r) := by
  intro r hr
  obtain ⟨d1r, d1t, c1, c1r, c1t⟩ := polar_data h₁
  obtain ⟨d2r, d2t, c2, c2r, c2t⟩ := polar_data h₂
  have ha := hasDerivAt_fcoef m d1r c1 c1r r
  have hb := hasDerivAt_fcoef (m + 1) d2r c2 c2r r
  have e1 := mode_eq_bar h₁ h₂ lam hA m hr.ne'
  have e2 := mode_eq h₁ h₂ lam hB m hr.ne'
  have hK : (1 + (r : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + r ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  push_cast at e1 e2
  constructor
  · refine ha.congr_deriv ?_
    rw [← ha.deriv]
    push_cast
    have key : deriv (fcoef (polarFn g₁) m) r - (m : ℂ) / r * fcoef (polarFn g₁) m r =
        2 * lam * fcoef (polarFn g₂) (m + 1) r / (1 + (r : ℂ) ^ 2) / Complex.I := by
      rw [eq_div_iff hI, eq_div_iff hK]; linear_combination e1
    linear_combination key
  · refine hb.congr_deriv ?_
    rw [← hb.deriv]
    push_cast
    have key : deriv (fcoef (polarFn g₂) (m + 1)) r + ((m : ℂ) + 1) / r * fcoef (polarFn g₂) (m + 1) r =
        2 * lam * fcoef (polarFn g₁) m r / (1 + (r : ℂ) ^ 2) / Complex.I := by
      rw [eq_div_iff hI, eq_div_iff hK]; linear_combination e2
    linear_combination key

end Lightlike.Dirac
