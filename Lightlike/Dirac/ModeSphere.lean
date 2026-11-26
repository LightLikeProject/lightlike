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

/-- **Completeness for `C¹` chart eigenspinors with decay at the pole.** A `C¹` solution `(g₁, g₂)` of the chart
eigen equations with `|g_i(x)| ≤ C/|x|` for `|x| ≥ 1` is zero unless `λ = ±k` for an integer `k ≥ 1`. -/
theorem chart_eigenspinor_quantized {g₁ g₂ : E 2 → ℂ} (h₁ : ContDiff ℝ 1 g₁) (h₂ : ContDiff ℝ 1 g₂) {lam : ℂ}
    (hlam : lam ≠ 0)
    (hA : ∀ x : E 2, (1 + (‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I *
      (fderiv ℝ g₁ x (e (0 : Fin 2)) + Complex.I * fderiv ℝ g₁ x (e (1 : Fin 2))) = 2 * lam * g₂ x)
    (hB : ∀ x : E 2, (1 + (‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I *
      (fderiv ℝ g₂ x (e (0 : Fin 2)) - Complex.I * fderiv ℝ g₂ x (e (1 : Fin 2))) = 2 * lam * g₁ x)
    {C : ℝ} (hdec : ∀ x : E 2, 1 ≤ ‖x‖ → ‖g₁ x‖ ≤ C / ‖x‖ ∧ ‖g₂ x‖ ≤ C / ‖x‖)
    (hnz : ¬ (g₁ = 0 ∧ g₂ = 0)) :
    ∃ k : ℕ, 1 ≤ k ∧ (lam = k ∨ lam = -(k : ℂ)) := by
  by_contra hno
  push_neg at hno
  set ν : ℂ := 2 * lam / Complex.I with hν
  have hν0 : ν ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero hlam) Complex.I_ne_zero
  have hαlam : Complex.I * ν / 2 = lam := by
    rw [hν]; field_simp
  -- bounds
  obtain ⟨M₁, hM₁⟩ := (isCompact_closedBall (0 : E 2) 1).exists_bound_of_continuousOn h₁.continuous.continuousOn
  obtain ⟨M₂, hM₂⟩ := (isCompact_closedBall (0 : E 2) 1).exists_bound_of_continuousOn h₂.continuous.continuousOn
  -- every mode vanishes
  have key : ∀ m : ℤ, ∀ r : ℝ, 0 < r →
      fcoef (polarFn g₁) m r = 0 ∧ fcoef (polarFn g₂) (m + 1) r = 0 := by
    intro m
    have hsol := fourier_modes_isModeSol h₁ h₂ lam hA hB m
    by_contra hne
    push_neg at hne
    obtain ⟨r₀, hr₀, hr₀'⟩ := hne
    have hnz' : fcoef (polarFn g₁) m r₀ ≠ 0 ∨ fcoef (polarFn g₂) (m + 1) r₀ ≠ 0 := by
      by_contra hh; push_neg at hh; exact hr₀' hh.1 hh.2
    obtain ⟨k, hk, hkk⟩ := mode_decay_quantized_int hν0 m hsol hr₀ hnz'
      (C₀ := max (M₁ * (2 * Real.pi)) (M₂ * (2 * Real.pi)))
      (fun r hr hr1 => by
        have hn : ∀ θ : ℝ, ‖polarPt r θ‖ ≤ 1 := fun θ => by
          have := polarPt_norm_sq r θ
          nlinarith [norm_nonneg (polarPt r θ)]
        constructor
        · exact (fcoef_norm_le _ m r M₁ fun θ => hM₁ _ (by simpa using hn θ)).trans (le_max_left _ _)
        · exact (fcoef_norm_le _ (m + 1) r M₂ fun θ => hM₂ _ (by simpa using hn θ)).trans (le_max_right _ _))
      (C₁ := C * (2 * Real.pi))
      (fun r hr => by
        have hn : ∀ θ : ℝ, ‖polarPt r θ‖ = r := fun θ => by
          have := polarPt_norm_sq r θ
          have h0 : 0 ≤ ‖polarPt r θ‖ := norm_nonneg _
          nlinarith [sq_nonneg (‖polarPt r θ‖ - r), sq_nonneg (‖polarPt r θ‖ + r)]
        have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
        constructor
        · have := fcoef_norm_le (polarFn g₁) m r (C / r) fun θ => by
            have := (hdec (polarPt r θ) (by rw [hn θ]; exact hr)).1
            rwa [hn θ] at this
          calc _ ≤ C / r * (2 * Real.pi) := this
            _ = C * (2 * Real.pi) / r := by ring
        · have := fcoef_norm_le (polarFn g₂) (m + 1) r (C / r) fun θ => by
            have := (hdec (polarPt r θ) (by rw [hn θ]; exact hr)).2
            rwa [hn θ] at this
          calc _ ≤ C / r * (2 * Real.pi) := this
            _ = C * (2 * Real.pi) / r := by ring)
    rw [hαlam] at hkk
    rcases hkk with hk1 | hk2
    · exact (hno k hk).1 hk1
    · exact (hno k hk).2 hk2
  have z1 : g₁ = 0 := eq_zero_of_fcoef_polar_pos h₁.continuous fun m r hr => (key m r hr).1
  have z2 : g₂ = 0 := by
    refine eq_zero_of_fcoef_polar_pos h₂.continuous fun m r hr => ?_
    have := (key (m - 1) r hr).2
    simpa using this
  exact hnz ⟨z1, z2⟩

end Lightlike.Dirac
