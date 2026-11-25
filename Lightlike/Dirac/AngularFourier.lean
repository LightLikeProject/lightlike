import Mathlib

/-!
# Angular Fourier coefficients of a function of polar coordinates

For `G : ℝ → ℝ → ℂ` (radius, angle), `fcoef G m r = (2π)⁻¹ ∫₀^{2π} e^{-imθ} G r θ dθ`.  Two facts are needed to
reduce the Dirac equation on the sphere to radial ODEs, mode by mode: the coefficient of the angular derivative of a
periodic function is `i m` times the coefficient, and the radial derivative commutes with taking coefficients.
-/

namespace Lightlike.Dirac

open Complex MeasureTheory intervalIntegral Set

/-- The `m`-th angular Fourier coefficient of `G r ·` (without the factor `(2π)⁻¹`). -/
noncomputable def fcoef (G : ℝ → ℝ → ℂ) (m : ℤ) (r : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(m : ℂ) * θ * Complex.I) * G r θ

/-- The coefficient of the angular derivative of a periodic function is `i m` times the coefficient. -/
theorem fcoef_dtheta {g g' : ℝ → ℂ} (m : ℤ) (hg : ∀ θ, HasDerivAt g (g' θ) θ)
    (hper : g (2 * Real.pi) = g 0) (hg' : Continuous g') :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(m : ℂ) * θ * Complex.I) * g' θ =
      (m : ℂ) * Complex.I * ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(m : ℂ) * θ * Complex.I) * g θ := by
  have hu : ∀ x ∈ uIcc (0 : ℝ) (2 * Real.pi), HasDerivAt (fun θ : ℝ => Complex.exp (-(m : ℂ) * θ * Complex.I))
      (-(m : ℂ) * Complex.I * Complex.exp (-(m : ℂ) * x * Complex.I)) x := by
    intro x _
    have h1 : HasDerivAt (fun θ : ℝ => -(m : ℂ) * (θ : ℂ) * Complex.I) (-(m : ℂ) * Complex.I) x := by
      have := ((hasDerivAt_id (x : ℝ)).ofReal_comp).const_mul (-(m : ℂ))
      have := this.mul_const Complex.I
      simpa using this
    have := h1.cexp
    simpa [mul_comm] using this
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have key := integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * Real.pi) hu (fun x _ => hg x)
    (by
      refine Continuous.intervalIntegrable ?_ _ _
      fun_prop)
    (hg'.intervalIntegrable _ _)
  have hb : Complex.exp (-(m : ℂ) * ((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show -(m : ℂ) * ((2 * Real.pi : ℝ) : ℂ) * Complex.I = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [key]
  simp only [hb, one_mul, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, hper]
  rw [sub_self, zero_sub, ← intervalIntegral.integral_neg]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  ring

/-- **The radial derivative commutes with taking coefficients.** -/
theorem hasDerivAt_fcoef {G G' : ℝ → ℝ → ℂ} (m : ℤ)
    (hG : ∀ r θ, HasDerivAt (fun r => G r θ) (G' r θ) r)
    (hGc : Continuous fun p : ℝ × ℝ => G p.1 p.2) (hG'c : Continuous fun p : ℝ × ℝ => G' p.1 p.2) (r0 : ℝ) :
    HasDerivAt (fcoef G m) (fcoef G' m r0) r0 := by
  have hK : IsCompact (Metric.closedBall r0 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi)) :=
    (isCompact_closedBall r0 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hG'c.continuousOn (s := _))
  have hE : Continuous fun θ : ℝ => Complex.exp (-(m : ℂ) * θ * Complex.I) := by fun_prop
  have hθ : ∀ r : ℝ, Continuous fun θ : ℝ => ((r, θ) : ℝ × ℝ) := fun r => continuous_const.prodMk continuous_id
  have hEn : ∀ θ : ℝ, ‖Complex.exp (-(m : ℂ) * θ * Complex.I)‖ = 1 := by
    intro θ
    have : -(m : ℂ) * θ * Complex.I = ((-(m : ℝ) * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := 0)
    (b := 2 * Real.pi) (F := fun r θ => Complex.exp (-(m : ℂ) * θ * Complex.I) * G r θ)
    (F' := fun r θ => Complex.exp (-(m : ℂ) * θ * Complex.I) * G' r θ) (x₀ := r0) (s := Metric.closedBall r0 1)
    (bound := fun _ => C) (Metric.closedBall_mem_nhds r0 one_pos)
    (Filter.Eventually.of_forall fun r => ((hE.mul (hGc.comp (hθ r))).aestronglyMeasurable))
    ((hE.mul (hGc.comp (hθ r0))).intervalIntegrable _ _)
    ((hE.mul (hG'c.comp (hθ r0))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ht r hr => by
      rw [norm_mul, hEn, one_mul]
      exact hC (r, t) ⟨hr, by
        rw [Set.uIoc_of_le (by positivity)] at ht
        exact ⟨ht.1.le, ht.2⟩⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ r _ => (hG r t).const_mul _)
  exact this.2

end Lightlike.Dirac
