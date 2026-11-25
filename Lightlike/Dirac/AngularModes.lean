import Mathlib
import Lightlike.Dirac.AngularFourier
import Lightlike.Dirac.EigenAngular

/-!
# Mode equations for a smooth chart spinor

For `g : ℝ² → ℂ` of class `C¹` and the polar function `G r θ = g (r cos θ, r sin θ)`:
`∂_r G + (i/r) ∂_θ G = e^{-iθ} (∂₀ g + i ∂₁ g)` and `∂_r G − (i/r) ∂_θ G = e^{iθ} (∂₀ g − i ∂₁ g)`.
-/

namespace Lightlike.Dirac

open Complex

/-- The point with polar coordinates `(r, θ)`. -/
noncomputable def polarPt (r θ : ℝ) : E 2 := (r * Real.cos θ) • e (0 : Fin 2) + (r * Real.sin θ) • e (1 : Fin 2)

/-- `g` in polar coordinates. -/
noncomputable def polarFn (g : E 2 → ℂ) (r θ : ℝ) : ℂ := g (polarPt r θ)

/-- The polar point depends continuously on `(r, θ)`. -/
lemma polarPt_continuous : Continuous fun p : ℝ × ℝ => polarPt p.1 p.2 := by
  unfold polarPt; fun_prop

/-- The radial derivative of the polar function. -/
theorem hasDerivAt_polar_r {g : E 2 → ℂ} {g' : E 2 →L[ℝ] ℂ} (r θ : ℝ) (hg : HasFDerivAt g g' (polarPt r θ)) :
    HasDerivAt (fun r => polarFn g r θ) (g' (Real.cos θ • e (0 : Fin 2) + Real.sin θ • e (1 : Fin 2))) r := by
  have h1 : HasDerivAt (fun r : ℝ => polarPt r θ) (Real.cos θ • e (0 : Fin 2) + Real.sin θ • e (1 : Fin 2)) r := by
    unfold polarPt
    have a : HasDerivAt (fun r : ℝ => (r * Real.cos θ) • e (0 : Fin 2)) (Real.cos θ • e (0 : Fin 2)) r := by
      simpa using ((hasDerivAt_id r).mul_const (Real.cos θ)).smul_const (e (0 : Fin 2) : E 2)
    have b : HasDerivAt (fun r : ℝ => (r * Real.sin θ) • e (1 : Fin 2)) (Real.sin θ • e (1 : Fin 2)) r := by
      simpa using ((hasDerivAt_id r).mul_const (Real.sin θ)).smul_const (e (1 : Fin 2) : E 2)
    exact a.add b
  exact hg.comp_hasDerivAt r h1

/-- The angular derivative of the polar function. -/
theorem hasDerivAt_polar_theta {g : E 2 → ℂ} {g' : E 2 →L[ℝ] ℂ} (r θ : ℝ) (hg : HasFDerivAt g g' (polarPt r θ)) :
    HasDerivAt (fun θ => polarFn g r θ) (g' ((-(r * Real.sin θ)) • e (0 : Fin 2) + (r * Real.cos θ) • e (1 : Fin 2))) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => polarPt r θ) ((-(r * Real.sin θ)) • e (0 : Fin 2) + (r * Real.cos θ) • e (1 : Fin 2)) θ := by
    unfold polarPt
    have a : HasDerivAt (fun θ : ℝ => (r * Real.cos θ) • e (0 : Fin 2)) ((-(r * Real.sin θ)) • e (0 : Fin 2)) θ := by
      simpa using (((Real.hasDerivAt_cos θ).const_mul r)).smul_const (e (0 : Fin 2) : E 2)
    have b : HasDerivAt (fun θ : ℝ => (r * Real.sin θ) • e (1 : Fin 2)) ((r * Real.cos θ) • e (1 : Fin 2)) θ := by
      simpa using (((Real.hasDerivAt_sin θ).const_mul r)).smul_const (e (1 : Fin 2) : E 2)
    exact a.add b
  exact hg.comp_hasDerivAt θ h1

/-- `∂_r G + (i/r) ∂_θ G = e^{-iθ} (∂₀ g + i ∂₁ g)`. -/
theorem polar_wirtinger_bar (g' : E 2 →L[ℝ] ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    g' (Real.cos θ • e (0 : Fin 2) + Real.sin θ • e (1 : Fin 2)) +
      (Complex.I / r) * g' ((-(r * Real.sin θ)) • e (0 : Fin 2) + (r * Real.cos θ) • e (1 : Fin 2)) =
    Complex.exp (-(θ : ℂ) * Complex.I) * (g' (e (0 : Fin 2)) + Complex.I * g' (e (1 : Fin 2))) := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hexp : Complex.exp (-(θ : ℂ) * Complex.I) = (Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ) := by
    rw [show -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
    simp [Complex.ofReal_cos, Complex.ofReal_sin, Complex.cos_neg, Complex.sin_neg]
    ring
  simp only [map_add, map_smul, Complex.real_smul, hexp]
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- `∂_r G − (i/r) ∂_θ G = e^{iθ} (∂₀ g − i ∂₁ g)`. -/
theorem polar_wirtinger (g' : E 2 →L[ℝ] ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    g' (Real.cos θ • e (0 : Fin 2) + Real.sin θ • e (1 : Fin 2)) -
      (Complex.I / r) * g' ((-(r * Real.sin θ)) • e (0 : Fin 2) + (r * Real.cos θ) • e (1 : Fin 2)) =
    Complex.exp ((θ : ℂ) * Complex.I) * (g' (e (0 : Fin 2)) - Complex.I * g' (e (1 : Fin 2))) := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hexp : Complex.exp ((θ : ℂ) * Complex.I) = (Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ) := by
    rw [Complex.exp_mul_I]
    simp [Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  simp only [map_add, map_smul, Complex.real_smul, hexp]
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The radial derivative of `g` in polar coordinates, `∂_r G`. -/
noncomputable def polarDr (g : E 2 → ℂ) (r θ : ℝ) : ℂ :=
  fderiv ℝ g (polarPt r θ) (Real.cos θ • e (0 : Fin 2) + Real.sin θ • e (1 : Fin 2))

/-- The angular derivative of `g` in polar coordinates, `∂_θ G`. -/
noncomputable def polarDθ (g : E 2 → ℂ) (r θ : ℝ) : ℂ :=
  fderiv ℝ g (polarPt r θ) ((-(r * Real.sin θ)) • e (0 : Fin 2) + (r * Real.cos θ) • e (1 : Fin 2))

/-- The polar point is `2π`-periodic in the angle. -/
lemma polarPt_two_pi (r : ℝ) : polarPt r (2 * Real.pi) = polarPt r 0 := by
  simp [polarPt]

/-- The squared norm of the polar point is `r²`. -/
lemma polarPt_norm_sq (r θ : ℝ) : ‖polarPt r θ‖ ^ 2 = r ^ 2 := by
  have h0 : polarPt r θ 0 = r * Real.cos θ := by simp [polarPt, e]
  have h1 : polarPt r θ 1 = r * Real.sin θ := by simp [polarPt, e]
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, h0, h1]
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Regularity of the polar function of a `C¹` function. -/
theorem polar_data {g : E 2 → ℂ} (hg : ContDiff ℝ 1 g) :
    (∀ r θ, HasDerivAt (fun r => polarFn g r θ) (polarDr g r θ) r) ∧
    (∀ r θ, HasDerivAt (fun θ => polarFn g r θ) (polarDθ g r θ) θ) ∧
    (Continuous fun p : ℝ × ℝ => polarFn g p.1 p.2) ∧
    (Continuous fun p : ℝ × ℝ => polarDr g p.1 p.2) ∧
    (Continuous fun p : ℝ × ℝ => polarDθ g p.1 p.2) := by
  have hd : ∀ x, HasFDerivAt g (fderiv ℝ g x) x := fun x =>
    ((hg.differentiable (by norm_num)) x).hasFDerivAt
  have hcf : Continuous fun x => fderiv ℝ g x := hg.continuous_fderiv (by norm_num)
  have hP := polarPt_continuous
  refine ⟨fun r θ => hasDerivAt_polar_r r θ (hd _), fun r θ => hasDerivAt_polar_theta r θ (hd _),
    hg.continuous.comp hP, ?_, ?_⟩
  · unfold polarDr
    have : Continuous fun p : ℝ × ℝ => Real.cos p.2 • e (0 : Fin 2) + Real.sin p.2 • e (1 : Fin 2) := by fun_prop
    exact (hcf.comp hP).clm_apply this
  · unfold polarDθ
    have : Continuous fun p : ℝ × ℝ =>
        (-(p.1 * Real.sin p.2)) • e (0 : Fin 2) + (p.1 * Real.cos p.2) • e (1 : Fin 2) := by fun_prop
    exact (hcf.comp hP).clm_apply this

/-- **First mode equation.** If `(1+|x|²) i (∂₀ g₁ + i ∂₁ g₁) = 2 λ g₂` then the Fourier coefficients satisfy
`(1+r²) i (c₁_m' − (m/r) c₁_m) = 2 λ c₂_{m+1}`. -/
theorem mode_eq_bar {g₁ g₂ : E 2 → ℂ} (h₁ : ContDiff ℝ 1 g₁) (h₂ : ContDiff ℝ 1 g₂) (lam : ℂ)
    (hA : ∀ x : E 2, (1 + (‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I *
      (fderiv ℝ g₁ x (e (0 : Fin 2)) + Complex.I * fderiv ℝ g₁ x (e (1 : Fin 2))) = 2 * lam * g₂ x)
    (m : ℤ) {r : ℝ} (hr : r ≠ 0) :
    (1 + (r ^ 2 : ℝ) : ℂ) * Complex.I * (deriv (fcoef (polarFn g₁) m) r - (m / r) * fcoef (polarFn g₁) m r) =
      2 * lam * fcoef (polarFn g₂) (m + 1) r := by
  obtain ⟨d1r, d1t, c1, c1r, c1t⟩ := polar_data h₁
  have hder : deriv (fcoef (polarFn g₁) m) r = fcoef (polarDr g₁) m r :=
    (hasDerivAt_fcoef m d1r c1 c1r r).deriv
  have hθc : Continuous fun θ : ℝ => polarDθ g₁ r θ := c1t.comp (continuous_const.prodMk continuous_id)
  have hrc : Continuous fun θ : ℝ => polarDr g₁ r θ := c1r.comp (continuous_const.prodMk continuous_id)
  have hth := fcoef_dtheta m (fun θ => d1t r θ) (by simp [polarFn, polarPt_two_pi]) hθc
  -- the pointwise equation
  have hpt : ∀ θ : ℝ, Complex.exp (-(m : ℂ) * θ * Complex.I) *
      (polarDr g₁ r θ + (Complex.I / r) * polarDθ g₁ r θ) * ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) =
      2 * lam * (Complex.exp (-((m + 1 : ℤ) : ℂ) * θ * Complex.I) * polarFn g₂ r θ) := by
    intro θ
    have h := hA (polarPt r θ)
    rw [polarPt_norm_sq] at h
    have hw := polar_wirtinger_bar (fderiv ℝ g₁ (polarPt r θ)) hr θ
    have hw' : fderiv ℝ g₁ (polarPt r θ) (e (0 : Fin 2)) + Complex.I * fderiv ℝ g₁ (polarPt r θ) (e (1 : Fin 2)) =
        Complex.exp ((θ : ℂ) * Complex.I) * (polarDr g₁ r θ + (Complex.I / r) * polarDθ g₁ r θ) := by
      have hne : Complex.exp (-(θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
      have hmul : Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-(θ : ℂ) * Complex.I) = 1 := by
        rw [← Complex.exp_add]; simp
      unfold polarDr polarDθ
      rw [hw, ← mul_assoc, hmul, one_mul]
    rw [hw'] at h
    have hE : Complex.exp (-(m : ℂ) * θ * Complex.I) = Complex.exp (-((m + 1 : ℤ) : ℂ) * θ * Complex.I) *
        Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    calc _ = Complex.exp (-((m + 1 : ℤ) : ℂ) * θ * Complex.I) * ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I *
          (Complex.exp ((θ : ℂ) * Complex.I) * (polarDr g₁ r θ + (Complex.I / r) * polarDθ g₁ r θ))) := by
          rw [hE]; ring
      _ = _ := by rw [h]; unfold polarFn; ring
  have hE0 : Continuous fun θ : ℝ => Complex.exp (-(m : ℂ) * θ * Complex.I) := by fun_prop
  have hint := congrArg (fun f : ℝ → ℂ => ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ) (funext hpt)
  have lhs : ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(m : ℂ) * θ * Complex.I) *
        (polarDr g₁ r θ + (Complex.I / r) * polarDθ g₁ r θ) * ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) =
      ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) * (fcoef (polarDr g₁) m r +
        (Complex.I / r) * ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(m : ℂ) * θ * Complex.I) * polarDθ g₁ r θ) := by
    have e1 : ∀ θ : ℝ, Complex.exp (-(m : ℂ) * θ * Complex.I) *
        (polarDr g₁ r θ + (Complex.I / r) * polarDθ g₁ r θ) * ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) =
        ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) * (Complex.exp (-(m : ℂ) * θ * Complex.I) * polarDr g₁ r θ) +
        ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) * (Complex.I / r) *
          (Complex.exp (-(m : ℂ) * θ * Complex.I) * polarDθ g₁ r θ) := fun θ => by ring
    simp only [e1]
    have i1 : IntervalIntegrable (fun θ : ℝ => ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (-(m : ℂ) * θ * Complex.I) * polarDr g₁ r θ)) MeasureTheory.volume 0 (2 * Real.pi) :=
      (continuous_const.mul (hE0.mul hrc)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun θ : ℝ => ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) * (Complex.I / r) *
        (Complex.exp (-(m : ℂ) * θ * Complex.I) * polarDθ g₁ r θ)) MeasureTheory.volume 0 (2 * Real.pi) :=
      (continuous_const.mul (hE0.mul hθc)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    unfold fcoef
    ring
  have rhs : ∫ θ in (0 : ℝ)..(2 * Real.pi), 2 * lam *
        (Complex.exp (-((m + 1 : ℤ) : ℂ) * θ * Complex.I) * polarFn g₂ r θ) =
      2 * lam * fcoef (polarFn g₂) (m + 1) r := by
    rw [intervalIntegral.integral_const_mul]; rfl
  rw [lhs, rhs, hth] at hint
  rw [hder]
  have : (1 + (r ^ 2 : ℝ) : ℂ) * Complex.I * (fcoef (polarDr g₁) m r - (m / r) * fcoef (polarFn g₁) m r) =
      ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) * (fcoef (polarDr g₁) m r +
        (Complex.I / r) * ((m : ℂ) * Complex.I * ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(m : ℂ) * θ * Complex.I) * polarFn g₁ r θ)) := by
    unfold fcoef
    have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [this]; exact hint

/-- **Second mode equation.** If `(1+|x|²) i (∂₀ g₂ − i ∂₁ g₂) = 2 λ g₁` then
`(1+r²) i (c₂_{m+1}' + ((m+1)/r) c₂_{m+1}) = 2 λ c₁_m`. -/
theorem mode_eq {g₁ g₂ : E 2 → ℂ} (h₁ : ContDiff ℝ 1 g₁) (h₂ : ContDiff ℝ 1 g₂) (lam : ℂ)
    (hB : ∀ x : E 2, (1 + (‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I *
      (fderiv ℝ g₂ x (e (0 : Fin 2)) - Complex.I * fderiv ℝ g₂ x (e (1 : Fin 2))) = 2 * lam * g₁ x)
    (m : ℤ) {r : ℝ} (hr : r ≠ 0) :
    (1 + (r ^ 2 : ℝ) : ℂ) * Complex.I * (deriv (fcoef (polarFn g₂) (m + 1)) r +
        (((m + 1 : ℤ) : ℂ) / r) * fcoef (polarFn g₂) (m + 1) r) = 2 * lam * fcoef (polarFn g₁) m r := by
  obtain ⟨d2r, d2t, c2, c2r, c2t⟩ := polar_data h₂
  have hder : deriv (fcoef (polarFn g₂) (m + 1)) r = fcoef (polarDr g₂) (m + 1) r :=
    (hasDerivAt_fcoef (m + 1) d2r c2 c2r r).deriv
  have hθc : Continuous fun θ : ℝ => polarDθ g₂ r θ := c2t.comp (continuous_const.prodMk continuous_id)
  have hrc : Continuous fun θ : ℝ => polarDr g₂ r θ := c2r.comp (continuous_const.prodMk continuous_id)
  have hth := fcoef_dtheta (m + 1) (fun θ => d2t r θ) (by simp [polarFn, polarPt_two_pi]) hθc
  have hpt : ∀ θ : ℝ, Complex.exp (-((m + 1 : ℤ) : ℂ) * θ * Complex.I) *
      (polarDr g₂ r θ - (Complex.I / r) * polarDθ g₂ r θ) * ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) =
      2 * lam * (Complex.exp (-(m : ℂ) * θ * Complex.I) * polarFn g₁ r θ) := by
    intro θ
    have h := hB (polarPt r θ)
    rw [polarPt_norm_sq] at h
    have hw := polar_wirtinger (fderiv ℝ g₂ (polarPt r θ)) hr θ
    have hw' : fderiv ℝ g₂ (polarPt r θ) (e (0 : Fin 2)) - Complex.I * fderiv ℝ g₂ (polarPt r θ) (e (1 : Fin 2)) =
        Complex.exp (-(θ : ℂ) * Complex.I) * (polarDr g₂ r θ - (Complex.I / r) * polarDθ g₂ r θ) := by
      have hmul : Complex.exp (-(θ : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
        rw [← Complex.exp_add]; simp
      unfold polarDr polarDθ
      rw [hw, ← mul_assoc, hmul, one_mul]
    rw [hw'] at h
    have hE : Complex.exp (-((m + 1 : ℤ) : ℂ) * θ * Complex.I) = Complex.exp (-(m : ℂ) * θ * Complex.I) *
        Complex.exp (-(θ : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    calc _ = Complex.exp (-(m : ℂ) * θ * Complex.I) * ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I *
          (Complex.exp (-(θ : ℂ) * Complex.I) * (polarDr g₂ r θ - (Complex.I / r) * polarDθ g₂ r θ))) := by
          rw [hE]; ring
      _ = _ := by rw [h]; unfold polarFn; ring
  have hE0 : Continuous fun θ : ℝ => Complex.exp (-((m + 1 : ℤ) : ℂ) * θ * Complex.I) := by fun_prop
  have hint := congrArg (fun f : ℝ → ℂ => ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ) (funext hpt)
  have lhs : ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-((m + 1 : ℤ) : ℂ) * θ * Complex.I) *
        (polarDr g₂ r θ - (Complex.I / r) * polarDθ g₂ r θ) * ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) =
      ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) * (fcoef (polarDr g₂) (m + 1) r -
        (Complex.I / r) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-((m + 1 : ℤ) : ℂ) * θ * Complex.I) * polarDθ g₂ r θ) := by
    have e1 : ∀ θ : ℝ, Complex.exp (-((m + 1 : ℤ) : ℂ) * θ * Complex.I) *
        (polarDr g₂ r θ - (Complex.I / r) * polarDθ g₂ r θ) * ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) =
        ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) * (Complex.exp (-((m + 1 : ℤ) : ℂ) * θ * Complex.I) * polarDr g₂ r θ) -
        ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) * (Complex.I / r) *
          (Complex.exp (-((m + 1 : ℤ) : ℂ) * θ * Complex.I) * polarDθ g₂ r θ) := fun θ => by ring
    simp only [e1]
    have i1 : IntervalIntegrable (fun θ : ℝ => ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (-((m + 1 : ℤ) : ℂ) * θ * Complex.I) * polarDr g₂ r θ)) MeasureTheory.volume 0 (2 * Real.pi) :=
      (continuous_const.mul (hE0.mul hrc)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun θ : ℝ => ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) * (Complex.I / r) *
        (Complex.exp (-((m + 1 : ℤ) : ℂ) * θ * Complex.I) * polarDθ g₂ r θ)) MeasureTheory.volume 0 (2 * Real.pi) :=
      (continuous_const.mul (hE0.mul hθc)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    unfold fcoef
    ring
  have rhs : ∫ θ in (0 : ℝ)..(2 * Real.pi), 2 * lam *
        (Complex.exp (-(m : ℂ) * θ * Complex.I) * polarFn g₁ r θ) = 2 * lam * fcoef (polarFn g₁) m r := by
    rw [intervalIntegral.integral_const_mul]; rfl
  rw [lhs, rhs, hth] at hint
  rw [hder]
  have : (1 + (r ^ 2 : ℝ) : ℂ) * Complex.I * (fcoef (polarDr g₂) (m + 1) r +
        (((m + 1 : ℤ) : ℂ) / r) * fcoef (polarFn g₂) (m + 1) r) =
      ((1 + (r ^ 2 : ℝ) : ℂ) * Complex.I) * (fcoef (polarDr g₂) (m + 1) r -
        (Complex.I / r) * (((m + 1 : ℤ) : ℂ) * Complex.I * ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-((m + 1 : ℤ) : ℂ) * θ * Complex.I) * polarFn g₂ r θ)) := by
    unfold fcoef
    have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [this]; exact hint

end Lightlike.Dirac
