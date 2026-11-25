module

public import Mathlib

/-!
# The Cayley transform and integrals over the upper half-plane and the unit disc

The inverse Cayley transform `w ↦ i(1 + w)/(1 - w)` maps the unit disc bijectively onto the upper half-plane, with
Jacobian `4/|1 - w|⁴`; for `g : ℂ → [0, ∞]`,
`∫_{Im z > 0} g(z) dA(z) = ∫_{|w| < 1} g(i(1+w)/(1-w)) · 4/|1-w|⁴ dA(w)`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The inverse Cayley transform from the unit disc to the upper half-plane. -/
def cayleyInv (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)

/-- On the unit disc `1 - w ≠ 0`. -/
lemma one_sub_ne_zero {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : 1 - w ≠ 0 := by
  intro h
  have : w = 1 := by linear_combination -h
  rw [mem_ball_zero_iff, this] at hw
  simp at hw

/-- The imaginary part of the Cayley transform. -/
lemma im_cayleyInv {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    (cayleyInv w).im = (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
  have h := one_sub_ne_zero hw
  unfold cayleyInv
  rw [Complex.div_im]
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, zero_mul, one_mul, zero_add, sub_zero, Complex.sub_re, Complex.sub_im,
    zero_sub, mul_zero, add_zero, Complex.normSq_apply]
  have hn : (1 - w.re) * (1 - w.re) + w.im * w.im ≠ 0 := by
    have := Complex.normSq_pos.2 h
    simpa [Complex.normSq_apply] using this.ne'
  field_simp
  ring

/-- The Cayley transform maps the disc into the upper half-plane. -/
lemma cayleyInv_mem {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : (cayleyInv w).im > 0 := by
  rw [im_cayleyInv hw]
  have h1 : Complex.normSq w < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have : ‖w‖ < 1 := by simpa using hw
    nlinarith [norm_nonneg w]
  exact div_pos (by linarith) (Complex.normSq_pos.2 (one_sub_ne_zero hw))

/-- The Cayley transform is injective on the disc. -/
lemma cayleyInv_injOn : InjOn cayleyInv (ball (0 : ℂ) 1) := by
  intro w₁ h₁ w₂ h₂ h
  have e₁ := one_sub_ne_zero h₁
  have e₂ := one_sub_ne_zero h₂
  unfold cayleyInv at h
  rw [div_eq_div_iff e₁ e₂] at h
  have : Complex.I * (2 * (w₁ - w₂)) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 Complex.I_ne_zero
  · have : w₁ - w₂ = 0 := by
      rcases mul_eq_zero.1 h0 with h2 | h2
      · norm_num at h2
      · exact h2
    exact sub_eq_zero.1 this

/-- The Cayley transform maps the disc onto the upper half-plane. -/
lemma image_cayleyInv : cayleyInv '' ball (0 : ℂ) 1 = {z : ℂ | 0 < z.im} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact cayleyInv_mem hw
  · intro hz
    have hz' : (0 : ℝ) < z.im := hz
    have hne : z + Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    refine ⟨(z - Complex.I) / (z + Complex.I), ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.2 hne)]
      have h1 : ‖z - Complex.I‖ ^ 2 < ‖z + Complex.I‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
        nlinarith
      nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I)]
    · unfold cayleyInv
      have h1 : (1 : ℂ) - (z - Complex.I) / (z + Complex.I) = 2 * Complex.I / (z + Complex.I) := by
        field_simp; ring
      have h2 : (1 : ℂ) + (z - Complex.I) / (z + Complex.I) = 2 * z / (z + Complex.I) := by
        field_simp; ring
      rw [h1, h2]
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      field_simp

/-- The derivative of the Cayley transform. -/
lemma hasDerivAt_cayleyInv {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    HasDerivAt cayleyInv (2 * Complex.I / (1 - w) ^ 2) w := by
  have h := one_sub_ne_zero hw
  have hnum : HasDerivAt (fun w : ℂ => Complex.I * (1 + w)) Complex.I w := by
    simpa using ((hasDerivAt_id w).const_add 1).const_mul Complex.I
  have hden : HasDerivAt (fun w : ℂ => 1 - w) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have := hnum.div hden h
  show HasDerivAt (fun w : ℂ => Complex.I * (1 + w) / (1 - w)) _ w
  refine HasDerivAt.congr_deriv this ?_
  field_simp
  ring

/-- The Jacobian determinant of the Cayley transform. -/
lemma abs_det_cayleyInv {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    |(((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ)).det| =
      4 / ‖1 - w‖ ^ 4 := by
  have h := one_sub_ne_zero hw
  have hdet : LinearMap.det ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ :
      ℂ →ₗ[ℝ] ℂ) = Complex.normSq (2 * Complex.I / (1 - w) ^ 2) := by
    have h1 : ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ :
        ℂ →ₗ[ℝ] ℂ) = (LinearMap.mulLeft ℂ (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ := by
      ext x; simp [mul_comm]
    rw [h1, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
    have h2 : LinearMap.det (LinearMap.mulLeft ℂ (2 * Complex.I / (1 - w) ^ 2)) = 2 * Complex.I / (1 - w) ^ 2 := by
      have : LinearMap.mulLeft ℂ (2 * Complex.I / (1 - w) ^ 2) = (2 * Complex.I / (1 - w) ^ 2) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ) := by
        ext x; simp [mul_comm]
      rw [this, LinearMap.det_smul]; simp
    rw [h2]; rfl
  have hdet' : (ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      (2 * Complex.I / (1 - w) ^ 2))).det = Complex.normSq (2 * Complex.I / (1 - w) ^ 2) := hdet
  rw [hdet', abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, norm_div, norm_pow, norm_mul]
  simp
  have : ‖1 - w‖ ≠ 0 := norm_ne_zero_iff.2 h
  field_simp
  ring

/-- **Change of variables from the unit disc to the upper half-plane** (Bochner form):
`∫_{Im z > 0} g = ∫_{|w| < 1} (4/|1 - w|⁴) • g(i(1+w)/(1-w))`. -/
theorem integral_upperHalf_eq_disc (g : ℂ → ℂ) :
    ∫ z in {z : ℂ | 0 < z.im}, g z =
      ∫ w in ball (0 : ℂ) 1, (4 / ‖1 - w‖ ^ 4 : ℝ) • g (cayleyInv w) := by
  rw [← image_cayleyInv]
  have hf' : ∀ w ∈ ball (0 : ℂ) 1, HasFDerivWithinAt cayleyInv
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ))
      (ball (0 : ℂ) 1) w :=
    fun w hw => ((hasDerivAt_cayleyInv hw).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_ball hf' cayleyInv_injOn]
  refine setIntegral_congr_fun measurableSet_ball fun w hw => ?_
  simp only [abs_det_cayleyInv hw]

/-- **Change of variables from the unit disc to the upper half-plane**:
`∫_{Im z > 0} g = ∫_{|w| < 1} 4/|1 - w|⁴ · g(i(1+w)/(1-w))`. -/
theorem lintegral_upperHalf_eq_disc (g : ℂ → ENNReal) :
    ∫⁻ z in {z : ℂ | 0 < z.im}, g z =
      ∫⁻ w in ball (0 : ℂ) 1, ENNReal.ofReal (4 / ‖1 - w‖ ^ 4) * g (cayleyInv w) := by
  rw [← image_cayleyInv]
  have hf' : ∀ w ∈ ball (0 : ℂ) 1, HasFDerivWithinAt cayleyInv
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ))
      (ball (0 : ℂ) 1) w :=
    fun w hw => ((hasDerivAt_cayleyInv hw).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball hf' cayleyInv_injOn]
  refine setLIntegral_congr_fun measurableSet_ball fun w hw => ?_
  rw [abs_det_cayleyInv hw]
end Lightlike.Lorentz.SL2RPlancherel
