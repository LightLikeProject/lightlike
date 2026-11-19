import Lightlike.Asymptotics.Tauberian.Assembly
import Lightlike.Asymptotics.Tauberian.FourierBound

/-!
# The smoothed counting functions of two measures with close Laplace transforms

`smoothed_difference`: if `‖L₁(β + i t) - L₂(β + i t)‖ ≤ M` for `|t| ≤ 4b`, then
`|∫ ψ(Δ - x) dμ₁ - ∫ ψ(Δ - x) dμ₂| ≤ e^{βΔ} 16 b⁴ M / (N β)`.
-/

open MeasureTheory Set Real Filter Complex

noncomputable section

namespace Lightlike.Tauberian

/-- `‖1/(β + i t)‖ ≤ 1/β`. -/
lemma norm_inv_le {β : ℝ} (hβ : 0 < β) (t : ℝ) : ‖1 / ((β : ℂ) + t * Complex.I)‖ ≤ 1 / β := by
  have h1 : β ≤ ‖(β : ℂ) + t * Complex.I‖ := by
    have := Complex.abs_re_le_norm ((β : ℂ) + t * Complex.I)
    simpa [abs_of_pos hβ] using this
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le hβ h1

/-- `N ψ(Δ - x) = e^{β Δ} e^{-β x} Ψ(x - Δ)`. -/
lemma kapN_mul_psiS_comp {b β : ℝ} (hb : 0 < b) (Δ x : ℝ) :
    kapN b * psiS b β (Δ - x) = Real.exp (β * Δ) * (smoothΨ b β (x - Δ) * Real.exp (-β * x)) := by
  rw [kapN_mul_psiS hb]
  have : -(Δ - x) = x - Δ := by ring
  have e : Real.exp (β * (Δ - x)) = Real.exp (β * Δ) * Real.exp (-β * x) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this, e]; ring

/-- **The difference of two smoothed counting functions.** -/
theorem smoothed_difference (μ₁ μ₂ : Measure ℝ) [SFinite μ₁] [SFinite μ₂] {b β Δ M : ℝ} (hb : 0 < b)
    (hβ : 0 < β) (h1 : Integrable (fun x : ℝ => Real.exp (-β * x)) μ₁)
    (h2 : Integrable (fun x : ℝ => Real.exp (-β * x)) μ₂) {g : ℝ → ℝ} (hgi : Integrable g)
    (hg0 : ∀ t, 0 ≤ g t) (hgs : ∀ t, 4 * b < |t| → g t = 0)
    (hg : ∀ x : ℝ, ∫ t, (g t : ℂ) * char x t = (((2 * b * Real.sinc (b * x)) ^ 4 : ℝ) : ℂ))
    (hM : 0 ≤ M)
    (hD : ∀ t : ℝ, |t| ≤ 4 * b →
      ‖laplaceC μ₁ (β + t * Complex.I) - laplaceC μ₂ (β + t * Complex.I)‖ ≤ M) :
    |(∫ x, psiS b β (Δ - x) ∂μ₁) - ∫ x, psiS b β (Δ - x) ∂μ₂| ≤
      Real.exp (β * Δ) * (16 * b ^ 4 * M / β) / kapN b := by
  have hN := kapN_pos hb
  -- the two integrals through `Ψ`
  have hΨ : ∀ μ : Measure ℝ, ∫ x, psiS b β (Δ - x) ∂μ =
      Real.exp (β * Δ) / kapN b * ∫ x, smoothΨ b β (x - Δ) * Real.exp (-β * x) ∂μ := by
    intro μ
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have := kapN_mul_psiS_comp (β := β) hb Δ x
    have hN' := hN.ne'
    calc psiS b β (Δ - x) = (kapN b * psiS b β (Δ - x)) / kapN b := by field_simp
      _ = _ := by rw [this]; ring
  rw [hΨ μ₁, hΨ μ₂, ← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < Real.exp (β * Δ) / kapN b)]
  -- the complex representation of the difference
  have hGi := integrable_weight (Δ := Δ) hβ hgi
  have r1 := smooth_representation μ₁ hβ h1 hgi hg (Δ := Δ)
  have r2 := smooth_representation μ₂ hβ h2 hgi hg (Δ := Δ)
  have i1 := integrable_fourier_laplace μ₁ h1 hGi
  have i2 := integrable_fourier_laplace μ₂ h2 hGi
  have hdiff : (((∫ x, smoothΨ b β (x - Δ) * Real.exp (-β * x) ∂μ₁) -
      ∫ x, smoothΨ b β (x - Δ) * Real.exp (-β * x) ∂μ₂ : ℝ) : ℂ) =
      ∫ t, (g t : ℂ) * Complex.exp (t * Δ * Complex.I) *
        ((1 / (β + t * Complex.I)) * (laplaceC μ₁ (β + t * Complex.I) - laplaceC μ₂ (β + t * Complex.I))) := by
    push_cast
    rw [r1, r2, ← integral_sub i1 i2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    ring
  have hnorm : ‖∫ t, (g t : ℂ) * Complex.exp (t * Δ * Complex.I) *
        ((1 / (β + t * Complex.I)) * (laplaceC μ₁ (β + t * Complex.I) - laplaceC μ₂ (β + t * Complex.I)))‖ ≤
      (∫ t, g t) * (1 / β * M) := by
    refine norm_kernel_integral_le (Λ := 4 * b) hg0 hgs hgi
      (D := fun t => (1 / ((β : ℂ) + t * Complex.I)) *
        (laplaceC μ₁ (β + t * Complex.I) - laplaceC μ₂ (β + t * Complex.I))) (fun t ht => ?_)
      (by positivity) Δ
    rw [norm_mul]
    exact mul_le_mul (norm_inv_le hβ t) (hD t ht) (norm_nonneg _) (by positivity)
  have hint0 : ∫ t, g t = 16 * b ^ 4 := by
    have h0 := hg 0
    have e : ∀ t : ℝ, (g t : ℂ) * char 0 t = (g t : ℂ) := fun t => by simp [char]
    simp_rw [e] at h0
    rw [integral_complex_ofReal] at h0
    have h' := Complex.ofReal_injective h0
    rw [h']; simp [Real.sinc_zero]; ring
  rw [← hdiff, Complex.norm_real, Real.norm_eq_abs, hint0] at hnorm
  calc Real.exp (β * Δ) / kapN b * |(∫ x, smoothΨ b β (x - Δ) * Real.exp (-β * x) ∂μ₁) -
        ∫ x, smoothΨ b β (x - Δ) * Real.exp (-β * x) ∂μ₂|
      ≤ Real.exp (β * Δ) / kapN b * (16 * b ^ 4 * (1 / β * M)) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = Real.exp (β * Δ) * (16 * b ^ 4 * M / β) / kapN b := by field_simp

end Lightlike.Tauberian
