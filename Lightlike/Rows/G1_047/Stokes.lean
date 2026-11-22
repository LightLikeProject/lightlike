import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Lightlike.Rows.G1_047.Field

/-!
# Green's theorem on a rectangle for `C¹` planar fields

Row G1-047 (CO24). With `d₁ d₂` the partial derivatives of `Field.lean`, for `C¹` functions
`F₁ F₂ : ℝ × ℝ → ℝ` the integral of the curl `∂₁F₂ - ∂₂F₁` over a rectangle equals the boundary
circulation. Used with `F = A` (flux) and `F = J` (current). Supporting lemmas; no catalogue entry.
-/

namespace Lightlike.Rows.G1_047

open MeasureTheory

/-- The partial derivatives of a `C¹` function are continuous. -/
theorem continuous_d₁ {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (d₁ f) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The partial derivatives of a `C¹` function are continuous. -/
theorem continuous_d₂ {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (d₂ f) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- **Green's theorem on a rectangle** for `C¹` functions `F₁ F₂`:
`∬ (∂₁F₂ - ∂₂F₁) = ∮ F · dℓ` (counterclockwise), written as four edge integrals. -/
theorem green_rect {F₁ F₂ : ℝ × ℝ → ℝ} (h₁ : ContDiff ℝ 1 F₁) (h₂ : ContDiff ℝ 1 F₂)
    (a₁ a₂ b₁ b₂ : ℝ) :
    (∫ x in a₁..b₁, ∫ y in a₂..b₂, (d₁ F₂ (x, y) - d₂ F₁ (x, y))) =
      ((∫ y in a₂..b₂, F₂ (b₁, y)) - ∫ y in a₂..b₂, F₂ (a₁, y)) -
        ((∫ x in a₁..b₁, F₁ (x, b₂)) - ∫ x in a₁..b₁, F₁ (x, a₂)) := by
  have hd1 : ∀ x, HasFDerivAt F₁ (fderiv ℝ F₁ x) x := fun x =>
    ((h₁.differentiable one_ne_zero) x).hasFDerivAt
  have hd2 : ∀ x, HasFDerivAt F₂ (fderiv ℝ F₂ x) x := fun x =>
    ((h₂.differentiable one_ne_zero) x).hasFDerivAt
  have key := integral2_divergence_prod_of_hasFDerivAt F₂ (fun x => -F₁ x)
    (fun x => fderiv ℝ F₂ x) (fun x => -fderiv ℝ F₁ x) a₁ a₂ b₁ b₂
    h₂.continuous.continuousOn (h₁.continuous.neg).continuousOn
    (fun x _ => hd2 x) (fun x _ => (hd1 x).neg)
    (by
      have : Continuous (fun x : ℝ × ℝ => d₁ F₂ x - d₂ F₁ x) :=
        (continuous_d₁ h₂).sub (continuous_d₂ h₁)
      exact (this.continuousOn).integrableOn_compact
        (isCompact_uIcc.prod isCompact_uIcc))
  have e1 : (∫ x in a₁..b₁, ∫ y in a₂..b₂, (d₁ F₂ (x, y) - d₂ F₁ (x, y))) =
      ∫ x in a₁..b₁, ∫ y in a₂..b₂,
        (fderiv ℝ F₂ (x, y) (1, 0) + (-fderiv ℝ F₁ (x, y)) (0, 1)) := by
    simp only [d₁, d₂, neg_apply, sub_eq_add_neg]
  rw [e1, key]
  simp only [intervalIntegral.integral_neg]
  ring

end Lightlike.Rows.G1_047
