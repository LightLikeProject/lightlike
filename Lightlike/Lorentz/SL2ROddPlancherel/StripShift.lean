import Mathlib

/-!
# Shifting a contour across a horizontal strip

If `f` is holomorphic on the closed strip `a ≤ Im z ≤ b` and decays like `C/(1 + x²)` there, uniformly in the
height, then the integrals of `f` along the two boundary lines agree (`integral_shift_strip`): the rectangle
`[-R, R] × [a, b]` has zero boundary integral (Mathlib's Cauchy-Goursat theorem for a rectangle,
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) and the vertical sides tend to `0` as `R → ∞`.
This is used to move the Fourier-side integrals of the odd Plancherel density `ρ coth(πρ)` onto the
real axis, where the even theorem applies.
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral

noncomputable section

namespace Lightlike.Lorentz.SL2ROddPlancherel

/-- **Contour shift across a horizontal strip**: if `f` is holomorphic on the closed strip
`a ≤ Im z ≤ b` and `‖f (x + yi)‖ ≤ C/(1 + x²)` there, then `∫ f(x + bi) dx = ∫ f(x + ai) dx`. -/
theorem integral_shift_strip {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hd : DifferentiableOn ℂ f {z : ℂ | a ≤ z.im ∧ z.im ≤ b}) {C : ℝ}
    (hbd : ∀ x y : ℝ, a ≤ y → y ≤ b → ‖f (x + y * I)‖ ≤ C / (1 + x ^ 2)) :
    ∫ x : ℝ, f (x + b * I) = ∫ x : ℝ, f (x + a * I) := by
  have hcont : ∀ y : ℝ, a ≤ y → y ≤ b → Continuous fun x : ℝ => f (x + y * I) := by
    intro y hy1 hy2
    have : ContinuousOn f {z : ℂ | a ≤ z.im ∧ z.im ≤ b} := hd.continuousOn
    refine this.comp_continuous (by fun_prop) fun x => ?_
    simp [hy1, hy2]
  have hint : ∀ y : ℝ, a ≤ y → y ≤ b → Integrable fun x : ℝ => f (x + y * I) := by
    intro y hy1 hy2
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C)
      (hcont y hy1 hy2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    have := hbd x y hy1 hy2
    simpa [div_eq_mul_inv] using this
  -- the rectangle identity for every R
  have hrect : ∀ R : ℝ, 0 ≤ R →
      (∫ x : ℝ in (-R)..R, f (x + a * I)) - (∫ x : ℝ in (-R)..R, f (x + b * I)) +
        I • (∫ y : ℝ in a..b, f (R + y * I)) - I • (∫ y : ℝ in a..b, f (-R + y * I)) = 0 := by
    intro R hR
    have H := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ((-R : ℝ) + a * I)
      ((R : ℝ) + b * I) (hd.mono ?_)
    · simpa using H
    · intro z hz
      rw [Complex.mem_reProdIm] at hz
      have hz2 := hz.2
      simp [uIcc_of_le hab] at hz2
      exact ⟨hz2.1, hz2.2⟩
  -- the vertical sides tend to 0
  have hvert : ∀ s : ℝ, s ^ 2 = 1 →
      Tendsto (fun R : ℝ => ∫ y : ℝ in a..b, f ((s * R : ℝ) + y * I)) atTop (𝓝 0) := by
    intro s hs
    have h1 : Tendsto (fun R : ℝ => C / (1 + R ^ 2) * |b - a|) atTop (𝓝 0) := by
      have : Tendsto (fun R : ℝ => 1 + R ^ 2) atTop atTop :=
        tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop (by norm_num))
      simpa using ((tendsto_const_nhds (x := C)).div_atTop this).mul_const |b - a|
    refine squeeze_zero_norm (fun R => ?_) h1
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
    have hy' : a ≤ y ∧ y ≤ b := by
      rw [uIoc_of_le hab] at hy; exact ⟨hy.1.le, hy.2⟩
    have := hbd (s * R) y hy'.1 hy'.2
    have e : (1 + (s * R) ^ 2) = 1 + R ^ 2 := by rw [mul_pow, hs, one_mul]
    rwa [e] at this
  have hA : Tendsto (fun R : ℝ => ∫ x : ℝ in (-R)..R, f (x + a * I)) atTop
      (𝓝 (∫ x : ℝ, f (x + a * I))) :=
    intervalIntegral_tendsto_integral (hint a le_rfl hab) tendsto_neg_atTop_atBot tendsto_id
  have hB : Tendsto (fun R : ℝ => ∫ x : ℝ in (-R)..R, f (x + b * I)) atTop
      (𝓝 (∫ x : ℝ, f (x + b * I))) :=
    intervalIntegral_tendsto_integral (hint b hab le_rfl) tendsto_neg_atTop_atBot tendsto_id
  have hV1 := hvert 1 (by norm_num)
  have hV2 := hvert (-1) (by norm_num)
  simp only [one_mul, neg_one_mul, Complex.ofReal_neg] at hV1 hV2
  have hlim : Tendsto (fun R : ℝ => (∫ x : ℝ in (-R)..R, f (x + a * I)) -
      (∫ x : ℝ in (-R)..R, f (x + b * I)) + I • (∫ y : ℝ in a..b, f (R + y * I)) -
      I • (∫ y : ℝ in a..b, f (-R + y * I))) atTop
      (𝓝 ((∫ x : ℝ, f (x + a * I)) - (∫ x : ℝ, f (x + b * I)) + I • (0 : ℂ) - I • (0 : ℂ))) :=
    ((hA.sub hB).add (hV1.const_smul I)).sub (hV2.const_smul I)
  have hz : Tendsto (fun R : ℝ => (∫ x : ℝ in (-R)..R, f (x + a * I)) -
      (∫ x : ℝ in (-R)..R, f (x + b * I)) + I • (∫ y : ℝ in a..b, f (R + y * I)) -
      I • (∫ y : ℝ in a..b, f (-R + y * I))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop (0 : ℝ)).mono fun R hR => (hrect R hR).symm)
  have := tendsto_nhds_unique hlim hz
  simp at this
  linear_combination -this

end Lightlike.Lorentz.SL2ROddPlancherel
