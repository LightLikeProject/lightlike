import Lightlike.Asymptotics.Tauberian.Inner

/-!
# Comparison of the step with its smoothing

`comparison_le`: for a measure `μ` with the local window bound and `e^{-β x}` integrable,
`|μ(-∞, Δ] - ∫ ψ(Δ - x) dμ| ≤ ∫ |ρ(Δ - x)| dμ ≤ (inner) + (outer)`.
-/

open MeasureTheory Set Real Filter

noncomputable section

namespace Lightlike.Tauberian

/-- `ψ(y) ≤ e^{β y}`. -/
lemma psiS_le_exp_self {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) (y : ℝ) :
    psiS b β y ≤ Real.exp (β * y) := by
  have hN := kapN_pos hb
  unfold psiS
  have h1 : ∫ u in Iio y, Real.exp (β * u) * kap b u ≤ ∫ u in Iio y, Real.exp (β * y) * kap b u :=
    setIntegral_mono_on (integrableOn_exp_kap hb hβ y) ((integrable_kap hb).integrableOn.const_mul _)
      measurableSet_Iio fun u hu => mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.2 (by have : u < y := hu; nlinarith)) (kap_nonneg b u)
  rw [integral_const_mul] at h1
  have h2 : ∫ u in Iio y, kap b u ≤ kapN b := setIntegral_le_integral (integrable_kap hb)
    (Filter.Eventually.of_forall fun u => kap_nonneg b u)
  calc 1 / kapN b * ∫ u in Iio y, Real.exp (β * u) * kap b u
      ≤ 1 / kapN b * (Real.exp (β * y) * ∫ u in Iio y, kap b u) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 1 / kapN b * (Real.exp (β * y) * kapN b) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) (by positivity)
    _ = Real.exp (β * y) := by field_simp

/-- `x ↦ ψ(Δ - x)` is `μ`-integrable when `e^{-β x}` is. -/
lemma integrable_psiS_comp (μ : Measure ℝ) {b β Δ : ℝ} (hb : 0 < b) (hβ : 0 ≤ β)
    (hint : Integrable (fun x : ℝ => Real.exp (-β * x)) μ) :
    Integrable (fun x : ℝ => psiS b β (Δ - x)) μ := by
  refine (hint.const_mul (Real.exp (β * Δ))).mono'
    (((psiS_mono hb hβ).measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_of_nonneg (psiS_nonneg hb _)]
  refine (psiS_le_exp_self hb hβ _).trans (le_of_eq ?_)
  rw [← Real.exp_add]; congr 1; ring

/-- The error is integrable on the outer region. -/
lemma integrableOn_outer (μ : Measure ℝ) {b β R Δ : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) (hR : 1 ≤ R)
    (hint : Integrable (fun x : ℝ => Real.exp (-β * x)) μ) :
    IntegrableOn (fun x : ℝ => |rhoErr b β (Δ - x)|) {x : ℝ | x ≤ Δ - R ∨ Δ + R < x} μ := by
  set S : Set ℝ := {x : ℝ | x ≤ Δ - R ∨ Δ + R < x}
  set K : ℝ := farC b * (β ^ 2 + β / R ^ 2 + 1 / R ^ 3) * Real.exp (β * Δ) with hK
  have hSm : MeasurableSet S := by
    simp only [S, Set.setOf_or]
    exact measurableSet_Iic.union measurableSet_Ioi
  have hmeas : Measurable fun x : ℝ => |rhoErr b β (Δ - x)| :=
    (continuous_abs.measurable.comp ((measurable_rhoErr hb hβ).comp (measurable_const.sub measurable_id)))
  refine ((hint.const_mul K).integrableOn).mono' hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun x hx => ?_)
  have hy : R ≤ Δ - x ∨ Δ - x < -R := by
    rcases hx with h | h
    · left; linarith
    · right; linarith
  have := rhoErr_far hb hβ hR hy
  rw [Real.norm_of_nonneg (abs_nonneg _)]
  refine this.trans (le_of_eq ?_)
  have : Real.exp (β * (Δ - x)) = Real.exp (β * Δ) * Real.exp (-β * x) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hK, this]; ring

/-- **Comparison of the step with its smoothing** (the two regions). -/
theorem comparison_le (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ] {b β a Δ K X₀ : ℝ} (hb : 0 < b)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (ha : 0 < a) (hΔ : 0 < Δ) (hβ : β = √(a / Δ)) (n : ℕ)
    (hn1 : 1 ≤ (n : ℝ)) (hn : (n : ℝ) ≤ Δ / 2) (hX : X₀ ≤ Δ / 2) (hK : 0 ≤ K)
    (hint : Integrable (fun x : ℝ => Real.exp (-β * x)) μ)
    (hW : ∀ c : ℝ, X₀ ≤ c →
      μ.real (Icc (c - 1 / 2) (c + 1 / 2)) ≤ K * c ^ (-(3 / 4 : ℝ)) * Real.exp (2 * √(a * c))) :
    |μ.real (Iic Δ) - ∫ x, psiS b β (Δ - x) ∂μ| ≤
      K * (Δ / 2) ^ (-(3 / 4 : ℝ)) * Real.exp (2 * √(a * Δ)) * Real.exp (β / 2) *
        (4 * ((1 + Real.exp β) * Real.exp β) + 2 * n * (farC b * β ^ 2) + 4 * (farC b * (β + 1))) +
      farC b * (β ^ 2 + β / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 3) * Real.exp (β * Δ) *
        ∫ x, Real.exp (-β * x) ∂μ := by
  have hψ := integrable_psiS_comp (Δ := Δ) μ hb hβ0 hint
  have hind : Integrable (fun x : ℝ => (Iic Δ).indicator (fun _ => (1 : ℝ)) x) μ := by
    refine (hint.const_mul (Real.exp (β * Δ))).mono'
      ((measurable_const.indicator measurableSet_Iic).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ Iic Δ
    · rw [Set.indicator_of_mem hx, norm_one, ← Real.exp_add]
      exact Real.one_le_exp (by have : x ≤ Δ := hx; nlinarith [mul_nonneg hβ0 (sub_nonneg.2 this)])
    · rw [Set.indicator_of_notMem hx]; simp; positivity
  have hρ : Integrable (fun x : ℝ => rhoErr b β (Δ - x)) μ := by
    refine (hind.sub hψ).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, rhoErr, Set.indicator, Set.mem_Iic]
    by_cases h : x ≤ Δ
    · rw [if_pos h, if_pos (by linarith)]
    · rw [if_neg h, if_neg (by linarith)]
  have hEq : μ.real (Iic Δ) - ∫ x, psiS b β (Δ - x) ∂μ = ∫ x, rhoErr b β (Δ - x) ∂μ := by
    have h1 : μ.real (Iic Δ) = ∫ x, (Iic Δ).indicator (fun _ => (1 : ℝ)) x ∂μ := by
      rw [integral_indicator_const _ measurableSet_Iic]; simp [Measure.real]
    rw [h1, ← integral_sub hind hψ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [rhoErr, Set.indicator, Set.mem_Iic]
    by_cases h : x ≤ Δ
    · rw [if_pos h, if_pos (by linarith)]
    · rw [if_neg h, if_neg (by linarith)]
  rw [hEq]
  refine (abs_integral_le_integral_abs).trans ?_
  have hS : {x : ℝ | x ≤ Δ - n ∨ Δ + n < x} = (Ioc (Δ - n) (Δ + n))ᶜ := by
    ext x; simp only [mem_setOf_eq, mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le]
  rw [← integral_add_compl measurableSet_Ioc hρ.abs]
  refine add_le_add ?_ ?_
  · exact inner_le μ hb hβ0 hβ1 ha hΔ hβ n hn hX hK hW
  · rw [← hS]; exact outer_le μ hb hβ0 hn1 hint

end Lightlike.Tauberian
