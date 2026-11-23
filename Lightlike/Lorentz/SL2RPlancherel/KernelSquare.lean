module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.AbelCompose

/-!
# The square of a half-order Abel integral as a triple integral

For a bounded measurable `φ : ℝ → ℂ` vanishing on `[R, ∞)`, put
`abelSlice φ v a = φ a / √(a - v)` (which is `0` for `a ≤ v`, as `√` of a nonpositive number is `0`
in Lean).  `integral_integral_abelSlice` is Fubini for the triple `(a, b, v)`:
`∫_a ∫_b ∫_{v > 1} φ a φ b / √((a - v)(b - v)) = ∫_{v > 1} (∫_a φ a / √(a - v))²`.
This is step (B) of the Plancherel route for `SL(2,ℝ)` (milestone HA3, density `ρ tanh(πρ)`):
the left side is the double integral of `g' ⊗ g'` against the kernel `∫_1^{min(a,b)} dv/√((a-v)(b-v))`
of `AbelKernel`, the right side is `π²‖F‖²` once `φ` is the half Abel integral of `F'`.
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The slice `a ↦ φ a / √(a - v)` (zero for `a ≤ v`). -/
def abelSlice (φ : ℝ → ℂ) (v a : ℝ) : ℂ := φ a * (((√(a - v))⁻¹ : ℝ) : ℂ)

variable {φ : ℝ → ℂ} {M R : ℝ}

lemma measurable_abelSlice (hφ : Measurable φ) : Measurable (Function.uncurry (abelSlice φ)) := by
  unfold abelSlice Function.uncurry
  fun_prop

lemma abelSlice_eq_zero (hR : ∀ a, R ≤ a → φ a = 0) {v a : ℝ} (h : a ∉ Ioo v R) :
    abelSlice φ v a = 0 := by
  unfold abelSlice
  by_cases h1 : v < a
  · have : R ≤ a := by
      by_contra hc
      exact h ⟨h1, not_le.1 hc⟩
    simp [hR a this]
  · have : a - v ≤ 0 := by linarith [not_lt.1 h1]
    simp [Real.sqrt_eq_zero_of_nonpos this]

lemma norm_abelSlice_le (hM : ∀ a, ‖φ a‖ ≤ M) (hR : ∀ a, R ≤ a → φ a = 0) {v : ℝ} (hv : v < R)
    (a : ℝ) :
    ‖abelSlice φ v a‖ ≤
      M * √(R - v) * (Ioo v R).indicator (fun a => 1 / √((a - v) * (R - a))) a := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  by_cases h : a ∈ Ioo v R
  · rw [indicator_of_mem h]
    have hx : 0 < √(a - v) := Real.sqrt_pos.2 (by linarith [h.1])
    have hy : 0 < √(R - a) := Real.sqrt_pos.2 (by linarith [h.2])
    have hzy : √(R - a) ≤ √(R - v) := Real.sqrt_le_sqrt (by linarith [h.1])
    have h1 : 1 ≤ √(R - v) / √(R - a) := (one_le_div hy).2 hzy
    have h2 : ‖φ a‖ ≤ M * (√(R - v) / √(R - a)) :=
      le_trans (hM a) (le_mul_of_one_le_right hM0 h1)
    have h3 : ‖abelSlice φ v a‖ = ‖φ a‖ * (√(a - v))⁻¹ := by
      unfold abelSlice
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [h3, Real.sqrt_mul (by linarith [h.1])]
    calc ‖φ a‖ * (√(a - v))⁻¹ ≤ M * (√(R - v) / √(R - a)) * (√(a - v))⁻¹ := by gcongr
      _ = M * √(R - v) * (1 / (√(a - v) * √(R - a))) := by field_simp
  · rw [abelSlice_eq_zero hR h, indicator_of_notMem h]
    simp

lemma integrable_abelSlice (hφ : Measurable φ) (hM : ∀ a, ‖φ a‖ ≤ M)
    (hR : ∀ a, R ≤ a → φ a = 0) (v : ℝ) : Integrable (abelSlice φ v) := by
  by_cases hv : v < R
  · refine Integrable.mono' (g := fun a => M * √(R - v) *
      (Ioo v R).indicator (fun a => 1 / √((a - v) * (R - a))) a) ?_ ?_ ?_
    · exact (((Lightlike.Lorentz.SL2R.integrableOn_inv_sqrt_mul_sub hv).integrable_indicator
        measurableSet_Ioo)).const_mul _
    · exact ((measurable_abelSlice hφ).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (norm_abelSlice_le hM hR hv)
  · have : abelSlice φ v = 0 := by
      funext a
      refine abelSlice_eq_zero hR ?_
      intro h
      linarith [h.1, h.2, not_lt.1 hv]
    rw [this]
    exact integrable_zero _ _ _

lemma integral_norm_abelSlice_le (hM : ∀ a, ‖φ a‖ ≤ M)
    (hR : ∀ a, R ≤ a → φ a = 0) (v : ℝ) : ∫ a, ‖abelSlice φ v a‖ ≤ M * π * √(R - v) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  by_cases hv : v < R
  · have hg : Integrable (fun a => M * √(R - v) *
        (Ioo v R).indicator (fun a => 1 / √((a - v) * (R - a))) a) :=
      (((Lightlike.Lorentz.SL2R.integrableOn_inv_sqrt_mul_sub hv).integrable_indicator
        measurableSet_Ioo)).const_mul _
    have h1 := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun a => norm_nonneg _)) hg
      (Filter.Eventually.of_forall (norm_abelSlice_le hM hR hv))
    rw [integral_const_mul, integral_indicator measurableSet_Ioo,
      Lightlike.Lorentz.SL2R.integral_inv_sqrt_mul_sub hv] at h1
    calc _ ≤ _ := h1
      _ = _ := by ring
  · have : abelSlice φ v = 0 := by
      funext a
      refine abelSlice_eq_zero hR ?_
      intro h
      linarith [h.1, h.2, not_lt.1 hv]
    simp [this, Real.sqrt_eq_zero_of_nonpos (by linarith [not_lt.1 hv] : R - v ≤ 0)]

/-- **Fubini for the triple `(a, b, v)`.** -/
theorem integral_integral_abelSlice (hφ : Measurable φ) (hM : ∀ a, ‖φ a‖ ≤ M)
    (hR : ∀ a, R ≤ a → φ a = 0) :
    ∫ a, ∫ b, ∫ v in Ioi (1 : ℝ), abelSlice φ v a * abelSlice φ v b =
      ∫ v in Ioi (1 : ℝ), (∫ a, abelSlice φ v a) ^ 2 := by
  set f : (ℝ × ℝ) × ℝ → ℂ := fun z => abelSlice φ z.2 z.1.1 * abelSlice φ z.2 z.1.2 with hf
  have hmeas : Measurable f := by
    have h := measurable_abelSlice hφ
    exact (h.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))).mul
      (h.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have hnorm : ∀ v, ∫ x : ℝ × ℝ, ‖f (x, v)‖ ∂(volume.prod volume) =
      (∫ a, ‖abelSlice φ v a‖) ^ 2 := by
    intro v
    have := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun a => ‖abelSlice φ v a‖) (fun a => ‖abelSlice φ v a‖)
    simp only [hf, norm_mul]
    rw [this]
    ring
  have hint : Integrable f ((volume.prod volume).prod (volume.restrict (Ioi (1 : ℝ)))) := by
    rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall (fun v => ?_), ?_⟩
    · exact (integrable_abelSlice hφ hM hR v).mul_prod (integrable_abelSlice hφ hM hR v)
    · simp only [hnorm]
      have hm : Measurable (fun v => ∫ a, ‖abelSlice φ v a‖) := by
        have : StronglyMeasurable (Function.uncurry fun v a => ‖abelSlice φ v a‖) :=
          (measurable_abelSlice hφ).norm.stronglyMeasurable
        exact (this.integral_prod_right).measurable
      have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
      have hc : IntegrableOn (fun _ : ℝ => (M * π) ^ 2 * (R - 1)) (Ioo 1 R) :=
        integrable_const _
      refine Integrable.mono' (g := (Iio R).indicator (fun _ : ℝ => (M * π) ^ 2 * (R - 1)))
        ?_ (hm.pow_const 2).aestronglyMeasurable ?_
      · rw [integrable_indicator_iff measurableSet_Iio]
        simp only [IntegrableOn, Measure.restrict_restrict measurableSet_Iio]
        have : Iio R ∩ Ioi 1 = Ioo 1 R := by
          ext x; simp [and_comm]
        rw [this]
        exact hc
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall (fun v hv => ?_))
        have hv1 : (1 : ℝ) < v := hv
        have h0 : 0 ≤ ∫ a, ‖abelSlice φ v a‖ := integral_nonneg (fun a => norm_nonneg _)
        have hle := integral_norm_abelSlice_le hM hR v
        rw [Real.norm_of_nonneg (by positivity)]
        by_cases hvR : v < R
        · rw [indicator_of_mem (show v ∈ Iio R from hvR)]
          calc (∫ a, ‖abelSlice φ v a‖) ^ 2 ≤ (M * π * √(R - v)) ^ 2 := by gcongr
            _ = (M * π) ^ 2 * (R - v) := by
              rw [mul_pow, Real.sq_sqrt (by linarith)]
            _ ≤ _ := by
              have : 0 ≤ (M * π) ^ 2 := by positivity
              nlinarith
        · have : abelSlice φ v = 0 := by
            funext a
            refine abelSlice_eq_zero hR ?_
            intro h
            linarith [h.1, h.2, not_lt.1 hvR]
          simp [this, show v ∉ Iio R from hvR]
  have hswap := integral_integral_swap (f := fun (x : ℝ × ℝ) (v : ℝ) => f (x, v)) hint
  have hR' : ∀ v, ∫ x : ℝ × ℝ, f (x, v) ∂(volume.prod volume) =
      (∫ a, abelSlice φ v a) ^ 2 := by
    intro v
    have := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun a => abelSlice φ v a) (fun a => abelSlice φ v a)
    simp only [hf]
    rw [this]
    ring
  have hL : ∫ a, ∫ b, ∫ v in Ioi (1 : ℝ), abelSlice φ v a * abelSlice φ v b =
      ∫ x : ℝ × ℝ, ∫ v, f (x, v) ∂(volume.restrict (Ioi (1 : ℝ))) ∂(volume.prod volume) := by
    rw [integral_prod _ hint.integral_prod_left]
  rw [hL, hswap]
  simp only [hR']

end Lightlike.Lorentz.SL2RPlancherel
