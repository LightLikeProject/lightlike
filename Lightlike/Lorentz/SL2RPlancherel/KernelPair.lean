module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.KernelSquare

/-!
# Fubini for two half-order Abel integrals

The bilinear form of `integral_integral_abelSlice`: for bounded measurable `φ, ψ : ℝ → ℂ` vanishing
on `[R, ∞)`,
`∫_a ∫_b ∫_{v > 1} (φ a / √(a - v)) (ψ b / √(b - v)) = ∫_{v > 1} (∫_a φ a / √(a - v)) (∫_b ψ b / √(b - v))`.
With `ψ = conj φ` this gives the Hermitian square needed for `‖F‖²` in the `SL(2,ℝ)` Plancherel
route (milestone HA3, density `ρ tanh(πρ)`).
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

variable {φ ψ : ℝ → ℂ} {M R : ℝ}

/-- **Fubini for the triple `(a, b, v)`, bilinear form.** -/
theorem integral_integral_abelSlice_pair (hφ : Measurable φ) (hψ : Measurable ψ)
    (hM : ∀ a, ‖φ a‖ ≤ M) (hM' : ∀ a, ‖ψ a‖ ≤ M)
    (hR : ∀ a, R ≤ a → φ a = 0) (hR' : ∀ a, R ≤ a → ψ a = 0) :
    ∫ a, ∫ b, ∫ v in Ioi (1 : ℝ), abelSlice φ v a * abelSlice ψ v b =
      ∫ v in Ioi (1 : ℝ), (∫ a, abelSlice φ v a) * (∫ b, abelSlice ψ v b) := by
  set f : (ℝ × ℝ) × ℝ → ℂ := fun z => abelSlice φ z.2 z.1.1 * abelSlice ψ z.2 z.1.2 with hf
  have hmeas : Measurable f := by
    have h := measurable_abelSlice hφ
    have h' := measurable_abelSlice hψ
    exact (h.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))).mul
      (h'.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have hnorm : ∀ v, ∫ x : ℝ × ℝ, ‖f (x, v)‖ ∂(volume.prod volume) =
      (∫ a, ‖abelSlice φ v a‖) * (∫ a, ‖abelSlice ψ v a‖) := by
    intro v
    have := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun a => ‖abelSlice φ v a‖) (fun a => ‖abelSlice ψ v a‖)
    simp only [hf, norm_mul]
    rw [this]
  have hint : Integrable f ((volume.prod volume).prod (volume.restrict (Ioi (1 : ℝ)))) := by
    rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall (fun v => ?_), ?_⟩
    · exact (integrable_abelSlice hφ hM hR v).mul_prod (integrable_abelSlice hψ hM' hR' v)
    · simp only [hnorm]
      have hm : ∀ {χ : ℝ → ℂ}, Measurable χ → Measurable (fun v => ∫ a, ‖abelSlice χ v a‖) := by
        intro χ hχ
        have : StronglyMeasurable (Function.uncurry fun v a => ‖abelSlice χ v a‖) :=
          (measurable_abelSlice hχ).norm.stronglyMeasurable
        exact (this.integral_prod_right).measurable
      have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
      have hc : IntegrableOn (fun _ : ℝ => (M * π) ^ 2 * (R - 1)) (Ioo 1 R) :=
        integrable_const _
      refine Integrable.mono' (g := (Iio R).indicator (fun _ : ℝ => (M * π) ^ 2 * (R - 1)))
        ?_ ((hm hφ).mul (hm hψ)).aestronglyMeasurable ?_
      · rw [integrable_indicator_iff measurableSet_Iio]
        simp only [IntegrableOn, Measure.restrict_restrict measurableSet_Iio]
        have : Iio R ∩ Ioi 1 = Ioo 1 R := by
          ext x; simp [and_comm]
        rw [this]
        exact hc
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall (fun v hv => ?_))
        have hv1 : (1 : ℝ) < v := hv
        have h0 : 0 ≤ ∫ a, ‖abelSlice φ v a‖ := integral_nonneg (fun a => norm_nonneg _)
        have h0' : 0 ≤ ∫ a, ‖abelSlice ψ v a‖ := integral_nonneg (fun a => norm_nonneg _)
        have hle := integral_norm_abelSlice_le hM hR v
        have hle' := integral_norm_abelSlice_le hM' hR' v
        rw [Real.norm_of_nonneg (by positivity)]
        by_cases hvR : v < R
        · rw [indicator_of_mem (show v ∈ Iio R from hvR)]
          calc (∫ a, ‖abelSlice φ v a‖) * (∫ a, ‖abelSlice ψ v a‖)
              ≤ (M * π * √(R - v)) * (M * π * √(R - v)) := by gcongr
            _ = (M * π) ^ 2 * (R - v) := by
              have := Real.mul_self_sqrt (show 0 ≤ R - v by linarith)
              calc (M * π * √(R - v)) * (M * π * √(R - v))
                  = (M * π) ^ 2 * (√(R - v) * √(R - v)) := by ring
                _ = _ := by rw [this]
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
  have hR2 : ∀ v, ∫ x : ℝ × ℝ, f (x, v) ∂(volume.prod volume) =
      (∫ a, abelSlice φ v a) * (∫ a, abelSlice ψ v a) := by
    intro v
    have := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun a => abelSlice φ v a) (fun a => abelSlice ψ v a)
    simp only [hf]
    rw [this]
  have hL : ∫ a, ∫ b, ∫ v in Ioi (1 : ℝ), abelSlice φ v a * abelSlice ψ v b =
      ∫ x : ℝ × ℝ, ∫ v, f (x, v) ∂(volume.restrict (Ioi (1 : ℝ))) ∂(volume.prod volume) := by
    rw [integral_prod _ hint.integral_prod_left]
  rw [hL, hswap]
  simp only [hR2]

end Lightlike.Lorentz.SL2RPlancherel
