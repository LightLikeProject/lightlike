import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PolarTorus

/-!
# Polar coordinates for the Bochner integral on `SL(2,ℝ)`

The Haar measure of `SL(2,ℝ)` is the image of `sinh ξ dξ ⊗ dα ⊗ dθ` on
`(0, ∞) × (0, 2π] × (0, 2π]` under `(ξ, α, θ) ↦ k_α a_ξ k_θ` (`haarR_eq_map_polarMeasure`, from the
`[0, ∞]`-valued formula `lintegral_haarR_torus`), so for every integrable `f`,
`∫ f dg = ∫_{ξ>0} sinh ξ ∫_0^{2π} ∫_0^{2π} f(k_α a_ξ k_θ) dθ dα dξ` (`integral_haarR_torus`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (matrix coefficients of `π_ν(f)`), milestone HA3.
-/

open MeasureTheory Set Lightlike.Lorentz.SL2R
open scoped ENNReal NNReal Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The polar map `(ξ, (α, θ)) ↦ k_α a_ξ k_θ`. -/
def polarMap (p : ℝ × (ℝ × ℝ)) : SL2R := rot p.2.1 * aR p.1 * rot p.2.2

lemma continuous_polarMap : Continuous polarMap :=
  ((continuous_rot.comp (continuous_fst.comp continuous_snd)).mul
    (continuous_aR.comp continuous_fst)).mul (continuous_rot.comp (continuous_snd.comp continuous_snd))

lemma measurable_sinh_toNNReal : Measurable fun ξ : ℝ => (Real.sinh ξ).toNNReal :=
  Real.continuous_sinh.measurable.real_toNNReal

/-- The polar measure `sinh ξ dξ ⊗ dα ⊗ dθ` on `(0, ∞) × (0, 2π] × (0, 2π]`. -/
def polarMeasure : Measure (ℝ × (ℝ × ℝ)) :=
  ((volume.restrict (Ioi (0 : ℝ))).withDensity fun ξ => ((Real.sinh ξ).toNNReal : ℝ≥0∞)).prod
    ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict (Ioc 0 (2 * π))))

/-- **The Haar measure in polar coordinates**: `haarR` is the image of the polar measure. -/
theorem haarR_eq_map_polarMeasure : haarR = polarMeasure.map polarMap := by
  have hT := continuous_polarMap.measurable
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_map hF hT, lintegral_haarR_torus hF, polarMeasure,
    lintegral_prod (fun z => F (polarMap z)) (hF.comp hT).aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ measurable_sinh_toNNReal.coe_nnreal_ennreal
      (Measurable.lintegral_prod_right' (f := fun z => F (polarMap z)) (hF.comp hT))]
  refine setLIntegral_congr_fun measurableSet_Ioi fun ξ _ => ?_
  simp only [Pi.mul_apply]
  congr 1
  rw [lintegral_prod (fun y => F (polarMap (ξ, y)))
    ((hF.comp hT).comp measurable_prodMk_left).aemeasurable]
  rfl

/-- **Polar coordinates for the Bochner integral**: for `f` integrable for the Haar measure,
`∫ f = ∫_{ξ>0} sinh ξ ∫_0^{2π} ∫_0^{2π} f(k_α a_ξ k_θ) dθ dα dξ`. -/
theorem integral_haarR_torus {f : SL2R → ℂ} (hf : Integrable f haarR) :
    ∫ g, f g ∂haarR = ∫ ξ in Ioi (0 : ℝ), (Real.sinh ξ : ℂ) *
      ∫ α in Ioc 0 (2 * π), ∫ θ in Ioc 0 (2 * π), f (rot α * aR ξ * rot θ) := by
  have hT := continuous_polarMap.measurable
  rw [haarR_eq_map_polarMeasure] at hf ⊢
  have hfm : AEStronglyMeasurable f (polarMeasure.map polarMap) := hf.aestronglyMeasurable
  have hfT : Integrable (f ∘ polarMap) polarMeasure :=
    (integrable_map_measure hfm hT.aemeasurable).1 hf
  rw [integral_map hT.aemeasurable hfm]
  rw [polarMeasure] at hfT ⊢
  rw [integral_prod (fun z => f (polarMap z)) hfT,
    integral_withDensity_eq_integral_smul measurable_sinh_toNNReal]
  have hae : ∀ᵐ ξ ∂(volume.restrict (Ioi (0 : ℝ))), Integrable (fun y => f (polarMap (ξ, y)))
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict (Ioc 0 (2 * π)))) := by
    have h := hfT.prod_right_ae
    rw [ae_withDensity_iff measurable_sinh_toNNReal.coe_nnreal_ennreal] at h
    filter_upwards [h, ae_restrict_mem measurableSet_Ioi] with ξ hξ hpos
    refine hξ ?_
    have : 0 < Real.sinh ξ := Real.sinh_pos_iff.2 hpos
    simpa using this
  refine integral_congr_ae ?_
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with ξ hint hξ
  rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.sinh_pos_iff.2 hξ).le, Complex.real_smul]
  congr 1
  rw [integral_prod _ hint]
  rfl

end Lightlike.Lorentz.SL2RPlancherel
