module

public import Lightlike.Lorentz.SL2R

/-!
# Integrals over the upper half-plane in coordinates

`lintegral_upperHalfPlane`: `∫_ℍ G dμ_ℍ = ∫_{y > 0} G(x + iy) dx dy / y²`, the first step of the
radial integral formula for `SL(2,ℝ)` (milestone HA3).
-/

@[expose] public section

open MeasureTheory UpperHalfPlane

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- **The invariant measure of `ℍ` in coordinates**: for measurable `G : ℍ → [0,∞]`,
`∫_ℍ G dμ_ℍ = ∫_{w ∈ ℂ, Im w > 0} G(w) / (Im w)² dw`. -/
lemma lintegral_upperHalfPlane {G : ℍ → ENNReal} (hG : Measurable G) :
    ∫⁻ z : ℍ, G z =
      ∫⁻ w : ℂ in {w : ℂ | 0 < w.im}, G (UpperHalfPlane.ofComplex w) *
        ENNReal.ofReal (1 / w.im ^ 2) := by
  have hd : Measurable fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) := by
    have : Measurable fun z : ℍ => z.im := (UpperHalfPlane.continuous_im).measurable
    fun_prop
  rw [volume_def, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hG]
  have hmp : MeasurableEmbedding UpperHalfPlane.coe := measurableEmbedding_coe
  have hrange : Set.range UpperHalfPlane.coe = {w : ℂ | 0 < w.im} := by
    ext w; constructor
    · rintro ⟨z, rfl⟩; exact z.im_pos
    · intro hw; exact ⟨⟨w, hw⟩, rfl⟩
  have key := hmp.lintegral_map (μ := volume.comap UpperHalfPlane.coe)
    (fun w : ℂ => G (UpperHalfPlane.ofComplex w) *
      ENNReal.ofReal (1 / w.im ^ 2))
  rw [hmp.map_comap, hrange] at key
  rw [key]
  refine lintegral_congr fun z => ?_
  have hz : UpperHalfPlane.ofComplex (z : ℂ) = z := UpperHalfPlane.ofComplex_apply z
  have him : (z : ℂ).im = z.im := rfl
  simp only [Pi.mul_apply, hz, him, mul_comm]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp [NNReal.coe_pow]

/-- **Iterated form**: `∫_ℍ G dμ_ℍ = ∫_{y>0} ∫_ℝ G(x + iy) dx dy / y²`, for measurable
`G : ℍ → [0,∞]`. -/
lemma lintegral_upperHalfPlane_prod {G : ℍ → ENNReal} (hG : Measurable G) :
    ∫⁻ z : ℍ, G z =
      ∫⁻ y in Set.Ioi (0 : ℝ), ∫⁻ x : ℝ,
        G (UpperHalfPlane.ofComplex ⟨x, y⟩) * ENNReal.ofReal (1 / y ^ 2) := by
  rw [lintegral_upperHalfPlane hG, ← lintegral_indicator (measurableSet_lt measurable_const
    Complex.measurable_im)]
  have hmp := Complex.volume_preserving_equiv_real_prod
  set F : ℂ → ENNReal := fun w => G (UpperHalfPlane.ofComplex w) * ENNReal.ofReal (1 / w.im ^ 2)
  have hF : Measurable F := by
    have h1 : Measurable fun w : ℂ => UpperHalfPlane.ofComplex w := by
      rw [← measurableEmbedding_coe.measurable_comp_iff]
      have : (UpperHalfPlane.coe ∘ fun w : ℂ => UpperHalfPlane.ofComplex w) =
          fun w : ℂ => if 0 < w.im then w else ((UpperHalfPlane.ofComplex 0 : ℍ) : ℂ) := by
        ext w
        by_cases h : 0 < w.im
        · simp [UpperHalfPlane.ofComplex_apply_of_im_pos h, h]
        · have h0 : UpperHalfPlane.ofComplex w = UpperHalfPlane.ofComplex 0 := by
            rw [UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp h),
              UpperHalfPlane.ofComplex_apply_of_im_nonpos (by simp)]
          simp [h0, h]
      rw [this]
      exact Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im)
        measurable_id measurable_const
    have h2 : Measurable fun w : ℂ => ENNReal.ofReal (1 / w.im ^ 2) := by fun_prop
    exact (hG.comp h1).mul h2
  have key := hmp.symm.lintegral_comp_emb Complex.measurableEquivRealProd.symm.measurableEmbedding
    (fun w : ℂ => Set.indicator {w : ℂ | 0 < w.im} F w)
  rw [← key]
  have hm : Measurable fun p : ℝ × ℝ => Set.indicator {w : ℂ | 0 < w.im} F
      (Complex.measurableEquivRealProd.symm p) :=
    (hF.indicator (measurableSet_lt measurable_const Complex.measurable_im)).comp
      Complex.measurableEquivRealProd.symm.measurable
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ hm.aemeasurable,
    ← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun y => ?_
  by_cases hy : 0 < y
  · simp [Set.indicator, hy, F]
  · simp [Set.indicator, hy]

end Lightlike.Lorentz.SL2R
