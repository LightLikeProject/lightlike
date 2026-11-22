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

end Lightlike.Lorentz.SL2R
