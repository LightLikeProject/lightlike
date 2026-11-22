import Lightlike.Lorentz.SL2RPlancherel.HalfLine

/-!
# The autocorrelation integral as a double integral

For an integrable kernel `L` and a Schwartz function `h`, the quantity
`∫ x, L x * ∫ y, conj (h y) * h (y + x)` that `integral_logTanhKernel_autocorr` evaluates on the
Fourier side is the double integral `∬ conj (h y) * L (z - y) * h z` over `ℝ²`.  This is the form
that meets the quadratic form `∬ g' (t) g' (s) K (t, s)` of the Abel transform (the radial
Plancherel formula for SL(2,ℝ)).
-/

namespace Lightlike.Lorentz.SL2RPlancherel

open MeasureTheory Set

/-- The integrand `(z, y) ↦ conj (h y) * L (z - y) * h z` is integrable on `ℝ × ℝ`. -/
theorem integrable_kernel_pair {L : ℝ → ℂ} (hL : Integrable L) (h : SchwartzMap ℝ ℂ) :
    Integrable (fun p : ℝ × ℝ => h p.1 * (starRingEnd ℂ (h p.2) * L (p.1 - p.2)))
      ((volume : Measure ℝ).prod volume) := by
  have hh : Integrable (fun y : ℝ => starRingEnd ℂ (h y)) :=
    (SchwartzMap.postcompCLM (𝕜 := ℝ) (Complex.conjCLE.toContinuousLinearMap) h).integrable
  have hc := Integrable.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hh hL
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
  refine Integrable.bdd_mul (c := ‖h.toBoundedContinuousFunction‖) hc ?_ ?_
  · exact (h.continuous.comp continuous_fst).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun p =>
      h.toBoundedContinuousFunction.norm_coe_le_norm p.1)

/-- Fubini form of the autocorrelation integral:
`∫ L(x) ∫ conj h(y) h(y+x) dy dx = ∫ conj h(y) ∫ L(z-y) h(z) dz dy`. -/
theorem integral_kernel_autocorr_eq {L : ℝ → ℂ} (hL : Integrable L) (h : SchwartzMap ℝ ℂ) :
    ∫ x, L x * ∫ y, starRingEnd ℂ (h y) * h (y + x) =
      ∫ y, starRingEnd ℂ (h y) * ∫ z, L (z - y) * h z := by
  have hH := integrable_kernel_pair hL h
  have hG : Integrable (fun p : ℝ × ℝ => L p.1 * (starRingEnd ℂ (h p.2) * h (p.2 + p.1)))
      ((volume : Measure ℝ).prod volume) := by
    have hmp := MeasureTheory.measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)
    let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
      { toEquiv := ⟨fun z => (z.1 + z.2, z.2), fun z => (z.1 - z.2, z.2),
          fun z => by simp, fun z => by simp⟩
        measurable_toFun := by
          show Measurable fun z : ℝ × ℝ => (z.1 + z.2, z.2)
          fun_prop
        measurable_invFun := by
          show Measurable fun z : ℝ × ℝ => (z.1 - z.2, z.2)
          fun_prop }
    have := (hmp.integrable_comp_emb (e.measurableEmbedding) |>.mpr hH)
    refine this.congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Function.comp, add_sub_cancel_right]
    rw [add_comm p.2 p.1]
    ring
  have hswap := integral_integral_swap
    (f := fun x y => L x * (starRingEnd ℂ (h y) * h (y + x))) hG
  calc ∫ x, L x * ∫ y, starRingEnd ℂ (h y) * h (y + x)
      = ∫ x, ∫ y, L x * (starRingEnd ℂ (h y) * h (y + x)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only
        rw [integral_const_mul]
    _ = ∫ y, ∫ x, L x * (starRingEnd ℂ (h y) * h (y + x)) := hswap
    _ = ∫ y, starRingEnd ℂ (h y) * ∫ z, L (z - y) * h z := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        simp only
        have := integral_add_left_eq_self (μ := (volume : Measure ℝ))
          (fun z => L (z - y) * h z) y
        simp only [add_sub_cancel_left] at this
        have e : ∫ x, L x * (starRingEnd ℂ (h y) * h (y + x)) =
            starRingEnd ℂ (h y) * ∫ x, L x * h (y + x) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          simp only
          ring
        rw [e, this]

end Lightlike.Lorentz.SL2RPlancherel
