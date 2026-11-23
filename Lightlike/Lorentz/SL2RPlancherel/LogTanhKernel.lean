import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.CosineLogTanh

/-!
# The kernel `-log tanh (|x|/4)` on the real line

The even kernel `L x = -log tanh (|x|/4)` is the kernel through which the spherical Plancherel
formula of the hyperbolic plane acquires its density `ρ tanh (π ρ)`.  Here it is defined on all of
`ℝ`, shown integrable, and its Fourier transform is computed from the cosine transform
`integral_cos_mul_neg_log_tanh`.
-/

namespace Lightlike.Lorentz.SL2RPlancherel

open MeasureTheory Set
open scoped FourierTransform

/-- The even kernel `x ↦ -log tanh (|x|/4)` on `ℝ`. -/
noncomputable def logTanhKernel (x : ℝ) : ℝ := -Real.log (Real.tanh (|x| / 4))

/-- The kernel is even. -/
theorem logTanhKernel_neg (x : ℝ) : logTanhKernel (-x) = logTanhKernel x := by
  simp [logTanhKernel]

/-- On `x > 0` the kernel is `-log tanh (x/4)`. -/
theorem logTanhKernel_of_pos {x : ℝ} (hx : 0 < x) :
    logTanhKernel x = -Real.log (Real.tanh (x / 4)) := by
  simp [logTanhKernel, abs_of_pos hx]

/-- The kernel is integrable on `(−∞, 0)`, by evenness. -/
theorem integrableOn_logTanhKernel_Iio : IntegrableOn logTanhKernel (Iio 0) := by
  have h : IntegrableOn (fun x : ℝ => logTanhKernel (-x)) (Iio 0) := by
    have hp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding (s := Ioi 0) (f := logTanhKernel)
    have hpre : (fun x : ℝ => -x) ⁻¹' Ioi 0 = Iio 0 := by
      ext x; simp
    have h0 : IntegrableOn logTanhKernel (Ioi 0) :=
      integrableOn_neg_log_tanh.congr_fun (fun x hx => (logTanhKernel_of_pos hx).symm)
        measurableSet_Ioi
    have := hp.mpr h0
    simpa [Function.comp_def, hpre] using this
  simpa [logTanhKernel_neg] using h

/-- The kernel `-log tanh (|x|/4)` is integrable on `ℝ`. -/
theorem integrable_logTanhKernel : Integrable logTanhKernel := by
  have h0 : IntegrableOn logTanhKernel (Ioi 0) :=
    integrableOn_neg_log_tanh.congr_fun (fun x hx => (logTanhKernel_of_pos hx).symm)
      measurableSet_Ioi
  have h1 := integrableOn_logTanhKernel_Iio.union h0
  have hu : Iio (0:ℝ) ∪ Ioi 0 = {0}ᶜ := by
    ext x; simp only [mem_union, mem_Iio, mem_Ioi, mem_compl_iff, mem_singleton_iff]
    exact lt_or_lt_iff_ne
  rw [hu] at h1
  rw [IntegrableOn, restrict_compl_singleton] at h1
  exact h1

/-- The cosine transform over all of `ℝ`: `∫ cos (a x) L(x) = 2 ∫_{x>0} cos (a x)(-log tanh (x/4))`. -/
theorem integral_cos_mul_logTanhKernel (a : ℝ) :
    ∫ x : ℝ, Real.cos (a * x) * logTanhKernel x
      = 2 * ∫ x in Ioi (0:ℝ), Real.cos (a * x) * (-Real.log (Real.tanh (x / 4))) := by
  have := integral_comp_abs (f := fun y : ℝ => Real.cos (a * y) * (-Real.log (Real.tanh (y / 4))))
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [logTanhKernel]
  congr 1
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, mul_neg, Real.cos_neg]

/-- The Fourier transform of `L` at `ξ > 0`, with `ρ = 2π ξ`:
`𝓕 L (ξ) = (π/ρ) tanh (π ρ)`.  This is the source of the density `ρ tanh (π ρ)` in the Plancherel
formula of `SL(2,ℝ)`. -/
theorem fourier_logTanhKernel {ξ : ℝ} (hξ : 0 < ξ) :
    𝓕 (fun x : ℝ => ((logTanhKernel x : ℝ) : ℂ)) ξ
      = ((Real.pi / (2 * Real.pi * ξ) * Real.tanh (Real.pi * (2 * Real.pi * ξ)) : ℝ) : ℂ) := by
  set a : ℝ := 2 * Real.pi * ξ with ha
  have hapos : 0 < a := by positivity
  set f : ℝ → ℂ := fun v => Complex.exp (↑(-a * v) * Complex.I) * ((logTanhKernel v : ℝ) : ℂ)
    with hf
  have hL := integrable_logTanhKernel
  have hfint : Integrable f := by
    refine hL.norm.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact (by fun_prop : Continuous fun v : ℝ => Complex.exp (↑(-a * v) * Complex.I)).aestronglyMeasurable.mul
        hL.ofReal.aestronglyMeasurable
    · simp only [hf, norm_mul]
      rw [show ((-a * v : ℝ) : ℂ) * Complex.I = ((-a * v : ℝ) : ℂ) * Complex.I from rfl,
        Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real]
  have hfint' : Integrable fun v => f (-v) := hfint.comp_neg
  have h1 : ∫ v, f (-v) = ∫ v, f v := integral_neg_eq_self f volume
  have hsum : ∫ v, (f v + f (-v)) = 2 * ∫ v, f v := by
    rw [integral_add hfint hfint', h1]; ring
  have hcos : ∀ v, f v + f (-v) = 2 * ((Real.cos (a * v) * logTanhKernel v : ℝ) : ℂ) := by
    intro v
    simp only [hf, logTanhKernel_neg]
    push_cast
    rw [Complex.cos]
    have e1 : -(a : ℂ) * -(v : ℂ) * Complex.I = (a : ℂ) * v * Complex.I := by ring
    have e2 : -(a : ℂ) * (v : ℂ) * Complex.I = -((a : ℂ) * v) * Complex.I := by ring
    rw [e1, e2]
    ring
  simp_rw [hcos] at hsum
  rw [integral_const_mul, integral_complex_ofReal, integral_cos_mul_logTanhKernel,
    integral_cos_mul_neg_log_tanh hapos] at hsum
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hfe : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) •
      ((logTanhKernel v : ℝ) : ℂ)) = f := by
    funext v; simp only [hf, smul_eq_mul]; congr 3; rw [ha]; push_cast; ring
  rw [hfe]
  have h2 : (2:ℂ) * ∫ v, f v = 2 * ((Real.pi / (2 * Real.pi * ξ) * Real.tanh (Real.pi * a) : ℝ) : ℂ) := by
    rw [← hsum]; push_cast; rw [ha]; push_cast; ring
  have := mul_left_cancel₀ (two_ne_zero) h2
  rw [this]

end Lightlike.Lorentz.SL2RPlancherel
