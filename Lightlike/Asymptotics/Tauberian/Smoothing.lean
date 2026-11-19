import Lightlike.Asymptotics.Tauberian.BoxConv
import Lightlike.Asymptotics.Tauberian.FourierExchange
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The pole-free smoothing of the step function

For the kernel `g ≥ 0` with `∫ g(t) e^{-i t x} dt = κ(x) = (2 b sinc (b x))⁴` and `β > 0`:

`∫ g(t) / (β + i t) · e^{-i t y} dt = ∫₀^∞ e^{-β s} κ(y + s) ds` (`fourier_inv_eq`),

by Fubini and `1/(β + i t) = ∫₀^∞ e^{-(β + i t) s} ds`; no inversion theorem and no pole is involved.
-/

open MeasureTheory Set Complex

noncomputable section

namespace Lightlike.Tauberian

/-- `1/(β + i t) = ∫₀^∞ e^{-(β + i t) s} ds`. -/
lemma integral_exp_Ioi {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    ∫ s in Ioi (0 : ℝ), Complex.exp (-((β + t * Complex.I) * s)) = 1 / (β + t * Complex.I) := by
  have hne : (β + t * Complex.I : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hre : (-(β + t * Complex.I : ℂ)).re < 0 := by simpa using hβ
  have h := integral_exp_mul_complex_Ioi hre 0
  have e1 : ∀ s : ℝ, Complex.exp (-((β + t * Complex.I) * s)) =
      Complex.exp ((-(β + t * Complex.I)) * s) := fun s => by rw [neg_mul]
  simp_rw [e1]
  rw [h]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div, div_neg, neg_neg]

/-- **The pole-free identity.** -/
theorem fourier_inv_eq {b β : ℝ} (hβ : 0 < β) {g : ℝ → ℝ} (hgi : Integrable g)
    (hg : ∀ x : ℝ, ∫ t, (g t : ℂ) * char x t = (((2 * b * Real.sinc (b * x)) ^ 4 : ℝ) : ℂ)) (y : ℝ) :
    ∫ t, (g t : ℂ) * (1 / (β + t * Complex.I)) * Complex.exp (-(t * y * Complex.I)) =
      (((∫ s in Ioi (0 : ℝ), Real.exp (-β * s) * (2 * b * Real.sinc (b * (y + s))) ^ 4 : ℝ)) : ℂ) := by
  set F : ℝ → ℝ → ℂ := fun t s => (g t : ℂ) * Complex.exp (-(t * y * Complex.I)) *
    Complex.exp (-((β + t * Complex.I) * s)) with hF
  have h1 : ∀ t : ℝ, (g t : ℂ) * (1 / (β + t * Complex.I)) * Complex.exp (-(t * y * Complex.I)) =
      ∫ s in Ioi (0 : ℝ), F t s := by
    intro t
    simp only [hF]
    rw [integral_const_mul, integral_exp_Ioi hβ t]
    ring
  simp_rw [h1]
  have hint : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hb : Integrable (fun z : ℝ × ℝ => ‖g z.1‖ * Real.exp (-β * z.2))
        (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
      exact Integrable.mul_prod (L := ℝ) (f := fun t : ℝ => ‖g t‖) (g := fun s : ℝ => Real.exp (-β * s))
        hgi.norm (integrableOn_exp_mul_Ioi (by linarith) 0)
    refine hb.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have h1 : AEStronglyMeasurable (fun z : ℝ × ℝ => (g z.1 : ℂ)) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
        hgi.ofReal.aestronglyMeasurable.comp_fst
      have h2 : Continuous fun z : ℝ × ℝ => Complex.exp (-(z.1 * y * Complex.I)) *
          Complex.exp (-((β + z.1 * Complex.I) * z.2)) := by fun_prop
      exact (h1.mul h2.aestronglyMeasurable).congr (Filter.Eventually.of_forall fun z => by
        simp only [Function.uncurry, hF, Pi.mul_apply]; ring)
    · simp only [Function.uncurry, hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      have e1 : (-(↑z.1 * ↑y * Complex.I)).re = 0 := by simp
      have e2 : (-((↑β + ↑z.1 * Complex.I) * ↑z.2)).re = -β * z.2 := by simp
      rw [e1, e2]; simp
  rw [MeasureTheory.integral_integral_swap hint, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have e3 : ∀ t : ℝ, F t s = (g t : ℂ) * char (y + s) t * Complex.exp (-(β * s)) := by
    intro t
    simp only [hF, char]
    rw [mul_assoc (g t : ℂ), ← Complex.exp_add, mul_assoc (g t : ℂ), ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [e3]
  rw [integral_mul_const, hg (y + s)]
  push_cast
  ring

/-- The smoothed step `Ψ(y) = ∫₀^∞ e^{-β s} κ(y + s) ds`. -/
def smoothΨ (b β y : ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), Real.exp (-β * s) * (2 * b * Real.sinc (b * (y + s))) ^ 4

/-- The weight `g(t) e^{i t Δ} / (β + i t)` is integrable. -/
lemma integrable_weight {β Δ : ℝ} (hβ : 0 < β) {g : ℝ → ℝ} (hgi : Integrable g) :
    Integrable (fun t : ℝ => (g t : ℂ) * (1 / (β + t * Complex.I)) * Complex.exp (t * Δ * Complex.I)) := by
  have hc : Continuous fun t : ℝ => (1 / (β + t * Complex.I)) * Complex.exp (t * Δ * Complex.I) := by
    refine Continuous.mul ?_ (by fun_prop)
    refine Continuous.div continuous_const (by fun_prop) fun t => ?_
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have := hgi.ofReal.mul_bdd hc.aestronglyMeasurable (c := 1 / β) (Filter.Eventually.of_forall fun t => ?_)
  · exact this.congr (Filter.Eventually.of_forall fun t => (mul_assoc _ _ _).symm)
  · rw [norm_mul, Complex.norm_exp]
    simp only [norm_div, norm_one, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    have h1 : β ≤ ‖(β : ℂ) + t * Complex.I‖ := by
      have := Complex.abs_re_le_norm ((β : ℂ) + t * Complex.I)
      simpa [abs_of_pos hβ] using this
    have h2 : 1 / ‖(β : ℂ) + t * Complex.I‖ ≤ 1 / β :=
      one_div_le_one_div_of_le hβ h1
    simpa using h2

/-- **The exchange for the smoothed step.** -/
theorem smooth_representation (μ : Measure ℝ) [SFinite μ] {b β Δ : ℝ} (hβ : 0 < β)
    (hint : Integrable (fun x : ℝ => Real.exp (-β * x)) μ) {g : ℝ → ℝ} (hgi : Integrable g)
    (hg : ∀ x : ℝ, ∫ t, (g t : ℂ) * char x t = (((2 * b * Real.sinc (b * x)) ^ 4 : ℝ) : ℂ)) :
    (((∫ x, smoothΨ b β (x - Δ) * Real.exp (-β * x) ∂μ : ℝ)) : ℂ) =
      ∫ t, (g t : ℂ) * (1 / (β + t * Complex.I)) * Complex.exp (t * Δ * Complex.I) *
        laplaceC μ (β + t * Complex.I) := by
  have hGi := integrable_weight (Δ := Δ) hβ hgi
  have h := integral_fourier_mul_exp μ hint hGi
  rw [← integral_complex_ofReal]
  have e1 : ∀ x : ℝ, (∫ t, ((g t : ℂ) * (1 / (β + t * Complex.I)) * Complex.exp (t * Δ * Complex.I)) *
      Complex.exp (-(t * x * Complex.I))) = ((smoothΨ b β (x - Δ) : ℝ) : ℂ) := by
    intro x
    rw [smoothΨ, ← fourier_inv_eq hβ hgi hg (x - Δ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [mul_assoc (↑(g t) * (1 / (↑β + ↑t * Complex.I))), ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [e1] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  push_cast
  ring

end Lightlike.Tauberian
