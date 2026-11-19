import Lightlike.Asymptotics.Tauberian.Window
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exchange of the spectral integral and the Fourier integral

First step of the route of Mukhametzhanov–Zhiboedov (Sections 3-4): a test function `φ` with
`φ x = ∫ g t e^{-i t x} dt`, `g` integrable, is integrated against `e^{-β x} dρ` by integrating `g`
against the Laplace transform on the vertical line, `∫ φ e^{-βx} dρ = ∫ g(t) L(β + i t) dt`.
-/

open MeasureTheory Set Complex

noncomputable section

namespace Lightlike.Tauberian

/-- The integrand of the exchange is integrable on the product. -/
lemma exchange_integrable (ρ : Measure ℝ) [SFinite ρ] {β : ℝ}
    (hint : Integrable (fun x : ℝ => Real.exp (-β * x)) ρ) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (Function.uncurry fun (x : ℝ) (t : ℝ) =>
      g t * Complex.exp (-(t * x * Complex.I)) * (Real.exp (-β * x) : ℂ)) (ρ.prod volume) := by
  have hb : Integrable (fun z : ℝ × ℝ => Real.exp (-β * z.1) * ‖g z.2‖) (ρ.prod volume) :=
    Integrable.mul_prod hint hg.norm
  refine hb.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · have h1 : AEStronglyMeasurable (fun z : ℝ × ℝ => g z.2) (ρ.prod volume) :=
      hg.aestronglyMeasurable.comp_snd
    have h2 : Continuous fun z : ℝ × ℝ =>
        Complex.exp (-(z.2 * z.1 * Complex.I)) * (Real.exp (-β * z.1) : ℂ) := by fun_prop
    exact (h1.mul h2.aestronglyMeasurable).congr (Filter.Eventually.of_forall fun z => by
      simp only [Function.uncurry, Pi.mul_apply]; ring)
  · simp only [Function.uncurry, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have : Real.exp (-(↑z.2 * ↑z.1 * Complex.I)).re = 1 := by simp
    rw [this]; ring_nf; exact le_refl _



/-- The complex Laplace transform `L(z) = ∫ e^{-z x} dρ(x)`. -/
def laplaceC (ρ : Measure ℝ) (z : ℂ) : ℂ := ∫ x, Complex.exp (-(z * x)) ∂ρ

/-- **Exchange.** -/
theorem integral_fourier_mul_exp (ρ : Measure ℝ) [SFinite ρ] {β : ℝ}
    (hint : Integrable (fun x : ℝ => Real.exp (-β * x)) ρ) {g : ℝ → ℂ} (hg : Integrable g) :
    ∫ x, (∫ t, g t * Complex.exp (-(t * x * Complex.I))) * Real.exp (-β * x) ∂ρ =
      ∫ t, g t * laplaceC ρ (β + t * Complex.I) := by
  have e1 : ∀ x : ℝ, (∫ t, g t * Complex.exp (-(t * x * Complex.I))) * (Real.exp (-β * x) : ℂ) =
      ∫ t, g t * Complex.exp (-(t * x * Complex.I)) * (Real.exp (-β * x) : ℂ) := fun x => by
    rw [integral_mul_const]
  have hF := exchange_integrable ρ hint hg
  simp_rw [e1]
  rw [MeasureTheory.integral_integral_swap hF]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [laplaceC]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show g t * Complex.exp (-(t * x * Complex.I)) * (Real.exp (-β * x) : ℂ) =
    g t * Complex.exp (-((β + t * Complex.I) * x))
  rw [mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The right-hand side of the exchange is integrable in `t`. -/
theorem integrable_fourier_laplace (ρ : Measure ℝ) [SFinite ρ] {β : ℝ}
    (hint : Integrable (fun x : ℝ => Real.exp (-β * x)) ρ) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (fun t : ℝ => g t * laplaceC ρ (β + t * Complex.I)) := by
  have hF := exchange_integrable ρ hint hg
  refine (hF.integral_prod_right).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.uncurry, laplaceC]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show g t * Complex.exp (-(t * x * Complex.I)) * (Real.exp (-β * x) : ℂ) =
    g t * Complex.exp (-((β + t * Complex.I) * x))
  rw [mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Lightlike.Tauberian
