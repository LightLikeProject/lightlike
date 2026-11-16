import Lightlike.Asymptotics.Lorentzian.CoherentVertex
import Lightlike.Lorentz.FixedChart
import Lightlike.Asymptotics.Lorentzian.Amplitude

/-!
# The Haar measure of the vertex in the fixed chart

`FixedChart.lean` shows that the Haar measure `haarC` of `SL(2,ℂ)` is Lebesgue measure on `ℂ³` in
the chart `g_z(b, w, λ)`: the density is exactly `1` (`haarC_eq_map_fixChart`). Here this is used for
the vertex: the gauge-fixed vertex `lorVertex` is `(∏ c_e) s⁻⁴` times the Lebesgue integral of the
integrand over `(ℂ³)⁴ × ℂ¹⁰` (real dimension `24 + 20 = 44`) in these charts, `s = haarScalarFactor
haarC SL2C.haar` (`lorVertex_eq_fixChart_integral`). Because the density is `1`, the amplitude of
the chart integral is the product of the densities `Ω_e` alone, which is the explicit `a(x)` of the
asymptotic formula, with no further Jacobian, in this chart (a change of chart multiplies it by the
Jacobian of the transition map).

The vertex is defined as an iterated integral (`SL(2,ℂ)⁴` outside, `ℂ¹⁰` inside; finiteness of the
outer integral for coherent data is `integrable_lorOuter`); the joint integrability on the product
is a hypothesis here, which BDFHP use implicitly when they apply the stationary phase formula to the
whole integral.

## Limits

* **Joint integrability (`hjoint`) and measurability of the outer integral (`hF`) are hypotheses, not
  results.** They do not follow from `integrable_lorInner` and `integrable_lorOuter`: the inner
  integrability is per point of `SL(2,ℂ)⁵` and the outer one is the integrability of the *complex*
  inner integral `x ↦ ∫ G(x,w) dw` (the finiteness of the EPRL amplitude, which uses the decay of the
  matrix coefficients, i.e. cancellations in the sum over magnetic numbers); joint integrability is
  that of `‖G‖`, `∫ ∏_e N_e(x) dx` with `N_e(x) = ∫ ‖g_e(x, w)‖ dw`, which needs a separate estimate
  and is not proved here (the weights `e^{Re S} ≤ 1` give no decay in `x`).
* The statement is for the chart `g_0` of `SL(2,ℂ)`; the Haar density is `1` there, and the
  Jacobian of a change of chart enters when the Hessian is computed in another chart.

## Main results

* `integral_haar4_fixChart`: `∫ F d(haarC)⁴ = ∫ F(g_z(y₁), …, g_z(y₄)) dy`.
* `integral_pi_haar_eq`: the integral against `Measure.pi SL2C.haar` is `s⁻⁴` times the one against
  `Measure.pi haarC`.
* `lorVertex_eq_fixChart_integral`: the vertex as a Lebesgue integral in the fixed charts.
-/

open MeasureTheory Complex
open scoped NNReal
open Lightlike.Asymptotics.EPRL
open Lightlike.Lorentz (SL2C)

namespace Lightlike.Asymptotics.Lorentzian

/-- **The product Haar measure in the product of fixed charts**: for `F` measurable,
`∫ F d(haarC)⁴ = ∫ F(g_z(y₁), …, g_z(y₄)) dy` over `(ℂ³)⁴`. -/
theorem integral_haar4_fixChart (z : ℂ) {F : (Fin 4 → SL2C) → ℂ} (hF : AEStronglyMeasurable F
    (Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC)) :
    ∫ x, F x ∂(Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC) =
      ∫ y : Fin 4 → (Fin 3 → ℂ), F (fun a => Lightlike.Lorentz.fixChart z (y a)) := by
  have hm : ∀ _ : Fin 4, AEMeasurable (Lightlike.Lorentz.fixChart z) (volume : Measure (Fin 3 → ℂ)) :=
    fun _ => (Lightlike.Lorentz.measurable_fixChart z).aemeasurable
  have hsf : SigmaFinite ((volume : Measure (Fin 3 → ℂ)).map (Lightlike.Lorentz.fixChart z)) := by
    rw [← Lightlike.Lorentz.haarC_eq_map_fixChart z]; infer_instance
  have hmap : (Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC) =
      (Measure.pi fun _ : Fin 4 => (volume : Measure (Fin 3 → ℂ))).map
        (fun y a => Lightlike.Lorentz.fixChart z (y a)) := by
    rw [Measure.pi_map_pi (μ := fun _ : Fin 4 => (volume : Measure (Fin 3 → ℂ)))
      (f := fun _ => Lightlike.Lorentz.fixChart z) hm]
    simp only [← Lightlike.Lorentz.haarC_eq_map_fixChart z]
  have hmeas : Measurable (fun (y : Fin 4 → (Fin 3 → ℂ)) (a : Fin 4) =>
      Lightlike.Lorentz.fixChart z (y a)) :=
    Measurable.of_eval fun a => (Lightlike.Lorentz.measurable_fixChart z).comp (measurable_pi_apply a)
  rw [hmap, integral_map hmeas.aemeasurable (by rw [← hmap]; exact hF)]
  rfl

/-- The vertex integral against `Measure.pi SL2C.haar` is `s⁻⁴` times the one against `Measure.pi haarC`,
`s = haarScalarFactor haarC SL2C.haar`. -/
theorem integral_pi_haar_eq (F : (Fin 4 → SL2C) → ℂ) :
    ∫ x, F x ∂(Measure.pi fun _ : Fin 4 => SL2C.haar) =
      (((((Measure.haarScalarFactor Lightlike.Lorentz.haarC SL2C.haar) ^ 4)⁻¹ : ℝ≥0) : ℝ) : ℂ) *
        ∫ x, F x ∂(Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC) := by
  obtain ⟨s, hs⟩ : ∃ s : NNReal, s = Measure.haarScalarFactor Lightlike.Lorentz.haarC SL2C.haar := ⟨_, rfl⟩
  have hC : Lightlike.Lorentz.haarC = s • SL2C.haar := by rw [hs]; exact Lightlike.Lorentz.haarC_eq_smul
  have hs0 : s ≠ 0 := by rw [hs]; exact Lightlike.Lorentz.haarScalarFactor_haarC_ne_zero
  have hmeas : (Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC) =
      s ^ 4 • Measure.pi fun _ : Fin 4 => SL2C.haar := by
    have : (Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC) =
        Measure.pi fun _ : Fin 4 => s • SL2C.haar := by rw [hC]
    rw [this]
    exact pi_const_smul SL2C.haar s 4
  rw [← hs, hmeas, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have : ((s ^ 4 : NNReal) : ℝ) ≠ 0 := by positivity
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast this

/-- **The vertex as a Lebesgue integral in the fixed chart**: if the integrand of the vertex is
jointly integrable on `SL(2,ℂ)⁴ × ℂ¹⁰` (in the chart `g_0` of each `SL(2,ℂ)`) and the outer integral
is measurable, then
`lorVertex = (∏ c_e) s⁻⁴ ∫_{(ℂ³)⁴ × ℂ¹⁰} lorIntegrand (g_0(y₁), …, g_0(y₄), 1) w dy dw`
with `s = haarScalarFactor haarC SL2C.haar`: the Haar measure in the chart `g_0` of `FixedChart.lean`
is Lebesgue measure, with density `1` (`haarC_eq_map_fixChart`). Joint integrability is an assumption
(the vertex is defined as an iterated integral; BDFHP use the joint integral implicitly). -/
theorem lorVertex_eq_fixChart_integral (j p : Fin 10 → ℝ) (c : Fin 10 → ℂ) (g : BdryData)
    (hF : AEStronglyMeasurable (fun x : Fin 4 → SL2C => ∫ w : Fin 10 → ℂ,
      lorIntegrand j p g (Lightlike.Lorentz.gauge x) w) (Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC))
    (hjoint : Integrable (fun q : (Fin 4 → (Fin 3 → ℂ)) × (Fin 10 → ℂ) =>
      lorIntegrand j p g (Lightlike.Lorentz.gauge (fun a => Lightlike.Lorentz.fixChart 0 (q.1 a))) q.2)) :
    lorVertex j p c g = (∏ e, c e) *
      ((((((Measure.haarScalarFactor Lightlike.Lorentz.haarC SL2C.haar) ^ 4)⁻¹ : ℝ≥0) : ℝ)) : ℂ) *
        ∫ q : (Fin 4 → (Fin 3 → ℂ)) × (Fin 10 → ℂ),
          lorIntegrand j p g (Lightlike.Lorentz.gauge (fun a => Lightlike.Lorentz.fixChart 0 (q.1 a))) q.2 := by
  unfold lorVertex
  rw [integral_pi_haar_eq, integral_haar4_fixChart 0 hF, ← integral_prod _ hjoint]
  rw [mul_assoc]
  rfl

end Lightlike.Asymptotics.Lorentzian
