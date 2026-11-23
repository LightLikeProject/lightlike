import Lightlike.SpinFoam.VertexAsymptoticsHyp.JointIntegrable

/-!
# Integrability of the far-remainder integrand (first half of task T-SF10-P6)

The chart integrand `a(x) e^{λ S(x)}` of the scaled vertex is integrable on `ℝ⁴⁴` for every real
`λ ≥ 0` (including `λ = 0`, where it is the amplitude `a` itself), and so is `(1 - ψ) a e^{λ S}` for
a cutoff `0 ≤ ψ ≤ 1`. The majorant is `∏_e lorEdgeDensity`, integrable by
`integrable_vertexDensity_prod`; no decay of `a` is assumed.
-/

open MeasureTheory
open Lightlike Lightlike.Lorentz Lightlike.Asymptotics.EPRL

namespace Lightlike.Asymptotics.Lorentzian

/-- **The chart integrand `a e^{λ S}` is integrable on `ℝ⁴⁴`** for every `λ ≥ 0`, unit boundary
spinors and nonnegative spins. -/
theorem integrable_chartIntegrand
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ)))
    (he : MeasurePreserving e volume volume) {j p : Fin 10 → ℝ} (hj : ∀ k, 0 ≤ j k) {g : BdryData}
    (hξ : ∀ k, ‖firstCol (g k 0)‖ = 1) (hξ' : ∀ k, ‖firstCol (g k 1)‖ = 1) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    Integrable (fun x : Fin 44 → ℝ => chartAmplitude e x *
      Complex.exp ((lam : ℂ) * lorChartAction j p g (fixVertexChart e) x)) volume := by
  have hl : ∀ k, 0 ≤ lam * j k := fun k => mul_nonneg hlam (hj k)
  have h := integrable_lorIntegrand_chart (p := fun k => lam * p k) hl hξ hξ'
  have h2 := (he.integrable_comp_emb e.measurableEmbedding).mpr h
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp, lorIntegrand, chartAmplitude, lorChartAction, fixVertexChart,
    lorAction_smul]
  ring

/-- **The cut-off integrand `(1 - ψ) a e^{λ S}` is integrable** (`0 ≤ ψ ≤ 1` measurable). -/
theorem integrable_tailIntegrand
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ)))
    (he : MeasurePreserving e volume volume) {j p : Fin 10 → ℝ} (hj : ∀ k, 0 ≤ j k) {g : BdryData}
    (hξ : ∀ k, ‖firstCol (g k 0)‖ = 1) (hξ' : ∀ k, ‖firstCol (g k 1)‖ = 1)
    (ψ : (Fin 44 → ℝ) → ℝ) (hψ : Measurable ψ) (hψ01 : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (lam : ℕ) :
    Integrable (fun x => (((1 - ψ x : ℝ) : ℂ) * chartAmplitude e x) *
      Complex.exp ((lam : ℝ) * lorChartAction j p g (fixVertexChart e) x)) volume := by
  have h := integrable_chartIntegrand e he hj hξ hξ' (lam : ℝ) (Nat.cast_nonneg _) (p := p)
  refine h.norm.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · have hm : Measurable fun x : Fin 44 → ℝ => (((1 - ψ x : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (measurable_const.sub hψ)
    have := (hm.aestronglyMeasurable.mul h.aestronglyMeasurable)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]
    push_cast
    ring
  · rw [norm_mul, norm_mul, norm_mul]
    have h1 : ‖(((1 - ψ x : ℝ) : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hψ01 x]
    have hn : 0 ≤ ‖chartAmplitude e x‖ * ‖Complex.exp ((lam : ℝ) *
        lorChartAction j p g (fixVertexChart e) x)‖ := by positivity
    push_cast at *
    calc _ ≤ 1 * (‖chartAmplitude e x‖ * ‖Complex.exp ((lam : ℂ) *
        lorChartAction j p g (fixVertexChart e) x)‖) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right h1 hn
      _ = _ := by rw [one_mul]

end Lightlike.Asymptotics.Lorentzian
