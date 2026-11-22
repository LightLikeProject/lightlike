import Lightlike.SpinFoam.VertexAsymptoticsHyp.DensityBound
import Lightlike.Asymptotics.Lorentzian.InnerIntegrable
import Lightlike.Asymptotics.Lorentzian.VertexFixChart
import Lightlike.Lorentz.FixedChart

/-!
# The Lorentzian vertex integrand is jointly integrable on `SL(2,ℂ)^4 × ℂ^10` (Haar-chart measure)

Third step of the joint integrability of the vertex integrand (task T-SF10-P1). With
`D(x, w) = ∏_e lorEdgeDensity (gauge x) (lorSpinor ∘ w) e`:

* `integrable_vertexDensity_prod`: `D` is integrable for `haar4 ⊗ volume` (Tonelli: the `ℂ^10`
  integral is a product of ten kernels `I` by `integral_vertexDensity`, integrable by
  `integrable_kernelProd_gauge`);
* `ae_overlaps`: for `haar4 ⊗ volume`-almost every `(x, w)` no overlap of the integrand vanishes;
* `integrable_lorIntegrand_haar4`: so `‖lorIntegrand‖ ≤ D` (`norm_lorIntegrand_le`) almost
  everywhere, and the integrand is integrable for `haar4 ⊗ volume`.
-/

open MeasureTheory Matrix
open scoped ENNReal NNReal
open Lightlike Lightlike.Lorentz Lightlike.Asymptotics.EPRL

namespace Lightlike.Asymptotics.Lorentzian

/-- **For fixed `X` the modulus bound is integrable on `ℂ^10`**: a product of ten integrable
functions of one variable. -/
theorem integrable_vertexDensity_inner (X : Fin 5 → SL2C) :
    Integrable (fun w : Fin 10 → ℂ => ∏ e, lorEdgeDensity X (fun e => lorSpinor (w e)) e) volume := by
  have h := Integrable.fintype_prod (ι := Fin 10) (μ := fun _ : Fin 10 => (volume : Measure ℂ))
    (f := fun (e : Fin 10) (w' : ℂ) => lorEdgeDensity X (fun _ => lorSpinor w') e)
    (fun e => integrable_lorEdgeDensity (X (edgeSrc e)) (X (edgeTgt e)))
  rw [← volume_pi] at h
  exact h

/-- The modulus bound is measurable in `(x, w)`. -/
theorem measurable_vertexDensity :
    Measurable fun q : (Fin 4 → SL2C) × (Fin 10 → ℂ) =>
      ∏ e, lorEdgeDensity (gauge q.1) (fun e => lorSpinor (q.2 e)) e := by
  refine Finset.measurable_prod _ fun e _ => ?_
  unfold lorEdgeDensity
  refine Measurable.inv (Measurable.mul ?_ ?_)
  · exact ((continuous_nodeSpinor (edgeSrc e) e).norm.pow 2).measurable
  · exact ((continuous_nodeSpinor (edgeTgt e) e).norm.pow 2).measurable

/-- The modulus bound is nonnegative. -/
theorem vertexDensity_nonneg (X : Fin 5 → SL2C) (w : Fin 10 → ℂ) :
    0 ≤ ∏ e, lorEdgeDensity X (fun e => lorSpinor (w e)) e :=
  Finset.prod_nonneg fun e _ => by unfold lorEdgeDensity; positivity

/-- **The modulus bound is integrable on `SL(2,ℂ)^4 × ℂ^10`** for `haar4 ⊗ volume`. -/
theorem integrable_vertexDensity_prod :
    Integrable (fun q : (Fin 4 → SL2C) × (Fin 10 → ℂ) =>
      ∏ e, lorEdgeDensity (gauge q.1) (fun e => lorSpinor (q.2 e)) e) (haar4.prod volume) := by
  rw [integrable_prod_iff measurable_vertexDensity.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
  · exact integrable_vertexDensity_inner (gauge x)
  refine integrable_kernelProd_gauge.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← integral_vertexDensity]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  rw [Real.norm_of_nonneg (vertexDensity_nonneg _ _)]

/-- **No overlap vanishes almost everywhere on `SL(2,ℂ)^4 × ℂ^10`.** -/
theorem ae_overlaps {g : BdryData}
    (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1) (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1) :
    ∀ᵐ q ∂(haar4.prod (volume : Measure (Fin 10 → ℂ))),
      (∀ e, inner ℂ (spinAct (gauge q.1 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
        (lorSpinor (q.2 e))) (firstCol (g e 0)) ≠ 0) ∧
      (∀ e, inner ℂ (jMap (firstCol (g e 1)))
        (spinAct (gauge q.1 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor (q.2 e))) ≠ 0) := by
  have hc1 : ∀ e, Continuous fun q : (Fin 4 → SL2C) × (Fin 10 → ℂ) =>
      inner ℂ (spinAct (gauge q.1 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
        (lorSpinor (q.2 e))) (firstCol (g e 0)) :=
    fun e => (continuous_nodeSpinor (edgeSrc e) e).inner continuous_const
  have hc2 : ∀ e, Continuous fun q : (Fin 4 → SL2C) × (Fin 10 → ℂ) =>
      inner ℂ (jMap (firstCol (g e 1)))
        (spinAct (gauge q.1 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor (q.2 e))) :=
    fun e => continuous_const.inner (continuous_nodeSpinor (edgeTgt e) e)
  have hopen : IsOpen {q : (Fin 4 → SL2C) × (Fin 10 → ℂ) | (∀ e, inner ℂ
      (spinAct (gauge q.1 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
        (lorSpinor (q.2 e))) (firstCol (g e 0)) ≠ 0) ∧
      (∀ e, inner ℂ (jMap (firstCol (g e 1)))
        (spinAct (gauge q.1 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor (q.2 e))) ≠ 0)} := by
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact (isOpen_iInter_of_finite fun e => isOpen_ne_fun (hc1 e) continuous_const).inter
      (isOpen_iInter_of_finite fun e => isOpen_ne_fun (hc2 e) continuous_const)
  rw [Measure.ae_prod_iff_ae_ae hopen.measurableSet]
  refine Filter.Eventually.of_forall fun x => ?_
  have h1 : ∀ e : Fin 10, ∀ᵐ w : Fin 10 → ℂ,
      inner ℂ (spinAct (gauge x (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
        (lorSpinor (w e))) (firstCol (g e 0)) ≠ 0 := fun e => by
    have hne : firstCol (g e 0) ≠ 0 := fun h => by have := hξ e; simp [h] at this
    exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin 10 => (volume : Measure ℂ)) e).ae
      (ae_overlap_src _ (gauge x (edgeSrc e)).2 hne)
  have h2 : ∀ e : Fin 10, ∀ᵐ w : Fin 10 → ℂ,
      inner ℂ (jMap (firstCol (g e 1)))
        (spinAct (gauge x (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor (w e))) ≠ 0 := fun e => by
    have hne : firstCol (g e 1) ≠ 0 := fun h => by have := hξ' e; simp [h] at this
    exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin 10 => (volume : Measure ℂ)) e).ae
      (ae_overlap_tgt _ (gauge x (edgeTgt e)).2 hne)
  filter_upwards [ae_all_iff.2 h1, ae_all_iff.2 h2] with w a b
  exact ⟨a, b⟩

/-- **The vertex integrand is integrable on `SL(2,ℂ)^4 × ℂ^10` for `haar4 ⊗ volume`**, for
unit boundary spinors and nonnegative spins (it is dominated by the modulus bound). -/
theorem integrable_lorIntegrand_haar4 {j p : Fin 10 → ℝ} (hj : ∀ e, 0 ≤ j e) {g : BdryData}
    (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1) (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1) :
    Integrable (fun q : (Fin 4 → SL2C) × (Fin 10 → ℂ) => lorIntegrand j p g (gauge q.1) q.2)
      (haar4.prod volume) := by
  refine integrable_vertexDensity_prod.mono' (measurable_lorIntegrand j p g).aestronglyMeasurable ?_
  filter_upwards [ae_overlaps hξ hξ'] with q hq
  exact norm_lorIntegrand_le hj hξ hξ' hq.1 hq.2

/-- The fixed-chart coordinates `ℂ^3 → SL(2,ℂ)` on the four free variables, identity on `ℂ^10`. -/
noncomputable def chartPair (q : (Fin 4 → (Fin 3 → ℂ)) × (Fin 10 → ℂ)) :
    (Fin 4 → SL2C) × (Fin 10 → ℂ) :=
  (fun a => fixChart 0 (q.1 a), q.2)

theorem measurable_chartPair : Measurable chartPair :=
  (measurable_pi_iff.mpr fun a => (measurable_fixChart 0).comp
    ((measurable_pi_apply a).comp measurable_fst)).prodMk measurable_snd

/-- **The Haar-chart measure is the Lebesgue measure transported by the fixed charts.** -/
theorem haar4_prod_eq_map_chartPair :
    haar4.prod (volume : Measure (Fin 10 → ℂ)) =
      (volume : Measure ((Fin 4 → (Fin 3 → ℂ)) × (Fin 10 → ℂ))).map chartPair := by
  have hsf : ∀ _ : Fin 4, SigmaFinite ((volume : Measure (Fin 3 → ℂ)).map (fixChart 0)) := by
    intro _; rw [← haarC_eq_map_fixChart 0]; infer_instance
  have h1 : haar4 = (volume : Measure (Fin 4 → (Fin 3 → ℂ))).map
      (fun x a => fixChart 0 (x a)) := by
    rw [volume_pi, Measure.pi_map_pi (f := fun _ : Fin 4 => fixChart 0) (hμ := hsf)
      (fun _ => (measurable_fixChart 0).aemeasurable)]
    unfold haar4
    simp only [haarC_eq_map_fixChart 0]
  have hm : Measurable (fun (x : Fin 4 → (Fin 3 → ℂ)) a => fixChart 0 (x a)) :=
    measurable_pi_iff.mpr fun a => (measurable_fixChart 0).comp (measurable_pi_apply a)
  have h2 := Measure.map_prod_map (volume : Measure (Fin 4 → (Fin 3 → ℂ)))
    (volume : Measure (Fin 10 → ℂ)) hm (g := id) measurable_id
  rw [Measure.map_id] at h2
  rw [h1, h2, Measure.volume_eq_prod]
  rfl

/-- **Joint integrability in the fixed charts** (Lebesgue measure on `(ℂ^3)^4 × ℂ^10`), for unit
boundary spinors and nonnegative spins. -/
theorem integrable_lorIntegrand_chart {j p : Fin 10 → ℝ} (hj : ∀ e, 0 ≤ j e) {g : BdryData}
    (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1) (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1) :
    Integrable (fun q : (Fin 4 → (Fin 3 → ℂ)) × (Fin 10 → ℂ) =>
      lorIntegrand j p g (gauge (fun a => fixChart 0 (q.1 a))) q.2) volume := by
  have h := integrable_lorIntegrand_haar4 (p := p) hj hξ hξ'
  rw [haar4_prod_eq_map_chartPair] at h
  exact (integrable_map_measure (measurable_lorIntegrand j p g).aestronglyMeasurable
    measurable_chartPair.aemeasurable).mp h

/-- **P1**: joint integrability of the vertex integrand (the hypothesis `VertexJointIntegrable`). -/
theorem vertexJointIntegrable_of_unit {j p : Fin 10 → ℝ} (hj : ∀ k, 0 < j k) {g : BdryData}
    (hξ : ∀ k, ‖firstCol (g k 0)‖ = 1) (hξ' : ∀ k, ‖firstCol (g k 1)‖ = 1) :
    VertexJointIntegrable j p g := by
  intro lam
  have hl : ∀ e, 0 ≤ (lam : ℝ) * j e := fun e => mul_nonneg (Nat.cast_nonneg _) (hj e).le
  refine ⟨?_, integrable_lorIntegrand_chart hl hξ hξ'⟩
  exact (integrable_lorIntegrand_haar4 (p := fun k => (lam : ℝ) * p k) hl hξ hξ').integral_prod_left.aestronglyMeasurable

end Lightlike.Asymptotics.Lorentzian
