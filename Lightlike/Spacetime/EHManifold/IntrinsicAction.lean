import Lightlike.Spacetime.ChartAgreement
import Lightlike.Spacetime.Coordinates
import Lightlike.Spacetime.EHManifold.ChartAction
import Lightlike.Spacetime.EHManifold.ChartVariation

/-!
# The Einstein–Hilbert action of a region inside one chart

* `NondegMetric.setIntegral_volumeMeasure_chart`: for a measurable `K` inside the domain of the chart at `x₀`,
  `∫_K f d vol_g = ∫_{φ(K)} √|det g| · (f ∘ φ⁻¹) dy`, with `φ` the chart and `g` its components.
* `eh_action_chart`: for a Levi-Civita connection `cov` of `g`, the Einstein–Hilbert action of `K`,
  `∫_K (R - 2Λ) d vol_g` with `R` the scalar curvature of `cov`, is the chart integral of the coordinate
  Lagrangian density `lagDensity (g.coordMetric x₀) 0 Λ 0 = √|det g| (R - 2Λ)` over the chart image of `K`.

Supporting lemmas for the Einstein–Hilbert variation on a manifold; no catalogue entry.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)

/-- The volume density of the chart components is continuous on the target of the chart. -/
lemma NondegMetric.continuousOn_volDensity (x₀ : M) :
    ContinuousOn (NondegMetric.volDensity g x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
  have hc := g.isCoordMetric_coordMetric x₀
  have hm : ContinuousOn (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hc.smooth i j).continuousOn
  have hd : ContinuousOn (fun y => (g.coordMetric x₀ y).det) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    (Continuous.matrix_det continuous_id).comp_continuousOn hm
  exact Real.continuous_sqrt.comp_continuousOn (continuous_abs.comp_continuousOn hd)

/-- **Integration for the volume measure in one chart.** -/
theorem NondegMetric.setIntegral_volumeMeasure_chart (x₀ : M) {K : Set M} (hK : MeasurableSet K)
    (hK0 : K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (f : M → ℝ)
    (hf : AEStronglyMeasurable f ((NondegMetric.volumeMeasure g).restrict K)) :
    ∫ p in K, f p ∂(NondegMetric.volumeMeasure g) =
      ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K,
        NondegMetric.volDensity g x₀ y * f ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) := by
  have hsub : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
    rintro _ ⟨p, hp, rfl⟩
    exact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (hK0 hp)
  have hT : MeasurableSet (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    (isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x₀).measurableSet
  have hdens : AEMeasurable (fun y => ENNReal.ofReal (NondegMetric.volDensity g x₀ y))
      ((volume : Measure (Fin n → ℝ)).restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K)) :=
    (((NondegMetric.continuousOn_volDensity g x₀).aemeasurable hT).mono_measure
      (Measure.restrict_mono hsub le_rfl)).ennreal_ofReal
  have hae : AEMeasurable (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm
      (((volume : Measure (Fin n → ℝ)).restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K)).withDensity
        fun y => ENNReal.ofReal (NondegMetric.volDensity g x₀ y)) :=
    ((((continuousOn_extChartAt_symm x₀).aemeasurable hT).mono_measure
      (Measure.restrict_mono hsub le_rfl))).mono_ac (withDensity_absolutelyContinuous _ _)
  have hμ := NondegMetric.volumeMeasure_restrict_chart g x₀ hK hK0
  rw [hμ] at hf ⊢
  rw [integral_map hae hf, integral_withDensity_eq_integral_toReal_smul₀ hdens
    (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show (ENNReal.ofReal (NondegMetric.volDensity g x₀ y)).toReal •
      f ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) =
    NondegMetric.volDensity g x₀ y * f ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
  have hnn : 0 ≤ NondegMetric.volDensity g x₀ y := Real.sqrt_nonneg _
  rw [ENNReal.toReal_ofReal hnn, smul_eq_mul]

variable (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-- **The Einstein–Hilbert action of a region inside one chart** is the chart integral of the coordinate
Lagrangian density of the components of the metric. -/
theorem eh_action_chart (hLC : cov.IsLeviCivita g) (x₀ : M) {K : Set M} (hK : MeasurableSet K)
    (hK0 : K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (Λ : ℝ)
    (hf : AEStronglyMeasurable (fun p => cov.scalarCurvatureAt g p - 2 * Λ)
      ((NondegMetric.volumeMeasure g).restrict K)) :
    ∫ p in K, (cov.scalarCurvatureAt g p - 2 * Λ) ∂(NondegMetric.volumeMeasure g) =
      ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, lagDensity (g.coordMetric x₀) 0 Λ 0 y := by
  rw [NondegMetric.setIntegral_volumeMeasure_chart g x₀ hK hK0 _ hf]
  refine setIntegral_congr_fun (measurableSet_image_extChartAt x₀ hK hK0) fun y hy => ?_
  obtain ⟨p, hp, rfl⟩ := hy
  have hyt : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (hK0 hp)
  show NondegMetric.volDensity g x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) *
      (cov.scalarCurvatureAt g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p)) -
        2 * Λ) = lagDensity (g.coordMetric x₀) 0 Λ 0 (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p)
  rw [scalarCurvatureAt_coord cov x₀ g hLC hyt]
  simp [lagDensity, NondegMetric.volDensity]

end Lightlike
