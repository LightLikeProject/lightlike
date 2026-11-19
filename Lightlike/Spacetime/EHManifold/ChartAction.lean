import Lightlike.Spacetime.VolumeMeasure

/-!
# The volume measure of a metric in one chart

`NondegMetric.volumeMeasure_restrict_chart`: on a measurable set `K` inside the domain of the chart at `x₀`,
the volume measure of a metric is the image under the inverse chart of the measure `√|det g| dy` on the chart
image of `K`. This is `NondegMetric.volumeMeasure_chart` (the value on every measurable subset) as an
identity of measures; it turns integrals over `K` for the volume measure into chart integrals.

Supporting lemma for the Einstein–Hilbert variation on a manifold; no catalogue entry.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)

/-- The chart image of `A ∩ K` is the part of the chart image of `K` that the inverse chart maps into `A`. -/
lemma image_inter_eq_preimage_inter (x₀ : M) {K : Set M}
    (hK0 : K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (A : Set M) :
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm ⁻¹' A ∩ extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K =
      extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' (A ∩ K) := by
  ext y
  constructor
  · rintro ⟨hyA, p, hpK, rfl⟩
    have hp : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) = p :=
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv (hK0 hpK)
    refine ⟨p, ⟨?_, hpK⟩, rfl⟩
    have h : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) ∈ A := hyA
    rwa [hp] at h
  · rintro ⟨p, ⟨hpA, hpK⟩, rfl⟩
    have hp : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) = p :=
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv (hK0 hpK)
    refine ⟨?_, p, hpK, rfl⟩
    show (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) ∈ A
    rw [hp]
    exact hpA

/-- **The volume measure in one chart**, as an identity of measures: on a measurable `K` inside the domain of
the chart at `x₀`, it is the image under the inverse chart of `√|det g| dy` on the chart image of `K`. -/
theorem NondegMetric.volumeMeasure_restrict_chart (x₀ : M) {K : Set M} (hK : MeasurableSet K)
    (hK0 : K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    (NondegMetric.volumeMeasure g).restrict K =
      Measure.map (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm
        (((volume : Measure (Fin n → ℝ)).restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K)).withDensity
          fun y => ENNReal.ofReal (NondegMetric.volDensity g x₀ y)) := by
  have hKm : MeasurableSet (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K) :=
    measurableSet_image_extChartAt x₀ hK hK0
  have hsub : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
    rintro _ ⟨p, hp, rfl⟩
    exact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (hK0 hp)
  have hT : MeasurableSet (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    (isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x₀).measurableSet
  have hae0 : AEMeasurable (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm
      ((volume : Measure (Fin n → ℝ)).restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :=
    (continuousOn_extChartAt_symm x₀).aemeasurable hT
  have hae : AEMeasurable (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm
      (((volume : Measure (Fin n → ℝ)).restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K)).withDensity
        fun y => ENNReal.ofReal (NondegMetric.volDensity g x₀ y)) :=
    (hae0.mono_measure (Measure.restrict_mono hsub le_rfl)).mono_ac
      (withDensity_absolutelyContinuous _ _)
  refine Measure.ext fun A hA => ?_
  rw [Measure.restrict_apply hA, Measure.map_apply_of_aemeasurable hae hA, withDensity_apply',
    Measure.restrict_restrict' hKm, image_inter_eq_preimage_inter x₀ hK0 A]
  exact NondegMetric.volumeMeasure_chart g x₀ (hA.inter hK) (inter_subset_right.trans hK0)

end Lightlike
