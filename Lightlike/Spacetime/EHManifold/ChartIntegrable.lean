import Lightlike.Spacetime.EHManifold.IntrinsicAction

/-!
# Compact sets inside a chart have finite volume, and continuous functions are integrable on them

* `NondegMetric.volumeMeasure_lt_top_of_isCompact`: a compact set inside one chart domain has finite volume
  for the volume measure of a metric.
* `NondegMetric.integrableOn_of_continuousOn`: a function continuous on such a compact set `T` is integrable
  on every measurable subset of `T`.

Supporting lemmas for the Einstein–Hilbert variation on a manifold; no catalogue entry.
-/

open MeasureTheory Set Manifold TopologicalSpace
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)

/-- A compact set inside one chart domain has finite volume. -/
theorem NondegMetric.volumeMeasure_lt_top_of_isCompact (x₀ : M) {T : Set M} (hT : IsCompact T)
    (hT0 : T ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    NondegMetric.volumeMeasure g T < ∞ := by
  have hTc : IsCompact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T) :=
    hT.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hT0)
  have hsub : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
    rintro _ ⟨p, hp, rfl⟩
    exact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (hT0 hp)
  have hint : IntegrableOn (NondegMetric.volDensity g x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T) volume :=
    ((NondegMetric.continuousOn_volDensity g x₀).mono hsub).integrableOn_compact hTc
  rw [NondegMetric.volumeMeasure_chart g x₀ hT.measurableSet hT0]
  exact hint.setLIntegral_lt_top

/-- A function continuous on a compact set `T` inside one chart domain is integrable, for the volume
measure of a metric, on every measurable subset of `T`. -/
theorem NondegMetric.integrableOn_of_continuousOn (x₀ : M) {T A : Set M} (hT : IsCompact T)
    (hT0 : T ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) {f : M → ℝ} (hf : ContinuousOn f T)
    (hAT : A ⊆ T) : IntegrableOn f A (NondegMetric.volumeMeasure g) := by
  obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn hf
  have hTint : IntegrableOn f T (NondegMetric.volumeMeasure g) :=
    ⟨hf.aestronglyMeasurable hT.measurableSet,
      HasFiniteIntegral.restrict_of_bounded (C := C)
        (NondegMetric.volumeMeasure_lt_top_of_isCompact g x₀ hT hT0)
        ((ae_restrict_iff' hT.measurableSet).2 (Filter.Eventually.of_forall hC))⟩
  exact hTint.mono_set hAT

end Lightlike
