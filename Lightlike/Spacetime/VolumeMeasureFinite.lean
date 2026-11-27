import Mathlib
import Lightlike.Spacetime.VolumeMeasure
import Lightlike.Spacetime.EHManifold.IntrinsicAction
import Lightlike.Spacetime.EHManifold.ChartIntegrable

/-!
# The volume measure of a metric: chart form, local finiteness, positivity

For the volume measure `NondegMetric.volumeMeasure g` of a smooth nondegenerate metric `g` (any signature) on a second
countable Hausdorff manifold modelled on `ℝⁿ`:

* `NondegMetric.volumeMeasure_restrict_source`: on the domain of any chart `φ` the measure is the pushforward under `φ⁻¹`
  of `√|det g| dy` on the chart target (the library's `NondegMetric.volumeMeasure_restrict_chart` for the whole domain);
* `NondegMetric.lintegral_chart`, `NondegMetric.integral_chart`: hence
  `∫_{dom φ} f dvol_g = ∫_{φ(dom φ)} √|det g| (f ∘ φ⁻¹) dy`;
* `NondegMetric.isLocallyFiniteMeasure_volumeMeasure`, `NondegMetric.isFiniteMeasure_volumeMeasure` (on a compact
  manifold), `NondegMetric.isOpenPosMeasure_volumeMeasure`: the measure is locally finite, finite on a compact manifold,
  and positive on nonempty open sets, so `0 < vol_g(M) < ∞` for a nonempty compact manifold
  (`NondegMetric.volumeMeasure_univ_pos`, `NondegMetric.volumeMeasure_univ_lt_top`).

The chart forms reuse `NondegMetric.volumeMeasure_restrict_chart` (EHManifold/ChartAction.lean),
`NondegMetric.setIntegral_volumeMeasure_chart`, `NondegMetric.continuousOn_volDensity` (EHManifold/IntrinsicAction.lean)
and `NondegMetric.volumeMeasure_lt_top_of_isCompact` (EHManifold/ChartIntegrable.lean). These are the properties of the Riemannian measure that integration on a compact Riemannian manifold uses (the heat
trace, Green's formula). They hold for every nondegenerate metric because the density `√|det g|` is continuous and
positive on each chart target.

## References

* `rosenberg-1997`: S. Rosenberg, *The Laplacian on a Riemannian Manifold*, Cambridge University Press (1997), §1.2
  (the Riemannian measure in a chart is `√det g dx`). Comparison pending (not read at that location).
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Metric
open scoped ContDiff ENNReal Topology
noncomputable section
namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  [MeasurableSpace M] [BorelSpace M]
  (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)

omit [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M] in
/-- **The volume density is positive on the chart target** (the metric is nondegenerate). -/
theorem NondegMetric.volDensity_pos (x₀ : M) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    0 < g.volDensity x₀ y :=
  Real.sqrt_pos.2 (abs_pos.2 (g.coordMetric_isUnit_det x₀ hy).ne_zero)

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
theorem aemeasurable_extChartAt_symm (x₀ : M) {μ : Measure (Fin n → ℝ)} :
    AEMeasurable (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm (μ.restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :=
  (continuousOn_extChartAt_symm x₀).aemeasurable (isOpen_extChartAt_target x₀).measurableSet

/-- **The volume measure on a chart domain** is the pushforward under the inverse chart of `√|det g| dy` on the chart
target (`NondegMetric.volumeMeasure_restrict_chart` for the whole chart domain). -/
theorem NondegMetric.volumeMeasure_restrict_source (x₀ : M) :
    g.volumeMeasure.restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source =
      Measure.map (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm
        (((volume : Measure (Fin n → ℝ)).restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target).withDensity
          fun y => ENNReal.ofReal (g.volDensity x₀ y)) := by
  rw [NondegMetric.volumeMeasure_restrict_chart g x₀ (isOpen_extChartAt_source x₀).measurableSet subset_rfl,
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).image_source_eq_target]

/-- **Integration over a chart domain**: `∫_{dom φ} f dvol_g = ∫_{φ(dom φ)} √|det g| · (f ∘ φ⁻¹) dy`. -/
theorem NondegMetric.lintegral_chart (x₀ : M) {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source, f x ∂g.volumeMeasure =
      ∫⁻ y in (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target,
        ENNReal.ofReal (g.volDensity x₀ y) * f ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) := by
  have htgt : MeasurableSet (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    (isOpen_extChartAt_target x₀).measurableSet
  have hmeas := aemeasurable_extChartAt_symm (n := n) (μ := volume) x₀
  rw [g.volumeMeasure_restrict_source x₀,
    lintegral_map' hf.aemeasurable (hmeas.mono_ac (withDensity_absolutelyContinuous _ _))]
  exact lintegral_withDensity_eq_lintegral_mul₀
    ((NondegMetric.continuousOn_volDensity g x₀).aemeasurable htgt).ennreal_ofReal (hf.comp_aemeasurable hmeas)

/-- **Integration over a chart domain** (Bochner integral): for `F` a.e.-strongly measurable on the chart domain,
`∫_{dom φ} F dvol_g = ∫_{φ(dom φ)} √|det g| · (F ∘ φ⁻¹) dy` (`NondegMetric.setIntegral_volumeMeasure_chart` for the whole
chart domain). -/
theorem NondegMetric.integral_chart (x₀ : M) {F : M → ℝ}
    (hF : AEStronglyMeasurable F (g.volumeMeasure.restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)) :
    ∫ x in (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source, F x ∂g.volumeMeasure =
      ∫ y in (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target,
        g.volDensity x₀ y * F ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) := by
  rw [NondegMetric.setIntegral_volumeMeasure_chart g x₀ (isOpen_extChartAt_source x₀).measurableSet subset_rfl F hF,
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).image_source_eq_target]

/-- **The volume measure is locally finite.** -/
theorem NondegMetric.isLocallyFiniteMeasure_volumeMeasure : IsLocallyFiniteMeasure g.volumeMeasure := by
  refine ⟨fun x => ?_⟩
  obtain ⟨K, hKs, hKc, hKn⟩ : ∃ K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source, IsCompact K ∧ K ∈ 𝓝 x := by
    have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Fin n → ℝ) M
    obtain ⟨K, hKn, hKs, hKc⟩ := local_compact_nhds ((isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) x).mem_nhds
      (mem_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) x))
    exact ⟨K, hKs, hKc, hKn⟩
  exact ⟨K, hKn, NondegMetric.volumeMeasure_lt_top_of_isCompact g x hKc hKs⟩

/-- **On a compact manifold the volume measure is finite.** -/
theorem NondegMetric.isFiniteMeasure_volumeMeasure [CompactSpace M] : IsFiniteMeasure g.volumeMeasure := by
  have := g.isLocallyFiniteMeasure_volumeMeasure
  exact ⟨isCompact_univ.measure_lt_top (μ := g.volumeMeasure)⟩

/-- **The volume measure is positive on nonempty open sets.** -/
theorem NondegMetric.isOpenPosMeasure_volumeMeasure : g.volumeMeasure.IsOpenPosMeasure := by
  refine ⟨fun U hU hne h0 => ?_⟩
  obtain ⟨x, hx⟩ := hne
  set φ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hφ
  set S := U ∩ φ.source with hS
  have hSo : IsOpen S := hU.inter (isOpen_extChartAt_source x)
  have hSU : g.volumeMeasure S = 0 := measure_mono_null inter_subset_left h0
  rw [g.volumeMeasure_chart x hSo.measurableSet inter_subset_right] at hSU
  have hWo : IsOpen (φ '' S) := by
    rw [show φ '' S = φ.target ∩ φ.symm ⁻¹' U by
      rw [hS, inter_comm, φ.image_source_inter_eq']]
    exact (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x) hU
  have hWne : (φ '' S).Nonempty := ⟨φ x, x, ⟨hx, mem_extChartAt_source x⟩, rfl⟩
  have hWt : φ '' S ⊆ φ.target := by rintro _ ⟨p, hp, rfl⟩; exact φ.map_source hp.2
  have hae := (lintegral_eq_zero_iff' (((NondegMetric.continuousOn_volDensity g x).mono hWt).aemeasurable
    hWo.measurableSet).ennreal_ofReal).1 hSU
  have hpos : ∀ᵐ y ∂(volume.restrict (φ '' S)), 0 < ENNReal.ofReal (g.volDensity x y) :=
    (ae_restrict_mem hWo.measurableSet).mono fun y hy => ENNReal.ofReal_pos.2 (g.volDensity_pos x (hWt hy))
  have hfalse : ∀ᵐ y ∂(volume.restrict (φ '' S)), False :=
    (hae.and hpos).mono fun y hy => by simp [hy.1] at hy
  have h0' : (volume : Measure (Fin n → ℝ)).restrict (φ '' S) univ = 0 := by
    simpa using ae_iff.1 hfalse
  rw [Measure.restrict_apply_univ] at h0'
  exact (hWo.measure_pos volume hWne).ne' h0'

/-- **A nonempty compact manifold has finite volume.** -/
theorem NondegMetric.volumeMeasure_univ_lt_top [CompactSpace M] : g.volumeMeasure univ < ⊤ := by
  have := g.isFiniteMeasure_volumeMeasure; exact measure_lt_top _ _

/-- **A nonempty manifold has positive volume.** -/
theorem NondegMetric.volumeMeasure_univ_pos [Nonempty M] : 0 < g.volumeMeasure univ := by
  have := g.isOpenPosMeasure_volumeMeasure; exact isOpen_univ.measure_pos _ univ_nonempty

end Lightlike
