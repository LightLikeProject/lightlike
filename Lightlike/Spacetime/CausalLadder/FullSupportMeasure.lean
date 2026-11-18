import Lightlike.Spacetime.VolumeMeasure
import Lightlike.Spacetime.Coordinates

/-!
# A finite measure of full support on a Lorentzian manifold

On a second-countable Hausdorff manifold modelled on `ℝⁿ` with a Lorentzian metric `g`, the volume
measure `volumeMeasure g` (`Lightlike/Spacetime/VolumeMeasure.lean`) is positive on every nonempty
open set (`volumeMeasure_pos_of_isOpen`: in a chart it is the integral of `√|det g|`, which is
positive and continuous because `g` is nondegenerate and smooth). It is s-finite, so there is a finite
measure with the same null sets (Mathlib: `Measure.exists_isFiniteMeasure_absolutelyContinuous`); it
is positive on nonempty open sets and has the same null sets as the volume measure
(`exists_finite_fullSupport_measure`). This is the measure of Hawking's time function for task
`T-GE2-P11` (`x ↦ μ(J⁻(x))`).

Supporting lemmas for the causal ladder; no catalogue entry.
-/

open MeasureTheory Set Manifold TopologicalSpace Filter
open scoped ContDiff ENNReal Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)

/-- The volume density `√|det g|` is positive on the chart target (`g` is nondegenerate). -/
theorem volDensity_pos (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) : 0 < volDensity g x₀ y := by
  have hdet := g.coordMetric_isUnit_det x₀ hy
  unfold volDensity NondegMetric.volDensity
  rw [NondegMetric.ofLorentzian_coordMetric]
  exact Real.sqrt_pos.2 (abs_pos.2 hdet.ne_zero)

/-- The volume density is continuous on the chart target. -/
theorem continuousOn_volDensity (x₀ : M) :
    ContinuousOn (volDensity g x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
  have hentry : ∀ i j, ContinuousOn (fun y => g.coordMetric x₀ y i j)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := fun i j =>
    (g.coordMetric_smooth x₀ i j).continuousOn
  have hdet : ContinuousOn (fun y => (g.coordMetric x₀ y).det)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
    have : ContinuousOn (fun y => g.coordMetric x₀ y) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
      continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hentry i j
    exact (Continuous.comp_continuousOn (continuous_id.matrix_det) this)
  unfold volDensity NondegMetric.volDensity
  simp only [NondegMetric.ofLorentzian_coordMetric]
  exact (hdet.abs).sqrt

/-- **The volume measure is positive on nonempty open sets.** -/
theorem volumeMeasure_pos_of_isOpen {O : Set M} (hO : IsOpen O) (hne : O.Nonempty) :
    0 < volumeMeasure g O := by
  obtain ⟨x, hx⟩ := hne
  set φ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hφ
  set B : Set M := O ∩ φ.source with hB
  have hBopen : IsOpen B := hO.inter (isOpen_extChartAt_source x)
  have hxB : x ∈ B := ⟨hx, mem_extChartAt_source x⟩
  have hBsub : B ⊆ φ.source := inter_subset_right
  have himg : φ '' B = φ.target ∩ φ.symm ⁻¹' B := φ.image_eq_target_inter_inv_preimage hBsub
  have himgOpen : IsOpen (φ '' B) := by
    rw [himg]
    exact (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x) hBopen
  have hmem : φ x ∈ φ '' B := ⟨x, hxB, rfl⟩
  have hdens := continuousOn_volDensity g x
  have hpos : ∀ y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target, 0 < volDensity g x y :=
    fun y hy => volDensity_pos g x hy
  have hy0 : φ x ∈ φ.target := φ.map_source (mem_extChartAt_source x)
  -- a small ball in the image where the density is at least half its value at `φ x`
  set c : ℝ := volDensity g x (φ x) / 2 with hc
  have hcpos : 0 < c := by have := hpos _ hy0; positivity
  have hca : ContinuousAt (volDensity g x) (φ x) :=
    hdens.continuousAt ((isOpen_extChartAt_target x).mem_nhds hy0)
  have hev : ∀ᶠ y in 𝓝 (φ x), c < volDensity g x y :=
    hca.eventually (lt_mem_nhds (by have := hpos _ hy0; linarith))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem hev (himgOpen.mem_nhds hmem))
  have hrB : Metric.ball (φ x) r ⊆ φ '' B := fun y hy => (hball hy).2
  have hmeasB : MeasurableSet B := hBopen.measurableSet
  have hvol := volumeMeasure_chart g x hmeasB hBsub
  calc (0 : ℝ≥0∞) < ENNReal.ofReal c * volume (Metric.ball (φ x) r) := by
        refine ENNReal.mul_pos (by simpa using hcpos) ?_
        exact (Metric.measure_ball_pos volume (φ x) hr).ne'
    _ = ∫⁻ y in Metric.ball (φ x) r, ENNReal.ofReal c := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ y in Metric.ball (φ x) r, ENNReal.ofReal (volDensity g x y) :=
        setLIntegral_mono' Metric.isOpen_ball.measurableSet fun y hy =>
          ENNReal.ofReal_le_ofReal (hball hy).1.le
    _ ≤ ∫⁻ y in φ '' B, ENNReal.ofReal (volDensity g x y) := lintegral_mono_set hrB
    _ = volumeMeasure g B := hvol.symm
    _ ≤ volumeMeasure g O := measure_mono inter_subset_left

/-- The volume measure is s-finite (a countable sum of pushforwards of s-finite measures). -/
instance : SFinite (volumeMeasure g) := by
  unfold volumeMeasure NondegMetric.volumeMeasure
  infer_instance

/-- **A finite measure of full support with the null sets of the volume measure.** On a
second-countable Hausdorff manifold modelled on `ℝⁿ` with a Lorentzian metric there is a finite Borel
measure `ν`, positive on every nonempty open set, with `ν ≪ volumeMeasure g` and
`volumeMeasure g ≪ ν`. -/
theorem exists_finite_fullSupport_measure :
    ∃ ν : Measure M, IsFiniteMeasure ν ∧ (∀ O : Set M, IsOpen O → O.Nonempty → 0 < ν O) ∧
      ν ≪ volumeMeasure g ∧ volumeMeasure g ≪ ν := by
  obtain ⟨ν, hfin, h1, h2⟩ := exists_isFiniteMeasure_absolutelyContinuous (volumeMeasure g)
  refine ⟨ν, hfin, fun O hO hne => ?_, h2, h1⟩
  by_contra hzero
  have hz : ν O = 0 := le_antisymm (not_lt.1 hzero) zero_le
  exact (volumeMeasure_pos_of_isOpen g hO hne).ne' (h1 hz)

end Lightlike
