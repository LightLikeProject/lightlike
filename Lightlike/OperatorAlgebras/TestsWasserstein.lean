import Lightlike.OperatorAlgebras.Wasserstein

/-!
# Tests for couplings and the `1`-Wasserstein distance

* `diag_mem_couplings`, `wasserstein1_self`: the diagonal coupling of `μ` with itself has cost `0`, so `W₁(μ, μ) = 0`;
* `wasserstein1_dirac_pos`: `W₁(δₓ, δ_y) > 0` for `x ≠ y` (the distance separates Dirac measures).
-/

open MeasureTheory

namespace Lightlike.OperatorAlgebras.Transport

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The diagonal coupling `x ↦ (x, x)` of `μ` with itself. -/
lemma diag_mem_couplings (μ : Measure X) [IsProbabilityMeasure μ] :
    μ.map (fun x => (x, x)) ∈ couplings μ μ := by
  have hm : Measurable fun x : X => (x, x) := measurable_id.prodMk measurable_id
  refine ⟨(Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hm]; exact Measure.map_id
  · rw [Measure.map_map measurable_snd hm]; exact Measure.map_id

/-- **`W₁(μ, μ) = 0`.** -/
theorem wasserstein1_self (μ : Measure X) [IsProbabilityMeasure μ] : wasserstein1 μ μ = 0 := by
  have hm : Measurable fun x : X => (x, x) := measurable_id.prodMk measurable_id
  apply le_antisymm
  · have h := wasserstein1_le (diag_mem_couplings μ)
    rw [integral_map hm.aemeasurable continuous_dist.aestronglyMeasurable] at h
    simpa using h
  · have h := integral_sub_le_wasserstein1 μ μ (u := fun _ => (0 : ℝ)) ((LipschitzWith.const 0).weaken zero_le_one)
    simpa using h

/-- **`W₁(δₓ, δ_y) > 0` for `x ≠ y`.** -/
theorem wasserstein1_dirac_pos {x y : X} (hxy : x ≠ y) :
    0 < wasserstein1 (Measure.dirac x) (Measure.dirac y) := by
  rw [wasserstein1_dirac]; exact dist_pos.mpr hxy

end Lightlike.OperatorAlgebras.Transport
