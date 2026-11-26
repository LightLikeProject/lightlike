import Mathlib
import Lightlike.Geometry.FlatTorus
import Lightlike.Geometry.FlatTorusMetric

/-!
# Tests: the flat torus as a manifold modelled on `ℝⁿ`

Non-vacuity: `FlatTorus 2` carries the instances the volume and Laplacian layers ask for (smooth manifold modelled on
`𝓘(ℝ, Fin 2 → ℝ)`, compact, Hausdorff, second countable). Trust check: the circle chart cut at `0` sends the class of
`3/2` to its representative `1/2` in `(0, 1)`; a chart that forgot to reduce modulo `1` (returning `3/2`) is caught.
The flat metric `FlatTorus.flatMetric` has the identity matrix as coordinate metric at the centre of a chart; a metric
scaled by `2` (the circle of radius `1/π` instead of `1/2π`) would give `2` there and is caught.
-/

open Set Manifold
open scoped ContDiff
noncomputable section
namespace Lightlike.FlatTorusTests

example : IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (FlatTorus 2) := inferInstance
example : CompactSpace (FlatTorus 2) := inferInstance
example : T2Space (FlatTorus 2) := inferInstance
example : SecondCountableTopology (FlatTorus 2) := inferInstance

/-- The circle chart cut at `0` reduces `3/2` to `1/2`. -/
theorem circleChart_three_halves : FlatTorus.circleChart 0 ((3 / 2 : ℝ) : AddCircle (1 : ℝ)) = 1 / 2 := by
  rw [FlatTorus.circleChart_coe, toIcoMod_eq_iff]
  refine ⟨⟨by norm_num, by norm_num⟩, 1, by norm_num⟩

/-- A chart without the reduction modulo `1` would return `3/2`: caught. -/
example : FlatTorus.circleChart 0 ((3 / 2 : ℝ) : AddCircle (1 : ℝ)) ≠ 3 / 2 := by
  rw [circleChart_three_halves]; norm_num

/-- The coordinate metric of the flat torus at the centre of the chart at `x₀` is the identity. -/
example (x₀ : FlatTorus 2) :
    (FlatTorus.flatMetric 2).coordMetric x₀ (extChartAt 𝓘(ℝ, Fin 2 → ℝ) x₀ x₀) = 1 :=
  FlatTorus.coordMetric_flatMetric x₀ (mem_extChartAt_target x₀)

/-- A metric twice as large would have `g₀₀ = 2`: caught. -/
example (x₀ : FlatTorus 2) :
    (FlatTorus.flatMetric 2).coordMetric x₀ (extChartAt 𝓘(ℝ, Fin 2 → ℝ) x₀ x₀) 0 0 ≠ 2 := by
  rw [FlatTorus.coordMetric_flatMetric x₀ (mem_extChartAt_target x₀)]; simp

end Lightlike.FlatTorusTests
