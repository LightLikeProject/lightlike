import Mathlib
import Lightlike.Spacetime.VolumeMeasure
import Lightlike.Spacetime.RiemannSymmetry

/-!
# Smoothness of the inverse metric and of the volume density in a chart

For a smooth nondegenerate metric `g` on a manifold modelled on `ℝⁿ`, on the target of the chart at `x₀`:

* `NondegMetric.contDiffOn_coordMetric_det`, `NondegMetric.contDiffOn_coordMetric_inv`: the determinant and the inverse
  metric `g^{ij}` are smooth (the library's `contDiffOn_det_of_entries` and `IsCoordMetric.contDiffOn_inv`, applied to
  `NondegMetric.isCoordMetric_coordMetric`);
* `NondegMetric.contDiffOn_volDensity`: the density `√|det g|` is smooth (the determinant does not vanish).

These are the coefficients of the Laplace–Beltrami operator `|g|^{-1/2} ∂ᵢ(|g|^{1/2} g^{ij} ∂ⱼ)`.
-/

open Set Manifold Matrix
open scoped ContDiff
noncomputable section
namespace Lightlike

variable {n : ℕ}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  [MeasurableSpace M] [BorelSpace M]
  (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)

/-- **The coordinate determinant of the metric is smooth on the chart target.** -/
theorem NondegMetric.contDiffOn_coordMetric_det (x₀ : M) :
    ContDiffOn ℝ ∞ (fun y => (g.coordMetric x₀ y).det) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
  contDiffOn_det_of_entries (g.isCoordMetric_coordMetric x₀).smooth

/-- **The inverse metric `g^{ij}` is smooth on the chart target.** -/
theorem NondegMetric.contDiffOn_coordMetric_inv (x₀ : M) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun y => (g.coordMetric x₀ y)⁻¹ i j) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
  (g.isCoordMetric_coordMetric x₀).contDiffOn_inv i j

/-- **The volume density `√|det g|` is smooth on the chart target.** -/
theorem NondegMetric.contDiffOn_volDensity (x₀ : M) :
    ContDiffOn ℝ ∞ (g.volDensity x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
  intro y hy
  have hd := g.contDiffOn_coordMetric_det x₀
  have hne : (g.coordMetric x₀ y).det ≠ 0 := (g.coordMetric_isUnit_det x₀ hy).ne_zero
  rcases hne.lt_or_gt with hneg | hpos
  · -- near `y` the determinant is negative, so `|det| = -det`
    have hev : ∀ᶠ z in nhdsWithin y (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target,
        g.volDensity x₀ z = √(-(g.coordMetric x₀ z).det) := by
      filter_upwards [Filter.Tendsto.eventually (hd.continuousOn y hy) (gt_mem_nhds hneg)] with z hz
      unfold NondegMetric.volDensity; rw [abs_of_neg hz]
    refine ContDiffWithinAt.congr_of_eventuallyEq ?_ hev (by unfold NondegMetric.volDensity; rw [abs_of_neg hneg])
    exact ((hd y hy).neg).sqrt (by simpa using hneg.ne)
  · have hev : ∀ᶠ z in nhdsWithin y (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target,
        g.volDensity x₀ z = √((g.coordMetric x₀ z).det) := by
      filter_upwards [Filter.Tendsto.eventually (hd.continuousOn y hy) (lt_mem_nhds hpos)] with z hz
      unfold NondegMetric.volDensity; rw [abs_of_pos hz]
    refine ContDiffWithinAt.congr_of_eventuallyEq ?_ hev (by unfold NondegMetric.volDensity; rw [abs_of_pos hpos])
    exact (hd y hy).sqrt hpos.ne'

end Lightlike
