import Lightlike.Spacetime.Coordinates
import Lightlike.Spacetime.EHManifold.BallVariation

/-!
# The first variation of the Einstein–Hilbert action in a chart of a manifold

`eh_first_variation_chart`: for a metric `g` on a manifold `M` and a chart at `x₀`, the first variation
formula holds for the chart components `g.coordMetric x₀` of the metric and a perturbation `h` of the
components supported in a compact set `T` inside a ball `B(c, φ.rIn)` whose larger concentric ball
`B(c, φ.rOut)` lies in the target of the chart:

`d/dt ∫_T √|g + t h| (R(g + t h) - 2Λ) = -∫_T √|g| (R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}) h_{αβ}` at `t = 0`.

The components of the metric are smooth, symmetric and nondegenerate only on the target of the chart
(`NondegMetric.isCoordMetric_coordMetric`), which is why the ball version `eh_first_variation_ball` is used.

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 4, eqs. (4.54) to
  (4.67), pp. 114 to 116.
-/

open Filter Topology Metric MeasureTheory Manifold
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- **The first variation of the Einstein–Hilbert action in a chart of a manifold**, for a perturbation of
the chart components supported in a small coordinate ball. -/
theorem eh_first_variation_chart (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) {c : Fin n → ℝ}
    (φ : ContDiffBump c)
    (hball : ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hhs : ∀ y a b, h y a b = h y b a) {T : Set (Fin n → ℝ)} (hT : IsCompact T)
    (hTball : T ⊆ ball c φ.rIn) (hsupp : ∀ a b, tsupport (fun y => h y a b) ⊆ T) (Λ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ y in T, lagDensity (g.coordMetric x₀) h Λ t y)
      (-∫ y in T, √|(g.coordMetric x₀ y).det| * ∑ α, ∑ β, h y α β *
          (ricciUp (g.coordMetric x₀) y α β -
            (1 / 2) * scalarCurvature (g.coordMetric x₀) y * (g.coordMetric x₀ y)⁻¹ α β +
            Λ * (g.coordMetric x₀ y)⁻¹ α β)) 0 := by
  have hc := g.isCoordMetric_coordMetric x₀
  refine eh_first_variation_ball φ (g.coordMetric x₀) h (fun a b => (hc.smooth a b).mono hball) hh ?_
    hhs (fun y hy => (hc.isUnit_det y (hball hy)).ne_zero) hT hTball hsupp Λ
  intro y hy a b
  have hs := hc.symm y (hball hy)
  have h1 : (g.coordMetric x₀ y).transpose a b = g.coordMetric x₀ y a b := by rw [hs]
  exact h1.symm

end Lightlike
