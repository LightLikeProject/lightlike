import Lightlike.Spacetime.EHManifold.IntrinsicAction

/-!
# The first variation of the Einstein–Hilbert action on a manifold, for a perturbation in one chart

`eh_first_variation_manifold_chart`: let `g` be a metric on a manifold `M`, `K` a compact set inside the
domain of the chart at `x₀` whose chart image lies in a small coordinate ball, and `g_t` a family of metrics
on `M`, each with a Levi-Civita connection, whose components in that chart are `g + t h` near the image of
`K`, with `h` smooth, symmetric and supported in the image of `K`. Then the Einstein–Hilbert action of `K`,

`S(t) = ∫_K (R(g_t) - 2Λ) d vol_{g_t}`

(the integral for the volume measure of `g_t`, with the scalar curvature of its Levi-Civita connection) has
the derivative `-∫ √|g| (R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}) h_{αβ}` at `t = 0`, the integral being over the chart
image of `K`, in the components of the chart.

The family `g_t` and its connections are data of the statement; the right-hand side is in chart components.
The statement for a perturbation that is not supported in one coordinate ball, and the intrinsic form of
the right-hand side, are not proved here.

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 4, eqs. (4.54) to
  (4.67), pp. 114 to 116.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **The first variation of the Einstein–Hilbert action on a manifold**, for a family of metrics that
differs from `g` only inside a compact set contained in a small coordinate ball of one chart. -/
theorem eh_first_variation_manifold_chart (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M)
    (gt : ℝ → NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (covt : ℝ → Connection 𝓘(ℝ, Fin n → ℝ) M)
    [∀ t, CovariantDerivative.ContMDiffCovariantDerivative (covt t) ∞]
    (hLC : ∀ t, (covt t).IsLeviCivita (gt t)) {K : Set M} (hK : IsCompact K)
    (hK0 : K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) {c : Fin n → ℝ} (φ : ContDiffBump c)
    (hball : ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (hKball : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K ⊆ ball c φ.rIn)
    (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hhs : ∀ y a b, h y a b = h y b a)
    (hsupp : ∀ a b, tsupport (fun y => h y a b) ⊆ extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K)
    (hcoord : ∀ t, ∀ y ∈ extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K,
      (gt t).coordMetric x₀ =ᶠ[𝓝 y] fun z => g.coordMetric x₀ z + t • h z)
    (Λ : ℝ)
    (hmeas : ∀ t, AEStronglyMeasurable (fun p => (covt t).scalarCurvatureAt (gt t) p - 2 * Λ)
      ((NondegMetric.volumeMeasure (gt t)).restrict K)) :
    HasDerivAt
      (fun t : ℝ => ∫ p in K, ((covt t).scalarCurvatureAt (gt t) p - 2 * Λ)
        ∂(NondegMetric.volumeMeasure (gt t)))
      (-∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, √|(g.coordMetric x₀ y).det| * ∑ α, ∑ β, h y α β *
          (ricciUp (g.coordMetric x₀) y α β -
            (1 / 2) * scalarCurvature (g.coordMetric x₀) y * (g.coordMetric x₀ y)⁻¹ α β +
            Λ * (g.coordMetric x₀ y)⁻¹ α β)) 0 := by
  have hKm : MeasurableSet (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K) :=
    measurableSet_image_extChartAt x₀ hK.measurableSet hK0
  have hTc : IsCompact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K) :=
    hK.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hK0)
  have hS : ∀ t : ℝ, ∫ p in K, ((covt t).scalarCurvatureAt (gt t) p - 2 * Λ)
        ∂(NondegMetric.volumeMeasure (gt t)) =
      ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, lagDensity (g.coordMetric x₀) h Λ t y := by
    intro t
    rw [eh_action_chart (gt t) (covt t) (hLC t) x₀ hK.measurableSet hK0 Λ (hmeas t)]
    refine setIntegral_congr_fun hKm fun y hy => ?_
    have he := hcoord t y hy
    show lagDensity ((gt t).coordMetric x₀) 0 Λ 0 y = lagDensity (g.coordMetric x₀) h Λ t y
    unfold lagDensity
    have h1 : (fun z => (gt t).coordMetric x₀ z + (0 : ℝ) • (0 : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) z)
        =ᶠ[𝓝 y] fun z => g.coordMetric x₀ z + t • h z :=
      he.mono fun z hz => by
        show (gt t).coordMetric x₀ z + (0 : ℝ) • (0 : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) z =
          g.coordMetric x₀ z + t • h z
        rw [zero_smul, add_zero, hz]
    rw [scalarCurvature_congr h1, zero_smul, add_zero, he.eq_of_nhds]
  have hfun : (fun t : ℝ => ∫ p in K, ((covt t).scalarCurvatureAt (gt t) p - 2 * Λ)
        ∂(NondegMetric.volumeMeasure (gt t))) =
      fun t => ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, lagDensity (g.coordMetric x₀) h Λ t y :=
    funext hS
  rw [hfun]
  exact eh_first_variation_chart g x₀ φ hball h hh hhs hTc hKball hsupp Λ

end Lightlike
