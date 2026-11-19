import Lightlike.Spacetime.VariationCritical
import Lightlike.Spacetime.EHManifold.TensorVariation

/-!
# Solutions of the vacuum Einstein equations are critical points of the action on a manifold

`eh_first_variation_manifold_eq_zero`: if the components of `g` in a chart satisfy the vacuum Einstein
equations with cosmological constant on the chart image of a compact set `K` (the symmetric part of
`R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}` vanishes there), then the first variation of the Einstein–Hilbert action
`ehAction` of `K` vanishes for every symmetric tensor field supported in `K` (`K` inside a small coordinate
ball of the chart).

The converse on the manifold is not proved here (for coordinate metrics on a ball it is
`isEHCriticalOnBall_iff`).

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 4, eqs. (4.66) and
  (4.67), p. 116.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **Solutions of the vacuum Einstein equations are critical points of the Einstein–Hilbert action**, for
perturbations by a symmetric tensor field supported in a compact set inside a small coordinate ball. -/
theorem eh_first_variation_manifold_eq_zero (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) {K : Set M} (hK : IsCompact K)
    (hK0 : K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) {c : Fin n → ℝ} (φ : ContDiffBump c)
    (hball : ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (hKball : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K ⊆ ball c φ.rIn)
    (hsupp : ∀ x, x ∉ K → h.h x = 0) (Λ : ℝ)
    (hE : ∀ y ∈ extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, ∀ α β,
      einsteinUp (g.coordMetric x₀) Λ y α β + einsteinUp (g.coordMetric x₀) Λ y β α = 0) :
    HasDerivAt (fun t : ℝ => ehAction (g.perturb h t) Λ K) 0 0 := by
  have hmain := eh_first_variation_manifold g h x₀ hK hK0 φ hball hKball hsupp Λ
  have hKm : MeasurableSet (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K) :=
    measurableSet_image_extChartAt x₀ hK.measurableSet hK0
  have hz : ∀ y ∈ extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, ∑ α, ∑ β, h.coordComp x₀ y α β *
      (ricciUp (g.coordMetric x₀) y α β -
        (1 / 2) * scalarCurvature (g.coordMetric x₀) y * (g.coordMetric x₀ y)⁻¹ α β +
        Λ * (g.coordMetric x₀ y)⁻¹ α β) = 0 := by
    intro y hy
    have hsw : ∑ α, ∑ β, h.coordComp x₀ y α β * einsteinUp (g.coordMetric x₀) Λ y α β =
        ∑ α, ∑ β, h.coordComp x₀ y α β * einsteinUp (g.coordMetric x₀) Λ y β α := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      rw [h.coordComp_symm x₀ y β α]
    have h2 : ∑ α, ∑ β, h.coordComp x₀ y α β * einsteinUp (g.coordMetric x₀) Λ y α β +
        ∑ α, ∑ β, h.coordComp x₀ y α β * einsteinUp (g.coordMetric x₀) Λ y β α = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun α _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun β _ => ?_
      rw [← mul_add, hE y hy α β, mul_zero]
    have h3 : ∑ α, ∑ β, h.coordComp x₀ y α β * einsteinUp (g.coordMetric x₀) Λ y α β = 0 := by
      rw [← hsw] at h2
      linarith
    exact h3
  have hint : ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, √|(g.coordMetric x₀ y).det| *
      ∑ α, ∑ β, h.coordComp x₀ y α β *
      (ricciUp (g.coordMetric x₀) y α β -
        (1 / 2) * scalarCurvature (g.coordMetric x₀) y * (g.coordMetric x₀ y)⁻¹ α β +
        Λ * (g.coordMetric x₀ y)⁻¹ α β) = 0 := by
    rw [setIntegral_congr_fun hKm (g := fun _ => (0 : ℝ)) fun y hy => by
      show √|(g.coordMetric x₀ y).det| * ∑ α, ∑ β, h.coordComp x₀ y α β *
        (ricciUp (g.coordMetric x₀) y α β -
          (1 / 2) * scalarCurvature (g.coordMetric x₀) y * (g.coordMetric x₀ y)⁻¹ α β +
          Λ * (g.coordMetric x₀ y)⁻¹ α β) = 0
      rw [hz y hy, mul_zero]]
    simp
  rw [hint, neg_zero] at hmain
  exact hmain

end Lightlike
