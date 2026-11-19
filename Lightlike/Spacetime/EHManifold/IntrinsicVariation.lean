import Lightlike.Spacetime.EHManifold.IntrinsicIntegrand
import Lightlike.Spacetime.EHManifold.TensorVariation

/-!
# The first variation of the Einstein–Hilbert action on a manifold, in intrinsic form

`eh_first_variation_manifold_intrinsic`: for a metric `g` on a manifold and a symmetric tensor field `h`
that vanishes outside a compact set `K` inside a small coordinate ball of one chart,

`d/dt ∫_K (R(g + t h) - 2Λ) d vol_{g + t h} = -∫_K ⟨G + Λ g, h⟩_g d vol_g` at `t = 0`,

where `G` is the Einstein tensor of `g` and `⟨·, ·⟩_g` the contraction with the inverse metric
(`ehIntegrand`). Both sides are intrinsic: no chart appears in the conclusion.

This is the first variation of the action, Carroll's (4.66) with a cosmological constant (he varies the
inverse metric, so his integrand is `(R_{μν} - ½ R g_{μν}) δg^{μν}`, with the opposite sign), for a
perturbation supported in one small coordinate ball.

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

/-- The integrand `⟨G + Λ g, h⟩_g` is continuous on every chart domain. -/
theorem continuousOn_ehIntegrand (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (Λ : ℝ) (x₀ : M) :
    ContinuousOn (ehIntegrand g h Λ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source := by
  have hc := g.isCoordMetric_coordMetric x₀
  have hinv : ∀ a b, ContinuousOn (fun y => (g.coordMetric x₀ y)⁻¹ a b)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := fun a b => (hc.contDiffOn_inv a b).continuousOn
  have hric : ∀ a b, ContinuousOn (fun y => ricci (g.coordMetric x₀) a b y)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := fun a b => (hc.contDiffOn_ricci a b).continuousOn
  have hR : ContinuousOn (fun y => scalarCurvature (g.coordMetric x₀) y)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := hc.contDiffOn_scalarCurvature.continuousOn
  have hup : ∀ α β, ContinuousOn (fun y => ricciUp (g.coordMetric x₀) y α β)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
    intro α β
    unfold ricciUp
    exact continuousOn_finset_sum _ fun a _ => continuousOn_finset_sum _ fun b _ =>
      ((hinv α a).mul (hric a b)).mul (hinv b β)
  have hF : ContinuousOn (fun y => ∑ α, ∑ β, h.coordComp x₀ y α β *
      (ricciUp (g.coordMetric x₀) y α β -
        (1 / 2) * scalarCurvature (g.coordMetric x₀) y * (g.coordMetric x₀ y)⁻¹ α β +
        Λ * (g.coordMetric x₀ y)⁻¹ α β)) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    continuousOn_finset_sum _ fun α _ => continuousOn_finset_sum _ fun β _ =>
      ((h.coordComp_smooth x₀ α β).continuousOn).mul
        (((hup α β).sub ((continuousOn_const.mul hR).mul (hinv α β))).add
          (continuousOn_const.mul (hinv α β)))
  refine (hF.comp (continuousOn_extChartAt x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).mapsTo).congr
    fun p hp => ?_
  have h1 := ehIntegrand_chart g h Λ x₀ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hp)
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hp] at h1
  exact h1

/-- **The first variation of the Einstein–Hilbert action on a manifold, in intrinsic form.** -/
theorem eh_first_variation_manifold_intrinsic (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) {K : Set M} (hK : IsCompact K)
    (hK0 : K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) {c : Fin n → ℝ} (φ : ContDiffBump c)
    (hball : ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (hKball : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K ⊆ ball c φ.rIn)
    (hsupp : ∀ x, x ∉ K → h.h x = 0) (Λ : ℝ) :
    HasDerivAt (fun t : ℝ => ehAction (g.perturb h t) Λ K)
      (-∫ p in K, ehIntegrand g h Λ p ∂(NondegMetric.volumeMeasure g)) 0 := by
  have hmain := eh_first_variation_manifold g h x₀ hK hK0 φ hball hKball hsupp Λ
  have hKm : MeasurableSet (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K) :=
    measurableSet_image_extChartAt x₀ hK.measurableSet hK0
  have hsub : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
    rintro _ ⟨p, hp, rfl⟩
    exact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (hK0 hp)
  have hmeas : AEStronglyMeasurable (ehIntegrand g h Λ) ((NondegMetric.volumeMeasure g).restrict K) :=
    ((continuousOn_ehIntegrand g h Λ x₀).aestronglyMeasurable
      (isOpen_extChartAt_source x₀).measurableSet).mono_measure (Measure.restrict_mono hK0 le_rfl)
  have hint : ∫ p in K, ehIntegrand g h Λ p ∂(NondegMetric.volumeMeasure g) =
      ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, √|(g.coordMetric x₀ y).det| *
        ∑ α, ∑ β, h.coordComp x₀ y α β *
          (ricciUp (g.coordMetric x₀) y α β -
            (1 / 2) * scalarCurvature (g.coordMetric x₀) y * (g.coordMetric x₀ y)⁻¹ α β +
            Λ * (g.coordMetric x₀ y)⁻¹ α β) := by
    rw [NondegMetric.setIntegral_volumeMeasure_chart g x₀ hK.measurableSet hK0 _ hmeas]
    refine setIntegral_congr_fun hKm fun y hy => ?_
    show NondegMetric.volDensity g x₀ y *
        ehIntegrand g h Λ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) = _
    rw [ehIntegrand_chart g h Λ x₀ (hsub hy)]
    rfl
  rw [hint]
  exact hmain

end Lightlike
