import Lightlike.Spacetime.EHManifold.FRManifoldPiece

/-!
# The first variation of the `f(R)` action on a manifold, for a perturbation supported in a small chart ball

`fR_first_variation_manifold`: let `h` be a symmetric tensor field on a manifold `M` vanishing outside a
compact set `K` inside a small coordinate ball of the chart at `x₀`. Then, in the components of that chart,

`d/dt|₀ ∫_K f(R(g + t h)) d vol_{g + t h} = -∫_{φ(K)} √|g| h_{ab} (f'(R) R^{ab} - ½ f(R) g^{ab} - ∇^a ∇^b f'(R) + g^{ab} □ f'(R)) dy`.

The components of the metric are continued outside the ball by the ball retraction (`coordMetricR`); on the
chart image of `K` they are the components of `g`.

## References

* T. P. Sotiriou, V. Faraoni, *f(R) theories of gravity*, arXiv:0805.1726, section II.A, (5)–(6), p. 5.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **The first variation of the `f(R)` action on a manifold**, for a perturbation of the metric by a
symmetric tensor field supported in a compact set inside a small coordinate ball of one chart. -/
theorem fR_first_variation_manifold (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) {K : Set M} (hK : IsCompact K)
    (hK0 : K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) {c : Fin n → ℝ} (φ : ContDiffBump c)
    (hball : ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (hKball : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K ⊆ ball c φ.rIn)
    (hsupp : ∀ x, x ∉ K → h.h x = 0) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hf' : ContDiff ℝ 2 (deriv f)) :
    HasDerivAt (fun t : ℝ => fRAction (g.perturb h t) f K)
      (-∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, √|(g.coordMetricR x₀ φ y).det| *
          ∑ α, ∑ β, h.coordComp x₀ y α β * fRTensorUp (g.coordMetricR x₀ φ) f y α β) 0 := by
  have hKm : MeasurableSet (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K) :=
    measurableSet_image_extChartAt x₀ hK.measurableSet hK0
  have hTc : IsCompact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K) :=
    hK.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hK0)
  have hsub : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
    rintro _ ⟨p, hp, rfl⟩
    exact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (hK0 hp)
  obtain ⟨ε, hε, hnd⟩ := g.exists_addSmul_nondegenerate h hK hsupp
  have hmain := fR_variation_tensor (g.coordMetricR x₀ φ) (h.coordCompExt x₀)
    (g.contDiff_coordMetricR x₀ φ hball) (h.contDiff_coordCompExt x₀ hK hK0 hsupp)
    (g.coordMetricR_symm x₀ φ) (h.coordCompExt_symm x₀) (g.det_coordMetricR_ne_zero x₀ φ hball) f hf
    hf' hTc (h.tsupport_coordCompExt_subset x₀ hK hK0 hsupp)
  have hrhs : ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, √|(g.coordMetricR x₀ φ y).det| *
        ∑ α, ∑ β, h.coordCompExt x₀ y α β * fRTensorUp (g.coordMetricR x₀ φ) f y α β =
      ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, √|(g.coordMetricR x₀ φ y).det| *
        ∑ α, ∑ β, h.coordComp x₀ y α β * fRTensorUp (g.coordMetricR x₀ φ) f y α β := by
    refine setIntegral_congr_fun hKm fun y hy => ?_
    simp only [h.coordCompExt_of_mem x₀ (hsub hy)]
  rw [hrhs] at hmain
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  have ht' : |t| < ε := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs] at ht
    exact ht
  show fRAction (g.perturb h t) f K =
    ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K,
      fRDensity (g.coordMetricR x₀ φ) (h.coordCompExt x₀) f t y
  rw [g.perturb_of_nondegenerate h t (hnd t ht'),
    fRAction_chart (g.addSmul h t (hnd t ht')) f hf.continuous x₀ hK.measurableSet hK0]
  refine setIntegral_congr_fun hKm fun y hy => ?_
  have hrr : ball c φ.rIn ⊆ ball c φ.rOut := ball_subset_ball φ.rIn_lt_rOut.le
  have he : (g.addSmul h t (hnd t ht')).coordMetric x₀ =ᶠ[𝓝 y]
      fun z => g.coordMetricR x₀ φ z + t • h.coordCompExt x₀ z := by
    filter_upwards [isOpen_ball.mem_nhds (hKball hy)] with z hz
    show (g.addSmul h t (hnd t ht')).coordMetric x₀ z =
      g.coordMetric x₀ (ballRetract φ z) + t • h.coordCompExt x₀ z
    rw [ballRetract_of_mem φ hz, g.coordMetric_addSmul h t (hnd t ht') x₀ z,
      h.coordCompExt_of_mem x₀ (hball (hrr hz))]
  show fRDensity ((g.addSmul h t (hnd t ht')).coordMetric x₀) 0 f 0 y =
    fRDensity (g.coordMetricR x₀ φ) (h.coordCompExt x₀) f t y
  unfold fRDensity
  have h1 : (fun z => (g.addSmul h t (hnd t ht')).coordMetric x₀ z +
        (0 : ℝ) • (0 : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) z)
      =ᶠ[𝓝 y] fun z => g.coordMetricR x₀ φ z + t • h.coordCompExt x₀ z :=
    he.mono fun z hz => by
      show (g.addSmul h t (hnd t ht')).coordMetric x₀ z +
          (0 : ℝ) • (0 : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) z =
        g.coordMetricR x₀ φ z + t • h.coordCompExt x₀ z
      rw [zero_smul, add_zero, hz]
  rw [scalarCurvature_congr h1, zero_smul, add_zero, he.eq_of_nhds]

end Lightlike
