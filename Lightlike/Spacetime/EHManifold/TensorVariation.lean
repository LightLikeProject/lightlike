import Lightlike.Spacetime.ChartTensor
import Lightlike.Spacetime.LeviCivitaSmooth
import Lightlike.Spacetime.EHManifold.IntrinsicAction
import Lightlike.Spacetime.EHManifold.PerturbationExt
import Lightlike.Spacetime.EHManifold.SmallT

/-!
# The first variation of the Einstein–Hilbert action on a manifold, for a tensor-field perturbation

* `ehAction g Λ K = ∫_K (R - 2Λ) d vol_g`: the Einstein–Hilbert action of a region `K` of a manifold with
  metric `g`, with `R` the scalar curvature of the Levi-Civita connection of `g` and `vol_g` the volume
  measure of `g`.
* `NondegMetric.perturb g h t`: the metric `g + t h` for a symmetric bilinear field `h` (and `g` itself for
  the `t` for which `g + t h` is degenerate; there are none near `0` when `h` has compact support).
* `eh_first_variation_manifold`: if `h` vanishes outside a compact set `K` inside the domain of one chart,
  whose chart image lies in a small coordinate ball, then

  `d/dt ehAction (g + t h) Λ K = -∫ √|g| (R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}) h_{αβ}` at `t = 0`,

  the integral over the chart image of `K`, in the components of the chart.

The perturbation is supported in one small coordinate ball, and the right-hand side is in chart components;
the general compactly supported perturbation is not proved here.

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

/-- **The Einstein–Hilbert action** of a region `K` of a manifold with metric `g`:
`∫_K (R - 2Λ) d vol_g`, with the scalar curvature of the Levi-Civita connection of `g`. -/
def ehAction (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (Λ : ℝ) (K : Set M) : ℝ :=
  ∫ p in K, ((leviCivita g).scalarCurvatureAt g p - 2 * Λ) ∂(NondegMetric.volumeMeasure g)

open Classical in
/-- **The perturbed metric `g + t h`**; equal to `g` for the `t` for which `g + t h` is degenerate. -/
def NondegMetric.perturb (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (t : ℝ) : NondegMetric 𝓘(ℝ, Fin n → ℝ) M :=
  if hnd : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x),
      (∀ w, g.g x v w + t * h.h x v w = 0) → v = 0 then g.addSmul h t hnd else g

lemma NondegMetric.perturb_of_nondegenerate (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (t : ℝ)
    (hnd : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x),
      (∀ w, g.g x v w + t * h.h x v w = 0) → v = 0) : g.perturb h t = g.addSmul h t hnd := by
  simp only [NondegMetric.perturb, dif_pos hnd]

/-- The Einstein–Hilbert action of a compact region inside one chart is the chart integral of the
coordinate Lagrangian density. -/
theorem ehAction_chart (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) {K : Set M}
    (hK : MeasurableSet K) (hK0 : K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (Λ : ℝ) :
    ehAction g Λ K =
      ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, lagDensity (g.coordMetric x₀) 0 Λ 0 y := by
  haveI := contMDiffCovariantDerivative_leviCivita g
  have hLC : (leviCivita g).IsLeviCivita g := ⟨leviCivita_torsion g, leviCivita_compat g⟩
  have hcont : ContinuousOn (fun p => (leviCivita g).scalarCurvatureAt g p - 2 * Λ)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source := by
    have h1 : ContinuousOn (fun p => scalarCurvature (g.coordMetric x₀)
        (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) - 2 * Λ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source :=
      (((g.isCoordMetric_coordMetric x₀).contDiffOn_scalarCurvature.continuousOn).comp
        (continuousOn_extChartAt x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).mapsTo).sub continuousOn_const
    refine h1.congr fun p hp => ?_
    have h2 := scalarCurvatureAt_coord (leviCivita g) x₀ g hLC
      ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hp)
    rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hp] at h2
    show (leviCivita g).scalarCurvatureAt g p - 2 * Λ = _
    rw [h2]
  have hmeas : AEStronglyMeasurable (fun p => (leviCivita g).scalarCurvatureAt g p - 2 * Λ)
      ((NondegMetric.volumeMeasure g).restrict K) :=
    (hcont.aestronglyMeasurable (isOpen_extChartAt_source x₀).measurableSet).mono_measure
      (Measure.restrict_mono hK0 le_rfl)
  exact eh_action_chart g (leviCivita g) hLC x₀ hK hK0 Λ hmeas

/-- **The first variation of the Einstein–Hilbert action on a manifold**, for a perturbation of the metric
by a symmetric tensor field supported in a compact set inside a small coordinate ball of one chart. -/
theorem eh_first_variation_manifold (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) {K : Set M} (hK : IsCompact K)
    (hK0 : K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) {c : Fin n → ℝ} (φ : ContDiffBump c)
    (hball : ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (hKball : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K ⊆ ball c φ.rIn)
    (hsupp : ∀ x, x ∉ K → h.h x = 0) (Λ : ℝ) :
    HasDerivAt (fun t : ℝ => ehAction (g.perturb h t) Λ K)
      (-∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, √|(g.coordMetric x₀ y).det| *
          ∑ α, ∑ β, h.coordComp x₀ y α β *
          (ricciUp (g.coordMetric x₀) y α β -
            (1 / 2) * scalarCurvature (g.coordMetric x₀) y * (g.coordMetric x₀ y)⁻¹ α β +
            Λ * (g.coordMetric x₀ y)⁻¹ α β)) 0 := by
  have hKm : MeasurableSet (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K) :=
    measurableSet_image_extChartAt x₀ hK.measurableSet hK0
  have hTc : IsCompact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K) :=
    hK.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hK0)
  have hsub : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
    rintro _ ⟨p, hp, rfl⟩
    exact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (hK0 hp)
  obtain ⟨ε, hε, hnd⟩ := g.exists_addSmul_nondegenerate h hK hsupp
  have hmain := eh_first_variation_chart g x₀ φ hball (h.coordCompExt x₀)
    (h.contDiff_coordCompExt x₀ hK hK0 hsupp) (h.coordCompExt_symm x₀) hTc hKball
    (h.tsupport_coordCompExt_subset x₀ hK hK0 hsupp) Λ
  have hrhs : ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, √|(g.coordMetric x₀ y).det| *
        ∑ α, ∑ β, h.coordCompExt x₀ y α β *
          (ricciUp (g.coordMetric x₀) y α β -
            (1 / 2) * scalarCurvature (g.coordMetric x₀) y * (g.coordMetric x₀ y)⁻¹ α β +
            Λ * (g.coordMetric x₀ y)⁻¹ α β) =
      ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, √|(g.coordMetric x₀ y).det| *
        ∑ α, ∑ β, h.coordComp x₀ y α β *
          (ricciUp (g.coordMetric x₀) y α β -
            (1 / 2) * scalarCurvature (g.coordMetric x₀) y * (g.coordMetric x₀ y)⁻¹ α β +
            Λ * (g.coordMetric x₀ y)⁻¹ α β) := by
    refine setIntegral_congr_fun hKm fun y hy => ?_
    simp only [h.coordCompExt_of_mem x₀ (hsub hy)]
  rw [hrhs] at hmain
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  have ht' : |t| < ε := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs] at ht
    exact ht
  show ehAction (g.perturb h t) Λ K =
    ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, lagDensity (g.coordMetric x₀) (h.coordCompExt x₀) Λ t y
  rw [g.perturb_of_nondegenerate h t (hnd t ht'),
    ehAction_chart (g.addSmul h t (hnd t ht')) x₀ hK.measurableSet hK0 Λ]
  refine setIntegral_congr_fun hKm fun y hy => ?_
  have he : (g.addSmul h t (hnd t ht')).coordMetric x₀ =ᶠ[𝓝 y]
      fun z => g.coordMetric x₀ z + t • h.coordCompExt x₀ z := by
    filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds (hsub hy)] with z hz
    show (g.addSmul h t (hnd t ht')).coordMetric x₀ z = g.coordMetric x₀ z + t • h.coordCompExt x₀ z
    rw [g.coordMetric_addSmul h t (hnd t ht') x₀ z, h.coordCompExt_of_mem x₀ hz]
  show lagDensity ((g.addSmul h t (hnd t ht')).coordMetric x₀) 0 Λ 0 y =
    lagDensity (g.coordMetric x₀) (h.coordCompExt x₀) Λ t y
  unfold lagDensity
  have h1 : (fun z => (g.addSmul h t (hnd t ht')).coordMetric x₀ z +
        (0 : ℝ) • (0 : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) z)
      =ᶠ[𝓝 y] fun z => g.coordMetric x₀ z + t • h.coordCompExt x₀ z :=
    he.mono fun z hz => by
      show (g.addSmul h t (hnd t ht')).coordMetric x₀ z +
          (0 : ℝ) • (0 : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) z =
        g.coordMetric x₀ z + t • h.coordCompExt x₀ z
      rw [zero_smul, add_zero, hz]
  rw [scalarCurvature_congr h1, zero_smul, add_zero, he.eq_of_nhds]

end Lightlike
