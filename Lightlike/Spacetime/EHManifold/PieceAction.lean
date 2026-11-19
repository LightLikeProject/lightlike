import Lightlike.Spacetime.EHManifold.PieceVariation
import Lightlike.Spacetime.EHManifold.Retraction
import Lightlike.Spacetime.EHManifold.TensorVariation

/-!
# The derivative of the Einstein–Hilbert action of a measurable piece inside one chart

`hasDerivAt_ehAction_piece`: for a metric `g`, a symmetric tensor field `h` (no condition on its support,
except that `g + t h` is a metric for small `t`), a compact set `T` inside a small coordinate ball of the
chart at `x₀` and a measurable `A ⊆ T`,

`d/dt ehAction (g + t h) Λ A = pieceVar g h x₀ φ Λ T A` at `t = 0`,

where `pieceVar` is the integral over the chart image of `A` of the Einstein term plus the divergence of
the Palatini flux, in the components of the chart (continued to all of `ℝⁿ` with the ball retraction).

Supporting lemma for perturbations that are not supported in one chart; no catalogue entry.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- The components of `g` in the chart at `x₀`, continued to all of `ℝⁿ` with the ball retraction. -/
def NondegMetric.coordMetricR (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) {c : Fin n → ℝ}
    (φ : ContDiffBump c) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  g.coordMetric x₀ (ballRetract φ y)

/-- The components of `h` in the chart at `x₀`, continued to all of `ℝⁿ` with the ball retraction. -/
def SymBilinField.coordCompR (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) {c : Fin n → ℝ}
    (φ : ContDiffBump c) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  h.coordComp x₀ (ballRetract φ y)

/-- **The variation of the action over a piece**, in the components of one chart: the integral over the
chart image of `A` of the Einstein term plus the divergence of the Palatini flux. -/
def pieceVar (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M)
    {c : Fin n → ℝ} (φ : ContDiffBump c) (Λ : ℝ) (T A : Set M) : ℝ :=
  ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T,
    (-√|(g.coordMetricR x₀ φ y).det| * ∑ α, ∑ β, h.coordCompR x₀ φ y α β *
        (ricciUp (g.coordMetricR x₀ φ) y α β -
          (1 / 2) * scalarCurvature (g.coordMetricR x₀ φ) y * (g.coordMetricR x₀ φ y)⁻¹ α β +
          Λ * (g.coordMetricR x₀ φ y)⁻¹ α β) +
      ehFluxDiv (g.coordMetricR x₀ φ) (h.coordCompR x₀ φ) y)
    ∂(volume.restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A))

variable (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M)
  {c : Fin n → ℝ} (φ : ContDiffBump c)
  (hball : ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)

include hball in
lemma NondegMetric.contDiff_coordMetricR (a b : Fin n) :
    ContDiff ℝ ∞ (fun y => g.coordMetricR x₀ φ y a b) :=
  contDiff_comp_ballRetract φ
    (fun a b => ((g.isCoordMetric_coordMetric x₀).smooth a b).mono hball) a b

include hball in
lemma SymBilinField.contDiff_coordCompR (a b : Fin n) :
    ContDiff ℝ ∞ (fun y => h.coordCompR x₀ φ y a b) :=
  contDiff_comp_ballRetract φ (fun a b => (h.coordComp_smooth x₀ a b).mono hball) a b

lemma NondegMetric.coordMetricR_symm (y : Fin n → ℝ) (a b : Fin n) :
    g.coordMetricR x₀ φ y a b = g.coordMetricR x₀ φ y b a := by
  have h1 := g.coordMetric_transpose x₀ (ballRetract φ y)
  have h2 : (g.coordMetric x₀ (ballRetract φ y))ᵀ a b = g.coordMetric x₀ (ballRetract φ y) a b := by
    rw [h1]
  exact h2.symm

lemma SymBilinField.coordCompR_symm (y : Fin n → ℝ) (a b : Fin n) :
    h.coordCompR x₀ φ y a b = h.coordCompR x₀ φ y b a :=
  h.coordComp_symm x₀ _ a b

include hball in
lemma NondegMetric.det_coordMetricR_ne_zero (y : Fin n → ℝ) : (g.coordMetricR x₀ φ y).det ≠ 0 :=
  (g.coordMetric_isUnit_det x₀ (hball (ballRetract_mem φ y))).ne_zero

include hball in
/-- **The derivative of the Einstein–Hilbert action of a measurable piece inside one chart.** -/
theorem hasDerivAt_ehAction_piece {T A : Set M} (hT : IsCompact T)
    (hT0 : T ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (hTball : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T ⊆ ball c φ.rIn)
    (hA : MeasurableSet A) (hAT : A ⊆ T) (Λ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hnd : ∀ t : ℝ, |t| < ε → ∀ (x : M) (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x),
      (∀ w, g.g x v w + t * h.h x v w = 0) → v = 0) :
    HasDerivAt (fun t : ℝ => ehAction (g.perturb h t) Λ A) (pieceVar g h x₀ φ Λ T A) 0 := by
  have hTc : IsCompact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T) :=
    hT.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hT0)
  have hA0 : A ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source := hAT.trans hT0
  have hAm : MeasurableSet (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A) :=
    measurableSet_image_extChartAt x₀ hA hA0
  have hAsub : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A ⊆ extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T :=
    image_mono hAT
  have hsubT : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
    rintro _ ⟨p, hp, rfl⟩
    exact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (hT0 hp)
  have hmain := eh_variation_piece (g.coordMetricR x₀ φ) (h.coordCompR x₀ φ)
    (g.contDiff_coordMetricR x₀ φ hball) (h.contDiff_coordCompR x₀ φ hball)
    (g.coordMetricR_symm x₀ φ) (h.coordCompR_symm x₀ φ) (g.det_coordMetricR_ne_zero x₀ φ hball) hTc
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A) Λ
  refine HasDerivAt.congr_of_eventuallyEq hmain ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  have ht' : |t| < ε := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs] at ht
    exact ht
  show ehAction (g.perturb h t) Λ A =
    ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T,
      lagDensity (g.coordMetricR x₀ φ) (h.coordCompR x₀ φ) Λ t y
      ∂(volume.restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A))
  rw [g.perturb_of_nondegenerate h t (hnd t ht'),
    ehAction_chart (g.addSmul h t (hnd t ht')) x₀ hA hA0 Λ,
    Measure.restrict_restrict hTc.isClosed.measurableSet, inter_eq_self_of_subset_right hAsub]
  refine setIntegral_congr_fun hAm fun y hy => ?_
  have hyT := hAsub hy
  have he : (g.addSmul h t (hnd t ht')).coordMetric x₀ =ᶠ[𝓝 y]
      fun z => g.coordMetricR x₀ φ z + t • h.coordCompR x₀ φ z := by
    filter_upwards [isOpen_ball.mem_nhds (hTball hyT)] with z hz
    show (g.addSmul h t (hnd t ht')).coordMetric x₀ z =
      g.coordMetric x₀ (ballRetract φ z) + t • h.coordComp x₀ (ballRetract φ z)
    rw [ballRetract_of_mem φ hz, g.coordMetric_addSmul h t (hnd t ht') x₀ z]
  show lagDensity ((g.addSmul h t (hnd t ht')).coordMetric x₀) 0 Λ 0 y =
    lagDensity (g.coordMetricR x₀ φ) (h.coordCompR x₀ φ) Λ t y
  unfold lagDensity
  have h1 : (fun z => (g.addSmul h t (hnd t ht')).coordMetric x₀ z +
        (0 : ℝ) • (0 : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) z)
      =ᶠ[𝓝 y] fun z => g.coordMetricR x₀ φ z + t • h.coordCompR x₀ φ z :=
    he.mono fun z hz => by
      show (g.addSmul h t (hnd t ht')).coordMetric x₀ z +
          (0 : ℝ) • (0 : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) z =
        g.coordMetricR x₀ φ z + t • h.coordCompR x₀ φ z
      rw [zero_smul, add_zero, hz]
  rw [scalarCurvature_congr h1, zero_smul, add_zero, he.eq_of_nhds]

end Lightlike
