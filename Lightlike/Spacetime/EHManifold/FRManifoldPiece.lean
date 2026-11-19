import Lightlike.Spacetime.EHManifold.CoverVariation
import Lightlike.Spacetime.EHManifold.FRMatter

/-!
# The `f(R)` action on a manifold: pieces inside one chart

* `fR_variation_piece`: the coordinate variation of `∫ √|g| f(R)` over a measurable piece of a compact set;
* `fRAction g f K = ∫_K f(R) d vol_g`: the `f(R)` action of a region of a manifold, with the scalar
  curvature of the Levi-Civita connection;
* `fRAction_chart`: inside one chart it is the chart integral of the coordinate density `√|g| f(R)`;
* `fRPieceVar`, `hasDerivAt_fRAction_piece`: the derivative of the action of a measurable piece inside a
  small coordinate ball, in the components of the chart: the integral of
  `-√|g| h_{ab} (f'(R) R^{ab} - ½ f(R) g^{ab}) + f'(R) ∂_ρ(√|g| W^ρ)`.

Supporting statements for the first variation of the `f(R)` action on a manifold; no catalogue entry.

## References

* T. P. Sotiriou, V. Faraoni, *f(R) theories of gravity*, arXiv:0805.1726, section II.A, (5)–(6), p. 5.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

section Coordinate

variable {n : ℕ}

/-- **The variation of the `f(R)` density over a measurable piece of a compact set**, in coordinates. -/
theorem fR_variation_piece (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ x, (g x).det ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) {T : Set (Fin n → ℝ)}
    (hT : IsCompact T) (A : Set (Fin n → ℝ)) :
    HasDerivAt (fun t : ℝ => ∫ x in T, fRDensity g h f t x ∂(volume.restrict A))
      (∫ x in T, (-√|(g x).det| * ∑ α, ∑ β, h x α β *
          (deriv f (scalarCurvature g x) * ricciUp g x α β -
            (1 / 2) * f (scalarCurvature g x) * (g x)⁻¹ α β) +
        deriv f (scalarCurvature g x) * ehFluxDiv g h x) ∂(volume.restrict A)) 0 := by
  have hΦc : ∀ x, ContDiffAt ℝ 1 (fun p : ℝ × (Fin n → ℝ) => fRDensity g h f p.1 p.2) (0, x) :=
    fun x => contDiffAt_fRDensity g h hg hh hdet f hf x
  have hmain := hasDerivAt_integral_family (μ := (volume : Measure (Fin n → ℝ)).restrict A) hT
    (fun p : ℝ × (Fin n → ℝ) => fRDensity g h f p.1 p.2) (fun x _ => hΦc x)
  have hder : ∀ x, fderiv ℝ (fun p : ℝ × (Fin n → ℝ) => fRDensity g h f p.1 p.2) (0, x) (1, 0) =
      -√|(g x).det| * ∑ α, ∑ β, h x α β *
          (deriv f (scalarCurvature g x) * ricciUp g x α β -
            (1 / 2) * f (scalarCurvature g x) * (g x)⁻¹ α β) +
        deriv f (scalarCurvature g x) * ehFluxDiv g h x := by
    intro x
    have h1 := hasDerivAt_fRDensity g h hg hh hgs hhs x (hdet x) f (deriv f (scalarCurvature g x))
      ((hf.differentiable (by simp)).differentiableAt.hasDerivAt)
    have h2 : HasDerivAt (fun t : ℝ => fRDensity g h f t x)
        (fderiv ℝ (fun p : ℝ × (Fin n → ℝ) => fRDensity g h f p.1 p.2) (0, x) (1, 0)) 0 := by
      have hd := ((hΦc x).differentiableAt (by simp)).hasFDerivAt
      have hl : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : Fin n → ℝ)) 0 :=
        (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 x)
      exact hd.comp_hasDerivAt (0 : ℝ) hl
    exact h2.unique h1
  have hint : ∫ x in T, fderiv ℝ (fun p : ℝ × (Fin n → ℝ) => fRDensity g h f p.1 p.2) (0, x) (1, 0)
        ∂(volume.restrict A) =
      ∫ x in T, (-√|(g x).det| * ∑ α, ∑ β, h x α β *
          (deriv f (scalarCurvature g x) * ricciUp g x α β -
            (1 / 2) * f (scalarCurvature g x) * (g x)⁻¹ α β) +
        deriv f (scalarCurvature g x) * ehFluxDiv g h x) ∂(volume.restrict A) :=
    setIntegral_congr_fun hT.isClosed.measurableSet fun x _ => hder x
  rw [hint] at hmain
  exact hmain

end Coordinate

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **The `f(R)` action** of a region `K` of a manifold with metric `g`: `∫_K f(R) d vol_g`, with the
scalar curvature of the Levi-Civita connection of `g`. -/
def fRAction (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (f : ℝ → ℝ) (K : Set M) : ℝ :=
  ∫ p in K, f ((leviCivita g).scalarCurvatureAt g p) ∂(NondegMetric.volumeMeasure g)

/-- `f(R)` is continuous on every chart domain, for continuous `f`. -/
theorem continuousOn_fR (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (f : ℝ → ℝ) (hf : Continuous f) (x₀ : M) :
    ContinuousOn (fun p => f ((leviCivita g).scalarCurvatureAt g p))
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source := by
  have h1 : ContinuousOn (fun p => (leviCivita g).scalarCurvatureAt g p)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source :=
    (continuousOn_ehLagrangian g 0 x₀).congr fun p _ => by simp
  exact hf.comp_continuousOn h1

/-- The `f(R)` action of a measurable region inside one chart is the chart integral of the coordinate
density `√|g| f(R)`. -/
theorem fRAction_chart (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (f : ℝ → ℝ) (hf : Continuous f) (x₀ : M)
    {K : Set M} (hK : MeasurableSet K) (hK0 : K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    fRAction g f K =
      ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K, fRDensity (g.coordMetric x₀) 0 f 0 y := by
  haveI := contMDiffCovariantDerivative_leviCivita g
  have hLC : (leviCivita g).IsLeviCivita g := ⟨leviCivita_torsion g, leviCivita_compat g⟩
  have hmeas : AEStronglyMeasurable (fun p => f ((leviCivita g).scalarCurvatureAt g p))
      ((NondegMetric.volumeMeasure g).restrict K) :=
    ((continuousOn_fR g f hf x₀).aestronglyMeasurable
      (isOpen_extChartAt_source x₀).measurableSet).mono_measure (Measure.restrict_mono hK0 le_rfl)
  unfold fRAction
  rw [NondegMetric.setIntegral_volumeMeasure_chart g x₀ hK hK0 _ hmeas]
  refine setIntegral_congr_fun (measurableSet_image_extChartAt x₀ hK hK0) fun y hy => ?_
  obtain ⟨p, hp, rfl⟩ := hy
  have hyt : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (hK0 hp)
  show NondegMetric.volDensity g x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) *
      f ((leviCivita g).scalarCurvatureAt g
        ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p))) =
    fRDensity (g.coordMetric x₀) 0 f 0 (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p)
  rw [scalarCurvatureAt_coord (leviCivita g) x₀ g hLC hyt]
  simp [fRDensity, NondegMetric.volDensity]

/-- **The variation of the `f(R)` action over a piece**, in the components of one chart. -/
def fRPieceVar (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M)
    {c : Fin n → ℝ} (φ : ContDiffBump c) (f : ℝ → ℝ) (T A : Set M) : ℝ :=
  ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T,
    (-√|(g.coordMetricR x₀ φ y).det| * ∑ α, ∑ β, h.coordCompR x₀ φ y α β *
        (deriv f (scalarCurvature (g.coordMetricR x₀ φ) y) * ricciUp (g.coordMetricR x₀ φ) y α β -
          (1 / 2) * f (scalarCurvature (g.coordMetricR x₀ φ) y) * (g.coordMetricR x₀ φ y)⁻¹ α β) +
      deriv f (scalarCurvature (g.coordMetricR x₀ φ) y) *
        ehFluxDiv (g.coordMetricR x₀ φ) (h.coordCompR x₀ φ) y)
    ∂(volume.restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A))

variable (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M)
  {c : Fin n → ℝ} (φ : ContDiffBump c)
  (hball : ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)

include hball in
/-- **The derivative of the `f(R)` action of a measurable piece inside one chart.** -/
theorem hasDerivAt_fRAction_piece (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) {T A : Set M} (hT : IsCompact T)
    (hT0 : T ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (hTball : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T ⊆ ball c φ.rIn)
    (hA : MeasurableSet A) (hAT : A ⊆ T) {ε : ℝ} (hε : 0 < ε)
    (hnd : ∀ t : ℝ, |t| < ε → ∀ (x : M) (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x),
      (∀ w, g.g x v w + t * h.h x v w = 0) → v = 0) :
    HasDerivAt (fun t : ℝ => fRAction (g.perturb h t) f A) (fRPieceVar g h x₀ φ f T A) 0 := by
  have hTc : IsCompact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T) :=
    hT.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hT0)
  have hA0 : A ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source := hAT.trans hT0
  have hAm : MeasurableSet (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A) :=
    measurableSet_image_extChartAt x₀ hA hA0
  have hAsub : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A ⊆ extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T :=
    image_mono hAT
  have hmain := fR_variation_piece (g.coordMetricR x₀ φ) (h.coordCompR x₀ φ)
    (g.contDiff_coordMetricR x₀ φ hball) (h.contDiff_coordCompR x₀ φ hball)
    (g.coordMetricR_symm x₀ φ) (h.coordCompR_symm x₀ φ) (g.det_coordMetricR_ne_zero x₀ φ hball) f hf
    hTc (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A)
  refine HasDerivAt.congr_of_eventuallyEq hmain ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  have ht' : |t| < ε := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs] at ht
    exact ht
  show fRAction (g.perturb h t) f A =
    ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T,
      fRDensity (g.coordMetricR x₀ φ) (h.coordCompR x₀ φ) f t y
      ∂(volume.restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A))
  rw [g.perturb_of_nondegenerate h t (hnd t ht'),
    fRAction_chart (g.addSmul h t (hnd t ht')) f hf.continuous x₀ hA hA0,
    Measure.restrict_restrict hTc.isClosed.measurableSet, inter_eq_self_of_subset_right hAsub]
  refine setIntegral_congr_fun hAm fun y hy => ?_
  have hyT := hAsub hy
  have he : (g.addSmul h t (hnd t ht')).coordMetric x₀ =ᶠ[𝓝 y]
      fun z => g.coordMetricR x₀ φ z + t • h.coordCompR x₀ φ z := by
    filter_upwards [isOpen_ball.mem_nhds (hTball hyT)] with z hz
    show (g.addSmul h t (hnd t ht')).coordMetric x₀ z =
      g.coordMetric x₀ (ballRetract φ z) + t • h.coordComp x₀ (ballRetract φ z)
    rw [ballRetract_of_mem φ hz, g.coordMetric_addSmul h t (hnd t ht') x₀ z]
  show fRDensity ((g.addSmul h t (hnd t ht')).coordMetric x₀) 0 f 0 y =
    fRDensity (g.coordMetricR x₀ φ) (h.coordCompR x₀ φ) f t y
  unfold fRDensity
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
