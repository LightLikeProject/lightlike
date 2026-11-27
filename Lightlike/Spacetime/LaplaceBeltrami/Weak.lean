import Mathlib
import Lightlike.Spacetime.LaplaceBeltrami.Coord

/-!
# The weak form of the Laplace–Beltrami operator and its independence of the chart

For a smooth nondegenerate metric `g` on a second countable Hausdorff manifold modelled on `ℝⁿ`, with its volume
measure `vol_g`:

* `NondegMetric.integral_mul_laplaceCoord_eq_dualPair` (**the weak form on the manifold**): for `ψ` smooth with compact
  support in the domain of the chart at `x₀`,
  `∫_M ψ · (Δ₀ f ∘ φ₀) dvol_g = ∫_M g⁻¹(dψ, df) dvol_g`;
* `NondegMetric.laplaceCoord_chart_change` (**chart independence**): the coordinate Laplacians of two charts agree at
  every point of the overlap, because both satisfy the same weak identity, whose right side `g⁻¹(dψ, df)` does not
  depend on the chart (`NondegMetric.dualPair_eq_coord`), and both are continuous;
* `NondegMetric.laplaceBeltrami_eq_coord`: so `Δ_g f (x)` may be computed in any chart containing `x`.

The proof uses no second-order chain rule: the weak form and the fundamental lemma of the calculus of variations on a
manifold (`IsOpen.ae_eq_zero_of_integral_contMDiff_smul_eq_zero`) replace it.
-/

open MeasureTheory Set Manifold Matrix Filter
open scoped ContDiff Topology
noncomputable section
namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  [MeasurableSpace M] [BorelSpace M]
  (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)

/-- `g⁻¹(dψ, df)` vanishes outside the topological support of `ψ`. -/
theorem NondegMetric.dualPair_eq_zero_of_notMem_tsupport {ψ : M → ℝ} (f : M → ℝ) {x : M} (hx : x ∉ tsupport ψ) :
    g.dualPair ψ f x = 0 := by
  have hev : ψ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm =ᶠ[𝓝 (extChartAt 𝓘(ℝ, Fin n → ℝ) x x)] fun _ => 0 := by
    have h1 : ψ =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 hx
    have h2 := continuousAt_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) x
    rw [ContinuousAt, extChartAt_to_inv (I := 𝓘(ℝ, Fin n → ℝ)) x] at h2
    exact h2.eventually h1
  unfold NondegMetric.dualPair NondegMetric.dualPairCoord coordPartial
  rw [hev.fderiv_eq]
  simp

section Transport

/-- The function `ψ ∘ φ₀⁻¹` on the chart target, extended by `0`. -/
def chartPush (x₀ : M) (ψ : M → ℝ) : (Fin n → ℝ) → ℝ :=
  (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target.indicator (ψ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm)

variable {x₀ : M} {ψ : M → ℝ}

theorem chartPush_eq_zero_of_notMem (x₀ : M) (ψ : M → ℝ) {y : Fin n → ℝ}
    (hy : y ∉ extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' tsupport ψ) : chartPush (n := n) x₀ ψ y = 0 := by
  unfold chartPush
  by_cases hyt : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target
  · rw [indicator_of_mem hyt, Function.comp_apply]
    refine image_eq_zero_of_notMem_tsupport fun h => hy ⟨_, h, ?_⟩
    exact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv hyt
  · exact indicator_of_notMem hyt _

theorem isCompact_image_tsupport (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    IsCompact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' tsupport ψ) :=
  hψc.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hψs)

theorem image_tsupport_subset_target (hψs : tsupport ψ ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' tsupport ψ ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
  rintro _ ⟨p, hp, rfl⟩; exact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (hψs hp)

theorem tsupport_chartPush_subset (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    tsupport (chartPush (n := n) x₀ ψ) ⊆ extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' tsupport ψ :=
  closure_minimal (fun y hy => by_contra fun h => hy (chartPush_eq_zero_of_notMem x₀ ψ h))
    (isCompact_image_tsupport hψc hψs).isClosed

theorem hasCompactSupport_chartPush (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) : HasCompactSupport (chartPush (n := n) x₀ ψ) :=
  (isCompact_image_tsupport hψc hψs).of_isClosed_subset (isClosed_tsupport _) (tsupport_chartPush_subset hψc hψs)

theorem chartPush_eventuallyEq (x₀ : M) (ψ : M → ℝ) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    chartPush (n := n) x₀ ψ =ᶠ[𝓝 y] ψ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm := by
  filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds hy] with z hz
  exact indicator_of_mem hz _

/-- **The pushed test function is smooth with compact support in the chart target.** -/
theorem contDiff_chartPush (hψ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) : ContDiff ℝ ∞ (chartPush (n := n) x₀ ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hyt : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target
  · exact (((contDiffOn_chart_comp hψ x₀).contDiffAt
      ((isOpen_extChartAt_target x₀).mem_nhds hyt))).congr_of_eventuallyEq (chartPush_eventuallyEq x₀ ψ hyt)
  · have hyK : y ∉ extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' tsupport ψ := fun h => hyt (image_tsupport_subset_target hψs h)
    have hev : chartPush (n := n) x₀ ψ =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [(isCompact_image_tsupport hψc hψs).isClosed.isOpen_compl.mem_nhds hyK] with z hz
      exact chartPush_eq_zero_of_notMem x₀ ψ hz
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem fderiv_chartPush (x₀ : M) (ψ : M → ℝ) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (i : Fin n) : fderiv ℝ (chartPush (n := n) x₀ ψ) y (Pi.single i 1) = coordPartial x₀ ψ y i := by
  unfold coordPartial; rw [(chartPush_eventuallyEq x₀ ψ hy).fderiv_eq]

theorem tsupport_chartPush_subset_target (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    tsupport (chartPush (n := n) x₀ ψ) ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
  (tsupport_chartPush_subset hψc hψs).trans (image_tsupport_subset_target hψs)

end Transport

section Weak

/-- The coordinate Laplacian of the chart at `x₀`, as a function on the manifold. -/
def NondegMetric.laplaceAt (x₀ : M) (f : M → ℝ) (x : M) : ℝ :=
  g.laplaceCoord x₀ f (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x)

theorem NondegMetric.continuousOn_laplaceAt {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f) (x₀ : M) :
    ContinuousOn (g.laplaceAt x₀ f) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source :=
  (g.contDiffOn_laplaceCoord hf x₀).continuousOn.comp (continuousOn_extChartAt x₀)
    fun _ hx => (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hx

theorem NondegMetric.continuousOn_dualPair {f ψ : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f)
    (hψ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ ψ) (x₀ : M) :
    ContinuousOn (g.dualPair ψ f) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source := by
  have hc : ContinuousOn (g.dualPairCoord x₀ ψ f) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
    unfold NondegMetric.dualPairCoord
    exact continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      (((g.contDiffOn_coordMetric_inv x₀ i j).continuousOn.mul (contDiffOn_coordPartial hψ x₀ i).continuousOn).mul
        (contDiffOn_coordPartial hf x₀ j).continuousOn)
  refine (hc.comp (continuousOn_extChartAt x₀) fun _ hx => (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hx).congr
    fun x hx => ?_
  exact g.dualPair_eq_coord hψ hf x₀ x hx

/-- **The weak form of the Laplacian on the manifold**: for `ψ` smooth with compact support in the domain of the chart
at `x₀`, `∫_M ψ · Δ₀f dvol_g = ∫_M g⁻¹(dψ, df) dvol_g`. -/
theorem NondegMetric.integral_mul_laplaceAt_eq_dualPair {f ψ : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f)
    (hψ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ ψ) (hψc : HasCompactSupport ψ) (x₀ : M)
    (hψs : tsupport ψ ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    ∫ x, ψ x * g.laplaceAt x₀ f x ∂g.volumeMeasure = ∫ x, g.dualPair ψ f x ∂g.volumeMeasure := by
  set φ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hφ
  have hsrc : MeasurableSet φ.source := (isOpen_extChartAt_source x₀).measurableSet
  have htgt : MeasurableSet φ.target := (isOpen_extChartAt_target x₀).measurableSet
  set Ψ := chartPush (n := n) x₀ ψ with hΨ
  -- both integrals live on the chart domain
  have hL0 : ∀ x ∉ φ.source, ψ x * g.laplaceAt x₀ f x = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (hψs h), zero_mul]
  have hR0 : ∀ x ∉ φ.source, g.dualPair ψ f x = 0 := fun x hx =>
    g.dualPair_eq_zero_of_notMem_tsupport f fun h => hx (hψs h)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hL0,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hR0]
  have hmL : AEStronglyMeasurable (fun x => ψ x * g.laplaceAt x₀ f x) (g.volumeMeasure.restrict φ.source) :=
    (hψ.continuous.continuousOn.mul (g.continuousOn_laplaceAt hf x₀)).aestronglyMeasurable hsrc
  have hmR : AEStronglyMeasurable (g.dualPair ψ f) (g.volumeMeasure.restrict φ.source) :=
    (g.continuousOn_dualPair hf hψ x₀).aestronglyMeasurable hsrc
  rw [g.integral_chart x₀ hmL, g.integral_chart x₀ hmR]
  -- in the chart: the weak form on `ℝⁿ`
  have hl : ∫ y in φ.target, g.volDensity x₀ y * (ψ (φ.symm y) * g.laplaceAt x₀ f (φ.symm y)) =
      ∫ y, Ψ y * (g.volDensity x₀ y * g.laplaceCoord x₀ f y) := by
    have h0 : ∀ y ∉ φ.target, Ψ y * (g.volDensity x₀ y * g.laplaceCoord x₀ f y) = 0 := fun y hy => by
      rw [show Ψ y = 0 from indicator_of_notMem hy _, zero_mul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h0]
    refine setIntegral_congr_fun htgt fun y hy => ?_
    have hΨy : Ψ y = ψ (φ.symm y) := by
      rw [hΨ, chartPush, indicator_of_mem hy, Function.comp_apply]
    have hφy : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (φ.symm y) = y := φ.right_inv hy
    rw [hΨy]
    simp only [NondegMetric.laplaceAt, hφy]
    ring
  have hr : ∫ y in φ.target, g.volDensity x₀ y * g.dualPair ψ f (φ.symm y) =
      ∫ y, g.volDensity x₀ y *
        ∑ i, ∑ j, (g.coordMetric x₀ y)⁻¹ i j * fderiv ℝ Ψ y (Pi.single i 1) * coordPartial x₀ f y j := by
    have h0 : ∀ y ∉ φ.target, g.volDensity x₀ y *
        ∑ i, ∑ j, (g.coordMetric x₀ y)⁻¹ i j * fderiv ℝ Ψ y (Pi.single i 1) * coordPartial x₀ f y j = 0 :=
      fun y hy => by
        have : ∀ i, fderiv ℝ Ψ y (Pi.single i 1) = 0 := fun i =>
          image_eq_zero_of_notMem_tsupport (f := fun z => fderiv ℝ Ψ z (Pi.single i 1)) fun h =>
            hy (tsupport_chartPush_subset_target hψc hψs (tsupport_fderiv_apply_subset ℝ _ h))
        simp [this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h0]
    refine setIntegral_congr_fun htgt fun y hy => ?_
    rw [g.dualPair_eq_coord hψ hf x₀ _ (φ.map_target hy), φ.right_inv hy]
    have hd : ∀ i, fderiv ℝ Ψ y (Pi.single i 1) = coordPartial x₀ ψ y i := fun i => by
      rw [hΨ]; exact fderiv_chartPush (n := n) x₀ ψ hy i
    simp only [NondegMetric.dualPairCoord, hd]
  rw [hl, hr]
  exact g.integral_mul_laplaceCoord hf x₀ (contDiff_chartPush hψ hψc hψs) (hasCompactSupport_chartPush hψc hψs)
    (tsupport_chartPush_subset_target hψc hψs)

/-- **The coordinate Laplacians of two charts agree on the overlap.** -/
theorem NondegMetric.laplaceAt_chart_change {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f) (x₀ x₁ : M)
    {x : M} (hx0 : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (hx1 : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source) :
    g.laplaceAt x₀ f x = g.laplaceAt x₁ f x := by
  have := g.isLocallyFiniteMeasure_volumeMeasure
  have := g.isOpenPosMeasure_volumeMeasure
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Fin n → ℝ) M
  set W := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source ∩ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source with hW
  have hWo : IsOpen W := (isOpen_extChartAt_source x₀).inter (isOpen_extChartAt_source x₁)
  set D := fun y => g.laplaceAt x₀ f y - g.laplaceAt x₁ f y with hD
  have hDc : ContinuousOn D W :=
    ((g.continuousOn_laplaceAt hf x₀).mono inter_subset_left).sub
      ((g.continuousOn_laplaceAt hf x₁).mono inter_subset_right)
  have hae : ∀ᵐ y ∂g.volumeMeasure, y ∈ W → D y = 0 := by
    refine hWo.ae_eq_zero_of_integral_contMDiff_smul_eq_zero 𝓘(ℝ, Fin n → ℝ)
      (hDc.locallyIntegrableOn hWo.measurableSet) fun ψ hψ hψc hψs => ?_
    have h0 := g.integral_mul_laplaceAt_eq_dualPair hf hψ hψc x₀ (hψs.trans inter_subset_left)
    have h1 := g.integral_mul_laplaceAt_eq_dualPair hf hψ hψc x₁ (hψs.trans inter_subset_right)
    have hi : ∀ x₂ : M, tsupport ψ ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₂).source →
        Integrable (fun y => ψ y * g.laplaceAt x₂ f y) g.volumeMeasure := fun x₂ hs =>
      (continuous_mul_of_tsupport_subset (isOpen_extChartAt_source x₂) hψ.continuous
        (g.continuousOn_laplaceAt hf x₂) hs).integrable_of_hasCompactSupport hψc.mul_right
    simp only [smul_eq_mul, hD, mul_sub]
    rw [integral_sub (hi x₀ (hψs.trans inter_subset_left)) (hi x₁ (hψs.trans inter_subset_right)), h0, h1,
      sub_self]
  by_contra hne
  have hxD : D x ≠ 0 := sub_ne_zero.2 hne
  set O := W ∩ D ⁻¹' {0}ᶜ with hO
  have hOo : IsOpen O := hDc.isOpen_inter_preimage hWo isOpen_compl_singleton
  have hpos : 0 < g.volumeMeasure O := hOo.measure_pos _ ⟨x, ⟨hx0, hx1⟩, hxD⟩
  have hnull : g.volumeMeasure O = 0 := by
    refine measure_mono_null (fun y hy => ?_) (ae_iff.1 hae)
    simp only [mem_setOf_eq, not_imp]
    exact ⟨hy.1, hy.2⟩
  exact hpos.ne' hnull

/-- **The Laplace–Beltrami operator may be computed in any chart** containing the point. -/
theorem NondegMetric.laplaceBeltrami_eq_coord {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f) (x₀ : M)
    {x : M} (hx0 : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    g.laplaceBeltrami f x = g.laplaceCoord x₀ f (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x) :=
  (g.laplaceAt_chart_change hf x₀ x hx0 (mem_extChartAt_source x)).symm

/-- **The weak form with the Laplace–Beltrami operator**: for `ψ` smooth with compact support in a chart domain,
`∫_M ψ Δ_g f dvol_g = ∫_M g⁻¹(dψ, df) dvol_g`. -/
theorem NondegMetric.integral_mul_laplaceBeltrami_chart {f ψ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f) (hψ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ ψ)
    (hψc : HasCompactSupport ψ) (x₀ : M) (hψs : tsupport ψ ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    ∫ x, ψ x * g.laplaceBeltrami f x ∂g.volumeMeasure = ∫ x, g.dualPair ψ f x ∂g.volumeMeasure := by
  rw [← g.integral_mul_laplaceAt_eq_dualPair hf hψ hψc x₀ hψs]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport ψ
  · change ψ x * g.laplaceBeltrami f x = ψ x * g.laplaceAt x₀ f x
    rw [g.laplaceBeltrami_eq_coord hf x₀ (hψs hx)]; rfl
  · simp [image_eq_zero_of_notMem_tsupport hx]

end Weak

end Lightlike
