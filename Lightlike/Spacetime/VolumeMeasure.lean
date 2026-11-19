import Lightlike.Spacetime.ChartAgreement
import Lightlike.Spacetime.Minkowski
import Lightlike.Spacetime.NondegMetric
/-!
# The volume measure of a metric on a manifold

For a second countable Hausdorff `C²` manifold `M` modelled on `ℝⁿ` (with its Borel `σ`-algebra) and a smooth symmetric nondegenerate bilinear field `g` (`NondegMetric`: a metric of any signature, in particular a
Lorentzian metric or a Riemannian metric of Mathlib; the Lorentzian case, with the names `volumeMeasure`, `volDensity`, ... and
the statements of the first version, is at the end of the file),
`NondegMetric.volumeMeasure g` is the measure of the volume form: in each chart the pushforward of `√|det g| dx` (`NondegMetric.volDensity`), the charts
being those of a countable atlas (`atlasPts`) cut into disjoint pieces (`atlasPiece`).

## Main results

* `NondegMetric.volumeMeasure_apply`: the measure of a measurable set is the sum over the atlas pieces of the integrals of the density
  over the chart images of its parts.
* `NondegMetric.volumeMeasure_chart` (**the chart formula**): for a measurable set `A` in the domain of *any* chart `x₀`,
  `NondegMetric.volumeMeasure g A = ∫_{ψ₀(A)} √|det g_{x₀}| dx`. In particular the measure does not depend on the atlas used in the
  definition: it is the unique measure with this property on subsets of chart domains.
* `NondegMetric.coordMetric_chart_change`, `NondegMetric.volDensity_chart_change`, `NondegMetric.lintegral_density_chart_change`: the metric transforms like a
  tensor under a change of chart, the density by the absolute value of the Jacobian determinant, and the change of variables.
* `volumeMeasure_minkowski`: trust check, the volume of Minkowski space is Lebesgue measure.

**Limits.** Dimension `n` charts `Fin n → ℝ`, no boundary, Hausdorff and second countable, `C²`. The density is
`√|det g|`, which for a Lorentzian metric is `√(-det g)`. The measure is a measure on the Borel sets of `M`; no orientation is
used. `σ`-finiteness and local finiteness are not proved here.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix
open scoped ContDiff ENNReal Topology
noncomputable section
namespace Lightlike
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]

/-- A countable set of points of `M` whose chart domains cover `M`. -/
def atlasPts (M : Type*) [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [SecondCountableTopology M] : Set M :=
  Classical.choose (countable_cover_nhds (f := fun x : M => (chartAt (Fin n → ℝ) x).source)
    (fun x => (chartAt (Fin n → ℝ) x).open_source.mem_nhds (mem_chart_source _ x)))

/-- The chosen set of chart centres is countable. -/
theorem atlasPts_countable : (atlasPts (n := n) M).Countable :=
  (Classical.choose_spec (countable_cover_nhds (f := fun x : M => (chartAt (Fin n → ℝ) x).source)
    (fun x => (chartAt (Fin n → ℝ) x).open_source.mem_nhds (mem_chart_source _ x)))).1

/-- The chart domains of the chosen centres cover `M`. -/
theorem atlasPts_cover : ⋃ x ∈ atlasPts (n := n) M, (chartAt (Fin n → ℝ) x).source = univ :=
  (Classical.choose_spec (countable_cover_nhds (f := fun x : M => (chartAt (Fin n → ℝ) x).source)
    (fun x => (chartAt (Fin n → ℝ) x).open_source.mem_nhds (mem_chart_source _ x)))).2

variable [MeasurableSpace M] [BorelSpace M]
variable (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)

/-- The index type of the countable atlas. -/
abbrev AtlasIdx (M : Type*) [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [SecondCountableTopology M] : Type _ :=
  ↥(atlasPts (n := n) M)

/-- The index type of the atlas is encodable. -/
instance : Encodable (AtlasIdx (n := n) M) := haveI := (atlasPts_countable (n := n) (M := M)).to_subtype; Encodable.ofCountable _

/-- The chart centre of an index. -/
def AtlasIdx.pt (i : AtlasIdx (n := n) M) : M := i.1

/-- The part of the chart domain of `i` not covered by the earlier charts. -/
def atlasPiece (i : AtlasIdx (n := n) M) : Set M :=
  (chartAt (Fin n → ℝ) i.1).source \ ⋃ j ∈ {j : AtlasIdx (n := n) M | Encodable.encode j < Encodable.encode i},
    (chartAt (Fin n → ℝ) j.1).source

/-- The volume density `√|det g|` of the coordinate components in the chart at `x₀`. -/
def NondegMetric.volDensity (x₀ : M) (y : Fin n → ℝ) : ℝ := √|(g.coordMetric x₀ y).det|

/-- **The volume measure of a metric** (relative to the chosen countable atlas): on each piece of the atlas, the pushforward
of `√|det g| dx`. -/
def NondegMetric.volumeMeasure : Measure M :=
  Measure.sum fun i : AtlasIdx (n := n) M =>
    Measure.map (extChartAt 𝓘(ℝ, Fin n → ℝ) i.1).symm
      (((volume : Measure (Fin n → ℝ)).restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) i.1 '' atlasPiece i)).withDensity
        fun y => ENNReal.ofReal (NondegMetric.volDensity g i.1 y))

/-- Each atlas piece is measurable. -/
theorem measurableSet_atlasPiece (i : AtlasIdx (n := n) M) : MeasurableSet (atlasPiece i) := by
  unfold atlasPiece
  refine ((chartAt (Fin n → ℝ) i.1).open_source.measurableSet).diff ?_
  exact MeasurableSet.biUnion (Set.to_countable _) fun j _ => (chartAt (Fin n → ℝ) j.1).open_source.measurableSet

/-- An atlas piece lies in its chart domain. -/
theorem atlasPiece_subset (i : AtlasIdx (n := n) M) : atlasPiece i ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) i.1).source := by
  intro x hx
  rw [extChartAt_source]; exact hx.1

/-- The image under the chart of a measurable subset of the chart domain is measurable. -/
theorem measurableSet_image_extChartAt (x₀ : M) {D : Set M} (hD : MeasurableSet D)
    (hDs : D ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    MeasurableSet (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' D) := by
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀
  have hT : MeasurableSet ψ.target := (isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x₀).measurableSet
  have hc : Continuous (fun y : ψ.target => ψ.symm y) :=
    continuousOn_iff_continuous_domRestrict.1 (continuousOn_extChartAt_symm x₀)
  have hm : MeasurableSet ((fun y : ψ.target => ψ.symm y) ⁻¹' D) := hc.measurable hD
  have := MeasurableSet.subtype_image hT hm
  convert this using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨ψ x, ψ.map_source (hDs hx)⟩, by simp [ψ.left_inv (hDs hx), hx], rfl⟩
  · rintro ⟨⟨y, hy⟩, hyD, rfl⟩
    exact ⟨ψ.symm y, hyD, ψ.right_inv hy⟩

/-- The chart image of an atlas piece is measurable. -/
theorem measurableSet_image_atlasPiece (i : AtlasIdx (n := n) M) :
    MeasurableSet (extChartAt 𝓘(ℝ, Fin n → ℝ) i.1 '' atlasPiece i) :=
  measurableSet_image_extChartAt i.1 (measurableSet_atlasPiece i) (atlasPiece_subset i)

/-- The measure of a measurable set `A` is the sum over the pieces of the integrals of the density over the chart images
of the parts of `A` in the pieces. -/
theorem NondegMetric.volumeMeasure_apply {A : Set M} (hA : MeasurableSet A) :
    NondegMetric.volumeMeasure g A = ∑' i : AtlasIdx (n := n) M,
      ∫⁻ y in extChartAt 𝓘(ℝ, Fin n → ℝ) i.1 '' (A ∩ atlasPiece i), ENNReal.ofReal (NondegMetric.volDensity g i.1 y) := by
  unfold NondegMetric.volumeMeasure
  rw [Measure.sum_apply _ hA]
  refine tsum_congr fun i => ?_
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) i.1 with hψ
  have hD := measurableSet_image_atlasPiece i
  have hae : AEMeasurable ψ.symm (((volume : Measure (Fin n → ℝ)).restrict (ψ '' atlasPiece i)).withDensity
      fun y => ENNReal.ofReal (NondegMetric.volDensity g i.1 y)) := by
    refine AEMeasurable.mono_ac ?_ (withDensity_absolutelyContinuous _ _)
    refine ContinuousOn.aemeasurable ?_ hD
    exact (continuousOn_extChartAt_symm i.1).mono (by
      rintro _ ⟨x, hx, rfl⟩; exact ψ.map_source (atlasPiece_subset i hx))
  rw [Measure.map_apply_of_aemeasurable hae hA, withDensity_apply' _, Measure.restrict_restrict' hD]
  congr 2
  ext y
  constructor
  · rintro ⟨hyA, x, hx, rfl⟩
    refine ⟨x, ⟨?_, hx⟩, rfl⟩
    simp only [mem_preimage] at hyA
    rwa [ψ.left_inv (atlasPiece_subset i hx)] at hyA
  · rintro ⟨x, ⟨hxA, hx⟩, rfl⟩
    exact ⟨by simp only [mem_preimage]; rwa [ψ.left_inv (atlasPiece_subset i hx)], x, hx, rfl⟩

/-- The chart-change linear map at `p`: from the components in the chart at `x₀` to the components in the chart at `x₁`. -/
def chgL (x₀ x₁ p : M) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (trivializationAt (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ) : M → Type _) x₁).continuousLinearMapAt ℝ p ∘L
    (trivializationAt (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ) : M → Type _) x₀).symmL ℝ p

/-- `g(∂ₐ, ∂_b)` is the coordinate component, for a metric of any signature. -/
theorem NondegMetric.g_coordField (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) (a b : Fin n) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    g.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) (coordField x₀ a ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
      (coordField x₀ b ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) = g.coordMetric x₀ y a b := by
  rw [coordField_apply x₀ a hy, coordField_apply x₀ b hy, g.coordMetric_eq x₀ hy]

/-- **The metric transforms like a tensor under a change of chart**: `g₀(a, b) = Σ C_{μa} g₁(μ, ν) C_{νb}` with `C` the chart-change
map. -/
theorem NondegMetric.coordMetric_chart_change (x₀ x₁ : M) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (hp₁ : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∈ (chartAt (Fin n → ℝ) x₁).source) (a b : Fin n) :
    g.coordMetric x₀ y a b = ∑ μ, ∑ ν, chgL x₀ x₁ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) (Pi.single a 1) μ *
      g.coordMetric x₁ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) μ ν *
      chgL x₀ x₁ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) (Pi.single b 1) ν := by
  set ψ₀ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hψ₀
  set ψ₁ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ with hψ₁
  set p := ψ₀.symm y with hp
  have hb0 : p ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet := symm_mem_chartTriv_baseSet x₀ hy
  have hb1 : p ∈ (tTriv (E := Fin n → ℝ) x₁).baseSet := by
    simpa [tTriv, TangentBundle.trivializationAt_baseSet] using hp₁
  have hs1 : p ∈ ψ₁.source := by rw [hψ₁, extChartAt_source]; exact hp₁
  have hy1 : ψ₁ p ∈ ψ₁.target := ψ₁.map_source hs1
  have h0 := NondegMetric.g_coordField g x₀ a b hy
  have h1 := fun m n' => NondegMetric.g_coordField g x₁ m n' hy1
  rw [← hp] at h0
  rw [ψ₁.left_inv hs1] at h1
  rw [← h0]
  have hexp : ∀ c : Fin n, coordField x₀ c p = ∑ μ, chgL x₀ x₁ p (Pi.single c 1) μ • coordField x₁ μ p := by
    intro c
    rw [← symmL_eq_coordField x₀ hb0 c]
    have : (tTriv (E := Fin n → ℝ) x₀).symmL ℝ p (Pi.single c 1) =
        (tTriv (E := Fin n → ℝ) x₁).symmL ℝ p (chgL x₀ x₁ p (Pi.single c 1)) := by
      unfold chgL
      simp only [ContinuousLinearMap.comp_apply]
      exact ((tTriv (E := Fin n → ℝ) x₁).symmL_continuousLinearMapAt hb1 _).symm
    rw [this]
    conv_lhs => rw [show chgL x₀ x₁ p (Pi.single c 1) = ∑ μ, chgL x₀ x₁ p (Pi.single c 1) μ • (Pi.single μ 1 : Fin n → ℝ) by
      ext k; simp [Finset.sum_apply, Pi.single_apply]]
    simp only [map_sum, map_smul, symmL_eq_coordField x₁ hb1]
  rw [hexp a, hexp b]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [h1 ν μ]
  ring

/-- The chart-change map is the derivative of the coordinate change. -/
theorem chgL_eq (x₀ x₁ p : M) (hp0 : p ∈ (chartAt (Fin n → ℝ) x₀).source)
    (hp1 : p ∈ (chartAt (Fin n → ℝ) x₁).source) :
    chgL x₀ x₁ p = fderiv ℝ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) := by
  unfold chgL
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hp1,
    TangentBundle.symmL_trivializationAt_eq_core hp0]
  have hx : p ∈ (tangentBundleCore 𝓘(ℝ, Fin n → ℝ) M).baseSet (achart (Fin n → ℝ) x₀) ∩
      (tangentBundleCore 𝓘(ℝ, Fin n → ℝ) M).baseSet (achart (Fin n → ℝ) p) ∩
      (tangentBundleCore 𝓘(ℝ, Fin n → ℝ) M).baseSet (achart (Fin n → ℝ) x₁) :=
    ⟨⟨hp0, mem_chart_source _ p⟩, hp1⟩
  have key := VectorBundleCore.coordChange_linear_comp (tangentBundleCore 𝓘(ℝ, Fin n → ℝ) M)
    (achart (Fin n → ℝ) x₀) (achart (Fin n → ℝ) p) (achart (Fin n → ℝ) x₁) p hx
  refine Eq.trans key ?_
  rw [tangentBundleCore_coordChange_achart, ModelWithCorners.range_eq_univ, fderivWithin_univ]

/-- **The density transforms with the absolute value of the Jacobian**: `√|det g₀| = |det C| √|det g₁|` at a point of both charts. -/
theorem NondegMetric.volDensity_chart_change (x₀ x₁ p : M) (hp0 : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (hp1 : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source) :
    NondegMetric.volDensity g x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) =
      |LinearMap.det (chgL (n := n) x₀ x₁ p).toLinearMap| *
        NondegMetric.volDensity g x₁ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ p) := by
  set ψ₀ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀
  have hy : ψ₀ p ∈ ψ₀.target := ψ₀.map_source hp0
  have hp1' : ψ₀.symm (ψ₀ p) ∈ (chartAt (Fin n → ℝ) x₁).source := by
    rw [ψ₀.left_inv hp0]; rwa [extChartAt_source] at hp1
  have hmat : g.coordMetric x₀ (ψ₀ p) =
      (LinearMap.toMatrix' (chgL (n := n) x₀ x₁ p).toLinearMap)ᵀ *
        g.coordMetric x₁ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ p) *
        LinearMap.toMatrix' (chgL (n := n) x₀ x₁ p).toLinearMap := by
    ext a b
    have := NondegMetric.coordMetric_chart_change g x₀ x₁ hy hp1' a b
    rw [ψ₀.left_inv hp0] at this
    rw [this]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  unfold NondegMetric.volDensity
  rw [hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix']
  rw [show (LinearMap.det (chgL (n := n) x₀ x₁ p).toLinearMap) * (g.coordMetric x₁ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ p)).det *
      LinearMap.det (chgL (n := n) x₀ x₁ p).toLinearMap = (LinearMap.det (chgL (n := n) x₀ x₁ p).toLinearMap) ^ 2 *
      (g.coordMetric x₁ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ p)).det by ring, abs_mul, abs_pow, Real.sqrt_mul (by positivity),
    Real.sqrt_sq_eq_abs, abs_abs]

/-- **Change of variables between two charts**: the integral of the density over the image of a measurable set `E` contained in both
chart domains is the same in the two charts. -/
theorem NondegMetric.lintegral_density_chart_change (x₀ x₁ : M) {E : Set M} (hE : MeasurableSet E)
    (hE0 : E ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (hE1 : E ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source) :
    ∫⁻ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' E, ENNReal.ofReal (NondegMetric.volDensity g x₁ y) =
      ∫⁻ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' E, ENNReal.ofReal (NondegMetric.volDensity g x₀ y) := by
  set ψ₀ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hψ₀
  set ψ₁ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ with hψ₁
  set f : (Fin n → ℝ) → (Fin n → ℝ) := ψ₁ ∘ ψ₀.symm with hf
  have hs : MeasurableSet (ψ₀ '' E) := measurableSet_image_extChartAt x₀ hE hE0
  have himg : f '' (ψ₀ '' E) = ψ₁ '' E := by
    rw [← image_comp]
    refine image_congr fun x hx => ?_
    simp [hf, ψ₀.left_inv (hE0 hx)]
  have hinj : InjOn f (ψ₀ '' E) := by
    intro y hy y' hy' h
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨x', hx', rfl⟩ := hy'
    simp only [hf, Function.comp_apply, ψ₀.left_inv (hE0 hx), ψ₀.left_inv (hE0 hx')] at h
    have : x = x' := by
      have h1 := ψ₁.injOn (by rw [hψ₁, extChartAt_source] at *; exact hE1 hx) (by exact hE1 hx') h
      exact h1
    rw [this]
  have hder : ∀ y ∈ ψ₀ '' E, HasFDerivWithinAt f (fderiv ℝ f y) (ψ₀ '' E) y := by
    rintro _ ⟨x, hx, rfl⟩
    have hd : DifferentiableAt ℝ f (ψ₀ x) := by
      have := contDiffWithinAt_ext_coord_change (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) x₁ x₀
        (y := ψ₀ x) (by
          simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, mem_inter_iff, mem_preimage]
          exact ⟨ψ₀.map_source (hE0 hx), by rw [ψ₀.left_inv (hE0 hx)]; exact hE1 hx⟩)
      rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at this
      exact this.differentiableAt (by simp)
    exact hd.hasFDerivAt.hasFDerivWithinAt
  rw [← himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hder hinj]
  refine setLIntegral_congr_fun hs ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx0 := hE0 hx
  have hx1 := hE1 hx
  have hC : fderiv ℝ f (ψ₀ x) = chgL x₀ x₁ x := by
    rw [chgL_eq x₀ x₁ x (by rwa [extChartAt_source] at hx0) (by rwa [extChartAt_source] at hx1)]
  have hdens := NondegMetric.volDensity_chart_change g x₀ x₁ x hx0 hx1
  have hfx : f (ψ₀ x) = ψ₁ x := by simp [hf, ψ₀.left_inv hx0]
  show ENNReal.ofReal |(fderiv ℝ f (ψ₀ x)).det| * ENNReal.ofReal (NondegMetric.volDensity g x₁ (f (ψ₀ x))) =
    ENNReal.ofReal (NondegMetric.volDensity g x₀ (ψ₀ x))
  rw [hfx, hdens, hC, ← ENNReal.ofReal_mul (abs_nonneg _)]

/-- The atlas pieces are pairwise disjoint. -/
theorem atlasPiece_disjoint : Pairwise (Function.onFun Disjoint (atlasPiece (n := n) (M := M))) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro x hxi hxj
  rcases lt_or_gt_of_ne (fun h => hij (Encodable.encode_injective h)) with h | h
  · exact hxj.2 (mem_biUnion (x := i) h hxi.1)
  · exact hxi.2 (mem_biUnion (x := j) h hxj.1)

/-- The atlas pieces cover `M`. -/
theorem iUnion_atlasPiece : ⋃ i : AtlasIdx (n := n) M, atlasPiece i = univ := by
  refine eq_univ_of_forall fun x => ?_
  have hx := atlasPts_cover (n := n) (M := M)
  have : x ∈ ⋃ y ∈ atlasPts (n := n) M, (chartAt (Fin n → ℝ) y).source := by rw [hx]; trivial
  simp only [mem_iUnion] at this
  obtain ⟨y, hy, hxy⟩ := this
  classical
  have hex : ∃ k : ℕ, ∃ j : AtlasIdx (n := n) M, Encodable.encode j = k ∧ x ∈ (chartAt (Fin n → ℝ) j.1).source :=
    ⟨_, ⟨y, hy⟩, rfl, hxy⟩
  obtain ⟨j, hjk, hxj⟩ := Nat.find_spec hex
  refine mem_iUnion.2 ⟨j, hxj, ?_⟩
  simp only [mem_iUnion, not_exists]
  intro j' hlt hxj'
  have := Nat.find_min hex (m := Encodable.encode j') (by rw [← hjk]; exact hlt) ⟨j', rfl, hxj'⟩
  exact this

/-- **The chart formula**: for a measurable set `A` in the domain of the chart at `x₀`, the volume of `A` is the integral of
`√|det g|` over the image of `A` in that chart. -/
theorem NondegMetric.volumeMeasure_chart (x₀ : M) {A : Set M} (hA : MeasurableSet A)
    (hA0 : A ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    NondegMetric.volumeMeasure g A =
      ∫⁻ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A, ENNReal.ofReal (NondegMetric.volDensity g x₀ y) := by
  rw [NondegMetric.volumeMeasure_apply g hA]
  set ψ₀ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hψ₀
  have hpiece : ∀ i : AtlasIdx (n := n) M,
      ∫⁻ y in extChartAt 𝓘(ℝ, Fin n → ℝ) i.1 '' (A ∩ atlasPiece i), ENNReal.ofReal (NondegMetric.volDensity g i.1 y) =
        ∫⁻ y in ψ₀ '' (A ∩ atlasPiece i), ENNReal.ofReal (NondegMetric.volDensity g x₀ y) := fun i =>
    NondegMetric.lintegral_density_chart_change g x₀ i.1 (hA.inter (measurableSet_atlasPiece i))
      (inter_subset_left.trans hA0) (inter_subset_right.trans (atlasPiece_subset i))
  simp only [hpiece]
  have hU : ψ₀ '' A = ⋃ i : AtlasIdx (n := n) M, ψ₀ '' (A ∩ atlasPiece i) := by
    rw [← image_iUnion, ← inter_iUnion, iUnion_atlasPiece, inter_univ]
  rw [hU, lintegral_iUnion]
  · intro i
    exact measurableSet_image_extChartAt x₀ (hA.inter (measurableSet_atlasPiece i)) (inter_subset_left.trans hA0)
  · intro i j hij
    have hinj : InjOn ψ₀ ψ₀.source := ψ₀.injOn
    have h1 : A ∩ atlasPiece i ⊆ ψ₀.source := inter_subset_left.trans hA0
    have h2 : A ∩ atlasPiece j ⊆ ψ₀.source := inter_subset_left.trans hA0
    rw [Function.onFun, Set.disjoint_iff_inter_eq_empty, ← hinj.image_inter h1 h2]
    have : (A ∩ atlasPiece i) ∩ (A ∩ atlasPiece j) = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, hxi⟩, _, hxj⟩
      exact (Set.disjoint_left.1 (atlasPiece_disjoint (n := n) (M := M) hij)) hxi hxj
    rw [this, image_empty]

/-! ## The Lorentzian case

The volume measure of a Lorentzian metric and its properties, as consequences of the general ones. -/

section Lorentzian

variable (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)

/-- The volume density `√|det g|` of the coordinate components in the chart at `x₀`. -/
def volDensity (x₀ : M) (y : Fin n → ℝ) : ℝ :=
  NondegMetric.volDensity (NondegMetric.ofLorentzian g) x₀ y

/-- **The volume measure of a Lorentzian metric** (relative to the chosen countable atlas): on each piece of the atlas, the pushforward
of `√|det g| dx`. -/
def volumeMeasure : Measure M := NondegMetric.volumeMeasure (NondegMetric.ofLorentzian g)

/-- The measure of a measurable set `A` is the sum over the pieces of the integrals of the density over the chart images
of the parts of `A` in the pieces. -/
theorem volumeMeasure_apply {A : Set M} (hA : MeasurableSet A) :
    volumeMeasure g A = ∑' i : AtlasIdx (n := n) M,
      ∫⁻ y in extChartAt 𝓘(ℝ, Fin n → ℝ) i.1 '' (A ∩ atlasPiece i), ENNReal.ofReal (volDensity g i.1 y) :=
  NondegMetric.volumeMeasure_apply (NondegMetric.ofLorentzian g) hA

/-- **The metric transforms like a tensor under a change of chart**: `g₀(a, b) = Σ C_{μa} g₁(μ, ν) C_{νb}` with `C` the chart-change
map. -/
theorem coordMetric_chart_change (x₀ x₁ : M) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (hp₁ : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∈ (chartAt (Fin n → ℝ) x₁).source) (a b : Fin n) :
    g.coordMetric x₀ y a b = ∑ μ, ∑ ν, chgL x₀ x₁ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) (Pi.single a 1) μ *
      g.coordMetric x₁ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) μ ν *
      chgL x₀ x₁ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) (Pi.single b 1) ν :=
  NondegMetric.coordMetric_chart_change (NondegMetric.ofLorentzian g) x₀ x₁ hy hp₁ a b

/-- **The density transforms with the absolute value of the Jacobian**: `√|det g₀| = |det C| √|det g₁|` at a point of both charts. -/
theorem volDensity_chart_change (x₀ x₁ p : M) (hp0 : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (hp1 : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source) :
    volDensity g x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) =
      |LinearMap.det (chgL (n := n) x₀ x₁ p).toLinearMap| *
        volDensity g x₁ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ p) :=
  NondegMetric.volDensity_chart_change (NondegMetric.ofLorentzian g) x₀ x₁ p hp0 hp1

/-- **Change of variables between two charts**: the integral of the density over the image of a measurable set `E` contained in both
chart domains is the same in the two charts. -/
theorem lintegral_density_chart_change (x₀ x₁ : M) {E : Set M} (hE : MeasurableSet E)
    (hE0 : E ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (hE1 : E ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source) :
    ∫⁻ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' E, ENNReal.ofReal (volDensity g x₁ y) =
      ∫⁻ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' E, ENNReal.ofReal (volDensity g x₀ y) :=
  NondegMetric.lintegral_density_chart_change (NondegMetric.ofLorentzian g) x₀ x₁ hE hE0 hE1

/-- **The chart formula**: for a measurable set `A` in the domain of the chart at `x₀`, the volume of `A` is the integral of
`√|det g|` over the image of `A` in that chart. -/
theorem volumeMeasure_chart (x₀ : M) {A : Set M} (hA : MeasurableSet A)
    (hA0 : A ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    volumeMeasure g A =
      ∫⁻ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A, ENNReal.ofReal (volDensity g x₀ y) :=
  NondegMetric.volumeMeasure_chart (NondegMetric.ofLorentzian g) x₀ hA hA0

/-- **Trust check: the volume of Minkowski space is Lebesgue measure.** -/
theorem volumeMeasure_minkowski {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    volumeMeasure (minkowskiMetric n) A = volume A := by
  have hsrc : A ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) (0 : Fin n → ℝ)).source := by
    rw [extChartAt_model_space_eq_id]; exact subset_univ _
  rw [volumeMeasure_chart (minkowskiMetric n) 0 hA hsrc, extChartAt_model_space_eq_id]
  have hd : ∀ y, volDensity (minkowskiMetric n) (0 : Fin n → ℝ) y = 1 := fun y => by
    unfold volDensity NondegMetric.volDensity
    rw [minkowski_coordMetric, eta, Matrix.det_diagonal, Finset.abs_prod]
    have : ∀ i : Fin n, |etaDiag i| = 1 := fun i => by unfold etaDiag; split_ifs <;> simp
    simp [this]
  simp [hd]

end Lorentzian

end Lightlike
