import Lightlike.Spacetime.EHManifold.GHYBoundary
import Lightlike.Spacetime.EHManifold.ChartIntegrable

/-!
# The Gibbons–Hawking–York cancellation on a manifold (M16)

`eh_ghy_variation_manifold`: let `D` be a measurable region of a manifold with a metric `g`, given near every point of its
closure by a `C²` defining function `u` (`D = {u ≥ 0}`) with `du ≠ 0` and `du(♯du) ≠ 0` where `u = 0` (a nowhere null
boundary), and let `h` be a symmetric tensor field vanishing outside a compact set `K` and on the boundary of `D`. In the
graph charts of `divergence_theorem_manifold_open` for the boundary vector field `V(h)`, with chart weights `w a`
(compactly supported, summing to `1` on `K`), the Einstein–Hilbert action of `D ∩ K` minus the Gibbons–Hawking–York term
`Σ σ_ab ∫ ρ_ab w_a 2 √|h| K dy` of `g + t h` has the derivative `-∫_{D ∩ K} ⟨G + Λ g, h⟩_g d vol_g` at `t = 0`.

The proof: the bulk variation is `∫_{D ∩ K} (-⟨G + Λ g, h⟩_g + div_g V(h))` (`eh_variation_region_manifold`); by the
divergence theorem `∫_D div_g V(h)` is minus the sum of the chart fluxes of `w_a V(h)`, whose densities are the weighted
Palatini fluxes (`divField_smul_palatiniField`); at every graph point of positive weight the chart image of `D` is the
graph region nearby, so the graph is the image of `∂D`, `h` vanishes on it and it is not null (`graph_boundary_facts`),
and the weighted Gibbons–Hawking–York density is affine in `t` with slope minus the weighted flux
(`ghyGraph_chart_affine`); its integrands are continuous with compact support (`continuous_ghy_weighted`,
`continuous_flux_weighted`, `hasCompactSupport_weighted`), so the boundary terms cancel exactly.

## References

* E. Dyer, K. Hinterbichler, *Boundary Terms, Variational Principles and Higher Derivative Modified Gravity*,
  arXiv:0809.4033, section 4, eqs. (4.1) to (4.4), p. 20.
-/

open MeasureTheory Set Filter Topology Matrix Metric Bundle
open scoped ContDiff Manifold

noncomputable section

universe u

namespace Lightlike

section Helpers

set_option synthInstance.maxHeartbeats 400000

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin m → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin m → ℝ) ∞ M]

open scoped Classical in
/-- A function on `M` read in the chart at `x₀`: `f ∘ φ⁻¹` on the chart target, `0` outside. -/
def chartFun (x₀ : M) (f : M → ℝ) (x : Fin m → ℝ) : ℝ :=
  if x ∈ (extChartAt 𝓘(ℝ, Fin m → ℝ) x₀).target then f ((extChartAt 𝓘(ℝ, Fin m → ℝ) x₀).symm x) else 0

omit [IsManifold 𝓘(ℝ, Fin m → ℝ) ∞ M] in
/-- `chartFun` vanishes off the chart image of the support. -/
theorem chartFun_eq_zero (x₀ : M) {f : M → ℝ} {x : Fin m → ℝ}
    (hx : x ∉ extChartAt 𝓘(ℝ, Fin m → ℝ) x₀ '' tsupport f) : chartFun x₀ f x = 0 := by
  classical
  unfold chartFun
  split_ifs with ht
  · by_contra hne
    exact hx ⟨_, subset_tsupport _ hne, (extChartAt 𝓘(ℝ, Fin m → ℝ) x₀).right_inv ht⟩
  · rfl

omit [IsManifold 𝓘(ℝ, Fin m → ℝ) ∞ M] in
/-- `chartFun` of a continuous function with compact support inside the chart domain is continuous. -/
theorem continuous_chartFun (x₀ : M) {f : M → ℝ} (hf : Continuous f) (hc : IsCompact (tsupport f))
    (hs : tsupport f ⊆ (extChartAt 𝓘(ℝ, Fin m → ℝ) x₀).source) : Continuous (chartFun (m := m) x₀ f) := by
  classical
  have hC : IsCompact (extChartAt 𝓘(ℝ, Fin m → ℝ) x₀ '' tsupport f) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hs)
  have hzero : ∀ x, x ∉ extChartAt 𝓘(ℝ, Fin m → ℝ) x₀ '' tsupport f → chartFun (m := m) x₀ f x = 0 := by
    intro x hx
    unfold chartFun
    split_ifs with ht
    · by_contra hne
      exact hx ⟨_, subset_tsupport _ hne, (extChartAt 𝓘(ℝ, Fin m → ℝ) x₀).right_inv ht⟩
    · rfl
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x ∈ extChartAt 𝓘(ℝ, Fin m → ℝ) x₀ '' tsupport f
  · have ht : x ∈ (extChartAt 𝓘(ℝ, Fin m → ℝ) x₀).target := by
      obtain ⟨p, hp, rfl⟩ := hx
      exact (extChartAt 𝓘(ℝ, Fin m → ℝ) x₀).map_source (hs hp)
    have heq : (fun z => f ((extChartAt 𝓘(ℝ, Fin m → ℝ) x₀).symm z)) =ᶠ[𝓝 x] chartFun (m := m) x₀ f := by
      filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin m → ℝ)) x₀).mem_nhds ht] with z hz
      simp only [chartFun, hz, ite_true]
    exact (hf.continuousAt.comp (continuousAt_extChartAt_symm'' ht)).congr heq
  · have heq : (fun _ => (0 : ℝ)) =ᶠ[𝓝 x] chartFun (m := m) x₀ f := by
      filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hx] with z hz
      exact (hzero z hz).symm
    exact continuousAt_const.congr heq

/-- **A smooth cut-off**: a smooth function with compact support equal to `1` on a compact set. -/
theorem exists_cutoff [T2Space M] [SecondCountableTopology M] {K : Set M} (hK : IsCompact K) :
    ∃ χ : M → ℝ, ContMDiff 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, ℝ) ∞ χ ∧ IsCompact (tsupport χ) ∧ ∀ p ∈ K, χ p = 1 := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Fin m → ℝ) M
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  obtain ⟨f, h1, h0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, Fin m → ℝ) (n := ⊤)
    hK.isClosed hKL
  refine ⟨f, f.contMDiff, hL.of_isClosed_subset (isClosed_tsupport _) ?_, fun p hp => h1.self_of_nhdsSet p hp⟩
  exact closure_minimal (fun x hx => by_contra fun hxL => hx (h0 x hxL)) hL.isClosed

variable [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin m → ℝ) 2 M] [MeasurableSpace M]
  [BorelSpace M]

/-- **Integrability on a compact set** of a function continuous on every chart domain. -/
theorem NondegMetric.integrableOn_of_isCompact (g : NondegMetric 𝓘(ℝ, Fin m → ℝ) M) {K : Set M}
    (hK : IsCompact K) {f : M → ℝ} (hf : ∀ x₀ : M, ContinuousOn f (extChartAt 𝓘(ℝ, Fin m → ℝ) x₀).source) :
    IntegrableOn f K (NondegMetric.volumeMeasure g) := by
  have hrex : ∀ p : M, ∃ r > 0, ball (extChartAt 𝓘(ℝ, Fin m → ℝ) p p) r ⊆
      (extChartAt 𝓘(ℝ, Fin m → ℝ) p).target := fun p =>
    Metric.isOpen_iff.1 (isOpen_extChartAt_target p) _ (mem_extChartAt_target p)
  choose r hr0 hrball using hrex
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover (fun p => coverU m p (r p))
    (fun p _ => coverU_mem_nhds (n := m) p (hr0 p))
  refine IntegrableOn.mono_set ?_ (htK.trans (iUnion₂_mono fun p _ => coverU_subset_coverC (n := m) p))
  refine (integrableOn_finset_iUnion).2 fun p _ => ?_
  exact g.integrableOn_of_continuousOn p (isCompact_coverC (n := m) p (hr0 p) (hrball p))
    (coverC_subset_source (n := m) p (hr0 p) (hrball p))
    ((hf p).mono (coverC_subset_source (n := m) p (hr0 p) (hrball p))) subset_rfl

end Helpers

section Flux

set_option synthInstance.maxHeartbeats 400000

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin m → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin m → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin m → ℝ) 2 M]
  (g : NondegMetric 𝓘(ℝ, Fin m → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin m → ℝ) M)

/-- **The flux density of `w V(h)` in a chart**: `√|G| (w V)ʲ = (w ∘ φ⁻¹) √|G| Wʲ`, the Palatini flux weighted by `w`. -/
theorem divField_smul_palatiniField (x₀ : M) (w : M → ℝ) (j : Fin m) (x : Fin m → ℝ) :
    divField g x₀ (fun p => w p • palatiniField g h p) j x =
      chartFun x₀ w x * ehFlux (g.coordMetric x₀) (h.coordComp x₀) j x := by
  classical
  unfold divField chartFun
  split_ifs with ht
  · have hz := (extChartAt 𝓘(ℝ, Fin m → ℝ) x₀).map_target ht
    have hzb := mem_baseSet_of_mem_source x₀ hz
    have hL : ∀ v : TangentSpace 𝓘(ℝ, Fin m → ℝ) ((extChartAt 𝓘(ℝ, Fin m → ℝ) x₀).symm x),
        hv x₀ _ v = (tTriv (E := Fin m → ℝ) x₀).continuousLinearMapAt ℝ _ v :=
      fun v => ((tTriv (E := Fin m → ℝ) x₀).continuousLinearMapAt_apply_of_mem ℝ hzb v).symm
    have hc : chartComp x₀ (fun p => w p • palatiniField g h p) x =
        w ((extChartAt 𝓘(ℝ, Fin m → ℝ) x₀).symm x) • pvec g h x₀ x := by
      show hv x₀ _ (w _ • palatiniField g h _) = _
      rw [hL, map_smul, ← hL, hv_palatiniField g h hz, (extChartAt 𝓘(ℝ, Fin m → ℝ) x₀).right_inv ht]
    rw [hc, Pi.smul_apply, smul_eq_mul, ehFlux]
    show _ = _ * (√|(g.coordMetric x₀ x).det| * pvec g h x₀ x j)
    ring
  · simp

end Flux

section Boundary

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) 2 M]
  (g : NondegMetric 𝓘(ℝ, Fin (n + 1) → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin (n + 1) → ℝ) M)

omit [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) 2 M] in
/-- A graph point in the chart target, in an open set where the chart image of `D` is the graph region, comes from a
frontier point of `D`. -/
theorem symm_graphPt_mem_frontier (x₀ : M) {D : Set M} {σ : SignType} (hσ : σ ≠ 0) {γ : (Fin n → ℝ) → ℝ}
    {i : Fin (n + 1)} {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U)
    (hUD : ∀ x ∈ U, (x ∈ extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀ '' (D ∩ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).source) ↔
      x ∈ graphRegion σ γ i))
    {y : Fin n → ℝ} (hyU : graphPt γ i y ∈ U) (hyt : graphPt γ i y ∈ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).target) :
    (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm (graphPt γ i y) ∈ frontier D := by
  have h1 := graphPt_mem_frontier σ hσ γ i y
  rw [← mem_frontier_congr (Filter.eventually_of_mem (hU.mem_nhds hyU) hUD)] at h1
  exact symm_mem_frontier_of_mem_frontier_image x₀ hyt h1

/-- **The boundary at a graph point**: if near the graph point the chart image of `D` is the graph region, `h`
vanishes on `∂D` and `∂D` is nowhere null (a defining function with `du(♯du) ≠ 0`), then the components of `h`
vanish on the graph near `y` and the graph is not null at `y`. -/
theorem graph_boundary_facts (x₀ : M) {D : Set M}
    (hreg : ∀ p ∈ closure D, ∃ u : M → ℝ, ContMDiffAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) 2 u p ∧
      (u p = 0 → mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) u p ≠ 0 ∧
        mvfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) u p (sharp g p (mvfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) u p)) ≠ 0) ∧
      ∀ᶠ q in 𝓝 p, (q ∈ D ↔ 0 ≤ u q))
    (hbd : ∀ p ∈ frontier D, h.h p = 0)
    {σ : SignType} (hσ : σ ≠ 0) {γ : (Fin n → ℝ) → ℝ} (hγ : ContDiff ℝ 2 γ) {i : Fin (n + 1)}
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U)
    (hUD : ∀ x ∈ U, (x ∈ extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀ '' (D ∩ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).source) ↔
      x ∈ graphRegion σ γ i))
    {y : Fin n → ℝ} (hyU : graphPt γ i y ∈ U) (hyt : graphPt γ i y ∈ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).target) :
    (∀ᶠ y' in 𝓝 y, h.coordComp x₀ (graphPt γ i y') = 0) ∧
      (∑ a, graphConormal γ i y a *
        ∑ b, (g.coordMetric x₀ (graphPt γ i y))⁻¹ a b * graphConormal γ i y b) ≠ 0 := by
  have hgc : Continuous (graphPt γ i) := continuous_graphPt γ hγ.continuous i
  have hnear : ∀ᶠ y' in 𝓝 y, graphPt γ i y' ∈ U ∩ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).target :=
    hgc.continuousAt.preimage_mem_nhds ((hU.inter (isOpen_extChartAt_target x₀)).mem_nhds ⟨hyU, hyt⟩)
  have hfr : ∀ᶠ y' in 𝓝 y, (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm (graphPt γ i y') ∈ frontier D :=
    hnear.mono fun y' hy' => symm_graphPt_mem_frontier x₀ hσ hU hUD hy'.1 hy'.2
  refine ⟨hfr.mono fun y' hy' => ?_, ?_⟩
  · funext a b
    unfold SymBilinField.coordComp
    rw [hbd _ hy']
    rfl
  · have hp : (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm (graphPt γ i y) ∈ frontier D := hfr.self_of_nhds
    obtain ⟨u, hu, hdu, hDu⟩ := hreg _ (frontier_subset_closure hp)
    have hu0 := eq_zero_of_mem_frontier hDu hu.continuousAt hp
    obtain ⟨-, hnn⟩ := hdu hu0
    have hps := (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).map_target hyt
    have hpy := (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).right_inv hyt
    have hun := (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).1 hu
    have hcs : ContinuousAt (fun y' => (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm (graphPt γ i y')) y :=
      (continuousAt_extChartAt_symm'' hyt).comp hgc.continuousAt
    have hz : ∀ᶠ y' in 𝓝 y, (u ∘ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm) (graphPt γ i y') = 0 := by
      filter_upwards [hfr, hcs.eventually (hun.and hDu.eventually_nhds)] with y' h1 h2
      show u ((extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm (graphPt γ i y')) = 0
      exact eq_zero_of_mem_frontier h2.2 h2.1.continuousAt h1
    have hmd : MDifferentiableAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) u
        ((extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm (graphPt γ i y)) := hu.mdifferentiableAt (by norm_num)
    have hdiff : DifferentiableAt ℝ (u ∘ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm) (graphPt γ i y) := by
      have h2 : MDifferentiableAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, Fin (n + 1) → ℝ)
          (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm (graphPt γ i y) := by
        have := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, Fin (n + 1) → ℝ)) (x := x₀) hyt
        simpa [mdifferentiableWithinAt_univ] using this
      exact mdifferentiableAt_iff_differentiableAt.1 (hmd.comp _ h2)
    have hval := mvfderiv_sharp_chart g x₀ hps hmd
    rw [hpy] at hval
    refine conormal_nonnull_of_defining _ γ (hγ.of_le (by norm_num)) i y _ hdiff hz ?_
    rw [← hval]
    exact hnn

end Boundary

section Weighted

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) 2 M]
  (g : NondegMetric 𝓘(ℝ, Fin (n + 1) → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin (n + 1) → ℝ) M)

/-- **The Gibbons–Hawking–York density in a graph chart is affine in `t`** at a graph point where the chart image of
`D` is the graph region nearby, with slope minus the Palatini flux. -/
theorem ghyGraph_chart_affine (x₀ : M) {D : Set M}
    (hreg : ∀ p ∈ closure D, ∃ u : M → ℝ, ContMDiffAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) 2 u p ∧
      (u p = 0 → mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) u p ≠ 0 ∧
        mvfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) u p (sharp g p (mvfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) u p)) ≠ 0) ∧
      ∀ᶠ q in 𝓝 p, (q ∈ D ↔ 0 ≤ u q))
    (hbd : ∀ p ∈ frontier D, h.h p = 0)
    {σ : SignType} (hσ : σ ≠ 0) {γ : (Fin n → ℝ) → ℝ} (hγ : ContDiff ℝ 2 γ) {i : Fin (n + 1)}
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U)
    (hUD : ∀ x ∈ U, (x ∈ extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀ '' (D ∩ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).source) ↔
      x ∈ graphRegion σ γ i))
    {y : Fin n → ℝ} (hyU : graphPt γ i y ∈ U) (hyt : graphPt γ i y ∈ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).target)
    (t : ℝ) :
    ghyGraph (fun z => g.coordMetric x₀ z + t • h.coordComp x₀ z) γ i y =
      ghyGraph (g.coordMetric x₀) γ i y + t * (-∑ ρ, ehFlux (g.coordMetric x₀) (h.coordComp x₀) ρ (graphPt γ i y) *
        graphConormal γ i y ρ) := by
  obtain ⟨hz, hN⟩ := graph_boundary_facts g h x₀ hreg hbd hσ hγ hU hUD hyU hyt
  have hgc := g.isCoordMetric_coordMetric x₀
  have hGs : ∀ z a b, g.coordMetric x₀ z a b = g.coordMetric x₀ z b a := fun z a b => by
    have := congrFun (congrFun (g.coordMetric_transpose x₀ z) b) a
    simpa [Matrix.transpose_apply] using this
  exact ghyGraph_add_smul_loc (isOpen_extChartAt_target x₀) hgc.smooth (h.coordComp_smooth x₀) hGs
    (fun z a b => h.coordComp_symm x₀ z a b) (fun z hz => (hgc.isUnit_det z hz).ne_zero) γ (hγ.of_le (by norm_num))
    i y hyt hz hN t

omit [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) 2 M] in
/-- The Gibbons–Hawking–York density of the chart metric is continuous at a graph point in the chart target where the
graph is not null. -/
theorem continuousAt_ghyGraph_chart (x₀ : M) {γ : (Fin n → ℝ) → ℝ} (hγ : ContDiff ℝ 2 γ) {i : Fin (n + 1)}
    {y : Fin n → ℝ} (hyt : graphPt γ i y ∈ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).target)
    (hN : (∑ a, graphConormal γ i y a *
      ∑ b, (g.coordMetric x₀ (graphPt γ i y))⁻¹ a b * graphConormal γ i y b) ≠ 0) :
    ContinuousAt (fun y => ghyGraph (g.coordMetric x₀) γ i y) y := by
  have hgc := g.isCoordMetric_coordMetric x₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_extChartAt_target (I := 𝓘(ℝ, Fin (n + 1) → ℝ)) x₀) _ hyt
  let φb : ContDiffBump (graphPt γ i y) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hballφ : ball (graphPt γ i y) φb.rOut ⊆ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).target := hball
  have hG' : ∀ a b, ContDiff ℝ ∞ (fun z => g.coordMetric x₀ (ballRetract φb z) a b) :=
    contDiff_comp_ballRetract φb fun a b => (hgc.smooth a b).mono hballφ
  have hdet' : ∀ z, (g.coordMetric x₀ (ballRetract φb z)).det ≠ 0 := fun z =>
    (hgc.isUnit_det _ (hballφ (ballRetract_mem φb z))).ne_zero
  have hxin : graphPt γ i y ∈ ball (graphPt γ i y) φb.rIn := mem_ball_self (half_pos hr)
  have hN' : (∑ a, graphConormal γ i y a *
      ∑ b, (g.coordMetric x₀ (ballRetract φb (graphPt γ i y)))⁻¹ a b * graphConormal γ i y b) ≠ 0 := by
    rwa [ballRetract_of_mem φb hxin]
  have hc := continuousAt_ghyGraph (fun z => g.coordMetric x₀ (ballRetract φb z)) hG' hdet' γ hγ i y hN'
  refine hc.congr ?_
  have hcont : ContinuousAt (graphPt γ i) y := (continuous_graphPt γ hγ.continuous i).continuousAt
  filter_upwards [hcont.preimage_mem_nhds (isOpen_ball.mem_nhds hxin)] with y' hy'
  exact ghyGraph_congr γ i y' (eventuallyEq_comp_ballRetract φb (g.coordMetric x₀) hy')

/-- **The weighted Gibbons–Hawking–York density of a graph chart is continuous**, for weights supported where the
chart image of `D` is the graph region and inside the chart. -/
theorem continuous_ghy_weighted (x₀ : M) {D : Set M}
    (hreg : ∀ p ∈ closure D, ∃ u : M → ℝ, ContMDiffAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) 2 u p ∧
      (u p = 0 → mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) u p ≠ 0 ∧
        mvfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) u p (sharp g p (mvfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) u p)) ≠ 0) ∧
      ∀ᶠ q in 𝓝 p, (q ∈ D ↔ 0 ≤ u q))
    (hbd : ∀ p ∈ frontier D, h.h p = 0)
    {σ : SignType} (hσ : σ ≠ 0) {γ : (Fin n → ℝ) → ℝ} (hγ : ContDiff ℝ 2 γ) {i : Fin (n + 1)}
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U)
    (hUD : ∀ x ∈ U, (x ∈ extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀ '' (D ∩ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).source) ↔
      x ∈ graphRegion σ γ i))
    {ρ : (Fin (n + 1) → ℝ) → ℝ} (hρ : Continuous ρ) (hρU : tsupport ρ ⊆ U)
    {w : M → ℝ} (hw : Continuous w) (hwc : IsCompact (tsupport w))
    (hws : tsupport w ⊆ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).source) :
    Continuous (fun y => ρ (graphPt γ i y) * chartFun x₀ w (graphPt γ i y) * ghyGraph (g.coordMetric x₀) γ i y) := by
  have hC : IsCompact (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀ '' tsupport w) :=
    hwc.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hws)
  have hgpc := continuous_graphPt γ hγ.continuous i
  have hwt : Continuous (fun y => ρ (graphPt γ i y) * chartFun x₀ w (graphPt γ i y)) :=
    (hρ.comp hgpc).mul ((continuous_chartFun x₀ hw hwc hws).comp hgpc)
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hZ : graphPt γ i y ∈ tsupport ρ ∩ extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀ '' tsupport w
  · have hyt : graphPt γ i y ∈ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).target := by
      obtain ⟨p, hp, hpe⟩ := hZ.2
      rw [← hpe]
      exact (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).map_source (hws hp)
    obtain ⟨-, hN⟩ := graph_boundary_facts g h x₀ hreg hbd hσ hγ hU hUD (hρU hZ.1) hyt
    exact hwt.continuousAt.mul (continuousAt_ghyGraph_chart g x₀ hγ hyt hN)
  · have hZc : IsClosed (tsupport ρ ∩ extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀ '' tsupport w) :=
      (isClosed_tsupport _).inter hC.isClosed
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [hgpc.continuousAt.preimage_mem_nhds (hZc.isOpen_compl.mem_nhds hZ)] with y' hy'
    have h0 : ρ (graphPt γ i y') * chartFun x₀ w (graphPt γ i y') = 0 := by
      by_cases h1 : graphPt γ i y' ∈ tsupport ρ
      · rw [chartFun_eq_zero x₀ fun h2 => hy' ⟨h1, h2⟩, mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
    rw [h0, zero_mul]

omit [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) 2 M] in
/-- **The weighted Palatini flux through a graph chart is continuous.** -/
theorem continuous_flux_weighted (x₀ : M) {γ : (Fin n → ℝ) → ℝ} (hγ : ContDiff ℝ 1 γ) {i : Fin (n + 1)}
    {ρ : (Fin (n + 1) → ℝ) → ℝ} (hρ : Continuous ρ) {w : M → ℝ} (hw : Continuous w) (hwc : IsCompact (tsupport w))
    (hws : tsupport w ⊆ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).source) :
    Continuous (fun y => ρ (graphPt γ i y) * chartFun x₀ w (graphPt γ i y) *
      (-∑ ρ', ehFlux (g.coordMetric x₀) (h.coordComp x₀) ρ' (graphPt γ i y) * graphConormal γ i y ρ')) := by
  have hC : IsCompact (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀ '' tsupport w) :=
    hwc.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hws)
  have hgpc := continuous_graphPt γ hγ.continuous i
  have hgc := g.isCoordMetric_coordMetric x₀
  have hwt : Continuous (fun y => ρ (graphPt γ i y) * chartFun x₀ w (graphPt γ i y)) :=
    (hρ.comp hgpc).mul ((continuous_chartFun x₀ hw hwc hws).comp hgpc)
  have hGc : ContinuousOn (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).target :=
    continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => (hgc.smooth a b).continuousOn
  have hF : ∀ ρ', ContinuousOn (ehFlux (g.coordMetric x₀) (h.coordComp x₀) ρ')
      (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).target := fun ρ' =>
    ((Real.continuous_sqrt.comp continuous_abs).comp_continuousOn
      ((continuous_id.matrix_det).comp_continuousOn hGc)).mul
      ((contDiffOn_pi.1 (contDiffOn_pvec g h x₀) ρ').continuousOn)
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hZ : graphPt γ i y ∈ extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀ '' tsupport w
  · have hyt : graphPt γ i y ∈ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).target := by
      obtain ⟨p, hp, hpe⟩ := hZ
      rw [← hpe]
      exact (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).map_source (hws hp)
    refine hwt.continuousAt.mul (ContinuousAt.neg (tendsto_finsetSum Finset.univ fun ρ' _ => ?_))
    exact (((hF ρ').continuousAt ((isOpen_extChartAt_target x₀).mem_nhds hyt)).comp hgpc.continuousAt).mul
      ((continuous_apply ρ').comp (continuous_graphConormal γ hγ i)).continuousAt
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [hgpc.continuousAt.preimage_mem_nhds (hC.isClosed.isOpen_compl.mem_nhds hZ)] with y' hy'
    rw [chartFun_eq_zero x₀ hy', mul_zero, zero_mul]

omit [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) 2 M] in
/-- Integrands weighted by `chartFun w` along a graph have compact support. -/
theorem hasCompactSupport_weighted (x₀ : M) (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (ρ : (Fin (n + 1) → ℝ) → ℝ)
    {w : M → ℝ} (hwc : IsCompact (tsupport w)) (hws : tsupport w ⊆ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).source)
    (F : (Fin n → ℝ) → ℝ) :
    HasCompactSupport (fun y => ρ (graphPt γ i y) * chartFun x₀ w (graphPt γ i y) * F y) := by
  have hC : IsCompact (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀ '' tsupport w) :=
    hwc.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hws)
  refine HasCompactSupport.intro (hC.image (removeNthL i).continuous) fun y hy => ?_
  have hgp : graphPt γ i y ∉ extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀ '' tsupport w := fun hgp =>
    hy ⟨graphPt γ i y, hgp, by simp [removeNthL_apply, graphPt]⟩
  rw [chartFun_eq_zero x₀ hgp, mul_zero, zero_mul]

end Weighted

section Main

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  (g : NondegMetric 𝓘(ℝ, Fin (n + 1) → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin (n + 1) → ℝ) M)

/-- **The Gibbons–Hawking–York cancellation on a manifold.** Let `D` be a measurable region of a manifold with a metric
`g`, given near every point of its closure by a `C²` defining function `u` (`D = {u ≥ 0}`) with `du ≠ 0` and
`du(♯du) ≠ 0` where `u = 0` (the boundary is nowhere null), and let `h` be a symmetric tensor field vanishing outside a
compact set `K` and on the boundary of `D`. Then there is an atlas of graph charts of the boundary (charts at `c a` with
weights `w a`, and in each chart graph charts with cut-offs `ρ a b`) such that the Einstein–Hilbert action of `D ∩ K`
minus the Gibbons–Hawking–York term `Σ σ_ab ∫ ρ_ab w_a 2 √|h| K dy` in these charts has the derivative
`-∫_{D ∩ K} ⟨G + Λ g, h⟩_g d vol_g` at `t = 0`: the boundary terms of the variation cancel. -/
theorem eh_ghy_variation_manifold {K : Set M} (hK : IsCompact K) (hsupp : ∀ p, p ∉ K → h.h p = 0)
    {D : Set M} (hD : MeasurableSet D)
    (hreg : ∀ p ∈ closure D, ∃ u : M → ℝ, ContMDiffAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) 2 u p ∧
      (u p = 0 → mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) u p ≠ 0 ∧
        mvfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) u p (sharp g p (mvfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) u p)) ≠ 0) ∧
      ∀ᶠ q in 𝓝 p, (q ∈ D ↔ 0 ≤ u q))
    (hbd : ∀ p ∈ frontier D, h.h p = 0) (Λ : ℝ) :
    ∃ (ι : Type u) (_ : Fintype ι) (c : ι → M) (w : ι → M → ℝ) (κ : ι → Type) (_ : ∀ a, Fintype (κ a))
      (ρ : ∀ a, κ a → (Fin (n + 1) → ℝ) → ℝ) (σ : ∀ a, κ a → SignType) (γ : ∀ a, κ a → (Fin n → ℝ) → ℝ)
      (i : ∀ a, κ a → Fin (n + 1)),
      (∀ a, ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) ∞ (w a)) ∧ (∀ a, IsCompact (tsupport (w a))) ∧
      (∀ a, tsupport (w a) ⊆ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) (c a)).source) ∧ (∀ p ∈ K, ∑ a, w a p = 1) ∧
      (∀ a b, ContDiff ℝ ∞ (ρ a b)) ∧ (∀ a b, ContDiff ℝ 2 (γ a b)) ∧
      (∀ a b y, y ∈ tsupport (ρ a b) →
        (y ∈ extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) (c a) '' (D ∩ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) (c a)).source) ↔
          y ∈ graphRegion (σ a b) (γ a b) (i a b))) ∧
      HasDerivAt (fun t : ℝ => ehAction (g.perturb h t) Λ (D ∩ K) -
          ∑ a, ∑ b, (σ a b : ℝ) * ∫ y, ρ a b (graphPt (γ a b) (i a b) y) *
            chartFun (c a) (w a) (graphPt (γ a b) (i a b) y) *
            ghyGraph (fun z => g.coordMetric (c a) z + t • h.coordComp (c a) z) (γ a b) (i a b) y)
        (-∫ p in D ∩ K, ehIntegrand g h Λ p ∂(NondegMetric.volumeMeasure g)) 0 := by
  classical
  have hLC : (leviCivita g).IsLeviCivita g := ⟨leviCivita_torsion g, leviCivita_compat g⟩
  have hV := contMDiff_palatiniField g h
  have hVK : ∀ p ∉ K, palatiniField g h p = 0 := fun p hp => palatiniField_eq_zero_of_notMem g h hK hsupp hp
  have hreg0 : ∀ p ∈ closure D, ∃ u : M → ℝ, ContMDiffAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) 2 u p ∧
      (u p = 0 → mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) u p ≠ 0) ∧ ∀ᶠ q in 𝓝 p, (q ∈ D ↔ 0 ≤ u q) :=
    fun p hp => by
      obtain ⟨u, hu, hdu, hDu⟩ := hreg p hp
      exact ⟨u, hu, fun h0 => (hdu h0).1, hDu⟩
  obtain ⟨ι, hι, c, ψ, κ, hκ, ρ, σ, γ, i, U, hψ, hψs, hψ1, hρ, hγ, hUo, hsU, hUD, hflux⟩ :=
    divergence_theorem_manifold_open g hV hK hVK hD hreg0
  obtain ⟨χ, hχ, hχc, hχ1⟩ := exists_cutoff (m := n + 1) hK
  obtain ⟨w, hwdef⟩ : ∃ w : ι → M → ℝ, w = fun a p => χ p * ψ a p := ⟨_, rfl⟩
  have hw : ∀ a, ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) ∞ (w a) := fun a => by
    rw [hwdef]; exact hχ.mul (hψ a)
  have hwsub : ∀ a, tsupport (w a) ⊆ tsupport χ ∩ tsupport (ψ a) := fun a => by
    rw [hwdef]
    exact subset_inter (tsupport_mul_subset_left (f := χ) (g := ψ a))
      (tsupport_mul_subset_right (f := χ) (g := ψ a))
  have hwc : ∀ a, IsCompact (tsupport (w a)) := fun a =>
    hχc.of_isClosed_subset (isClosed_tsupport _) ((hwsub a).trans inter_subset_left)
  have hws : ∀ a, tsupport (w a) ⊆ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) (c a)).source := fun a =>
    (hwsub a).trans (inter_subset_right.trans (hψs a))
  have hw1 : ∀ p ∈ K, ∑ a, w a p = 1 := fun p hp => by
    rw [hwdef]
    simp only
    rw [← Finset.mul_sum, hψ1 p hp, hχ1 p hp, mul_one]
  have hwV : ∀ a, (fun p => ψ a p • palatiniField g h p) = fun p => w a p • palatiniField g h p := fun a => by
    funext p
    by_cases hp : p ∈ K
    · rw [hwdef]; simp only; rw [hχ1 p hp, one_mul]
    · rw [hVK p hp, smul_zero, smul_zero]
  refine ⟨ι, hι, c, w, κ, hκ, ρ, σ, γ, i, hw, hwc, hws, hw1, hρ, hγ,
    fun a b y hy => hUD a b y (hsU a b hy), ?_⟩
  -- the bulk variation, split into the Einstein term and the divergence of `V(h)`
  have hcE : ∀ x₀ : M, ContinuousOn (ehIntegrand g h Λ) (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).source :=
    continuousOn_ehIntegrand g h Λ
  have hcV : ∀ x₀ : M, ContinuousOn (expansionM (leviCivita g) (palatiniField g h))
      (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).source := continuousOn_expansionM (leviCivita g) g hLC hV
  have hiE := (g.integrableOn_of_isCompact hK hcE).mono_set (inter_subset_right : D ∩ K ⊆ K)
  have hiV := (g.integrableOn_of_isCompact hK hcV).mono_set (inter_subset_right : D ∩ K ⊆ K)
  have hbulk := eh_variation_region_manifold g h hK hsupp hD Λ
  have hsplit : ∫ p in D ∩ K, (-ehIntegrand g h Λ p + expansionM (leviCivita g) (palatiniField g h) p)
      ∂(NondegMetric.volumeMeasure g) = -(∫ p in D ∩ K, ehIntegrand g h Λ p ∂(NondegMetric.volumeMeasure g)) +
        ∫ p in D ∩ K, expansionM (leviCivita g) (palatiniField g h) p ∂(NondegMetric.volumeMeasure g) := by
    have e := integral_add hiE.neg hiV
    simp only [Pi.neg_apply, integral_neg] at e
    exact e
  have hDK : ∫ p in D ∩ K, expansionM (leviCivita g) (palatiniField g h) p ∂(NondegMetric.volumeMeasure g) =
      ∫ p in D, expansionM (leviCivita g) (palatiniField g h) p ∂(NondegMetric.volumeMeasure g) := by
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hD inter_subset_left fun p hp => ?_).symm
    have hpK : p ∉ K := fun hpK => hp.2 ⟨hp.1, hpK⟩
    exact expansionM_eq_zero_of_eventually (leviCivita g) g hLC hV
      (Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hpK) fun q hq => hVK q hq)
  -- the chart integrands of the Gibbons–Hawking–York term are affine in `t`
  obtain ⟨A, hA⟩ : ∃ A : ∀ a, κ a → (Fin n → ℝ) → ℝ, A = fun a b y =>
      ρ a b (graphPt (γ a b) (i a b) y) * chartFun (c a) (w a) (graphPt (γ a b) (i a b) y) *
        ghyGraph (g.coordMetric (c a)) (γ a b) (i a b) y := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ∀ a, κ a → (Fin n → ℝ) → ℝ, B = fun a b y =>
      ρ a b (graphPt (γ a b) (i a b) y) * chartFun (c a) (w a) (graphPt (γ a b) (i a b) y) *
        (-∑ ρ', ehFlux (g.coordMetric (c a)) (h.coordComp (c a)) ρ' (graphPt (γ a b) (i a b) y) *
          graphConormal (γ a b) (i a b) y ρ') := ⟨_, rfl⟩
  have hpt : ∀ a b, σ a b ≠ 0 → ∀ (t : ℝ) (y : Fin n → ℝ),
      ρ a b (graphPt (γ a b) (i a b) y) * chartFun (c a) (w a) (graphPt (γ a b) (i a b) y) *
        ghyGraph (fun z => g.coordMetric (c a) z + t • h.coordComp (c a) z) (γ a b) (i a b) y =
      A a b y + t * B a b y := by
    intro a b hσ t y
    simp only [hA, hB]
    by_cases hw0 : ρ a b (graphPt (γ a b) (i a b) y) * chartFun (c a) (w a) (graphPt (γ a b) (i a b) y) = 0
    · simp only [hw0, zero_mul, mul_zero, add_zero]
    · have hρ0 : ρ a b (graphPt (γ a b) (i a b) y) ≠ 0 := left_ne_zero_of_mul hw0
      have hc0 : chartFun (c a) (w a) (graphPt (γ a b) (i a b) y) ≠ 0 := right_ne_zero_of_mul hw0
      have hyU : graphPt (γ a b) (i a b) y ∈ U a b := hsU a b (subset_tsupport _ hρ0)
      have hyt : graphPt (γ a b) (i a b) y ∈ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) (c a)).target := by
        by_contra ht
        exact hc0 (by unfold chartFun; exact ite_eq_right_iff.2 fun h' => absurd h' ht)
      rw [ghyGraph_chart_affine g h (c a) hreg hbd hσ (hγ a b) (hUo a b) (hUD a b) hyU hyt t]
      ring
  have hiA : ∀ a b, σ a b ≠ 0 → Integrable (A a b) := fun a b hσ => by
    rw [hA]
    exact (continuous_ghy_weighted g h (c a) hreg hbd hσ (hγ a b) (hUo a b) (hUD a b) (hρ a b).continuous
      (hsU a b) (hw a).continuous (hwc a) (hws a)).integrable_of_hasCompactSupport
      (hasCompactSupport_weighted (c a) (γ a b) (i a b) (ρ a b) (hwc a) (hws a) _)
  have hiB : ∀ a b, Integrable (B a b) := fun a b => by
    rw [hB]
    exact (continuous_flux_weighted g h (c a) ((hγ a b).of_le (by norm_num)) (hρ a b).continuous
      (hw a).continuous (hwc a) (hws a)).integrable_of_hasCompactSupport
      (hasCompactSupport_weighted (c a) (γ a b) (i a b) (ρ a b) (hwc a) (hws a) _)
  have hterm : ∀ a b (t : ℝ), (σ a b : ℝ) * ∫ y, ρ a b (graphPt (γ a b) (i a b) y) *
        chartFun (c a) (w a) (graphPt (γ a b) (i a b) y) *
        ghyGraph (fun z => g.coordMetric (c a) z + t • h.coordComp (c a) z) (γ a b) (i a b) y =
      (σ a b : ℝ) * (∫ y, A a b y) + t * ((σ a b : ℝ) * ∫ y, B a b y) := by
    intro a b t
    by_cases hσ : σ a b = 0
    · simp [hσ]
    · have e1 : ∫ y, ρ a b (graphPt (γ a b) (i a b) y) * chartFun (c a) (w a) (graphPt (γ a b) (i a b) y) *
            ghyGraph (fun z => g.coordMetric (c a) z + t • h.coordComp (c a) z) (γ a b) (i a b) y =
          ∫ y, (A a b y + t * B a b y) := integral_congr_ae (Filter.Eventually.of_forall fun y => hpt a b hσ t y)
      have e2 : ∫ y, (A a b y + t * B a b y) = (∫ y, A a b y) + t * ∫ y, B a b y := by
        rw [integral_add (hiA a b hσ) ((hiB a b).const_mul t), integral_const_mul]
      rw [e1, e2]
      ring
  -- the slope of the Gibbons–Hawking–York term is the integral of `div V(h)` over `D`
  have hS : ∑ a, ∑ b, (σ a b : ℝ) * (∫ y, B a b y) =
      ∫ p in D, expansionM (leviCivita g) (palatiniField g h) p ∂(NondegMetric.volumeMeasure g) := by
    rw [hflux, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [graphFlux_eq, hwV a]
    have hy : ∀ y, ∑ ρ', ρ a b (graphPt (γ a b) (i a b) y) *
        divField g (c a) (fun p => w a p • palatiniField g h p) ρ' (graphPt (γ a b) (i a b) y) *
          graphConormal (γ a b) (i a b) y ρ' = -B a b y := fun y => by
      simp only [hB, divField_smul_palatiniField g h, mul_neg, neg_neg, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ρ' _ => by ring
    simp only [hy, integral_neg]
    ring
  have hfun : (fun t : ℝ => ehAction (g.perturb h t) Λ (D ∩ K) -
      ∑ a, ∑ b, (σ a b : ℝ) * ∫ y, ρ a b (graphPt (γ a b) (i a b) y) *
        chartFun (c a) (w a) (graphPt (γ a b) (i a b) y) *
        ghyGraph (fun z => g.coordMetric (c a) z + t • h.coordComp (c a) z) (γ a b) (i a b) y) =
      fun t : ℝ => ehAction (g.perturb h t) Λ (D ∩ K) -
        ((∑ a, ∑ b, (σ a b : ℝ) * ∫ y, A a b y) + t * ∑ a, ∑ b, (σ a b : ℝ) * (∫ y, B a b y)) := by
    funext t
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => hterm a b t
  rw [hfun]
  have hlin := ((hasDerivAt_id (0 : ℝ)).mul_const (∑ a, ∑ b, (σ a b : ℝ) * ∫ y, B a b y)).const_add
    (∑ a, ∑ b, (σ a b : ℝ) * ∫ y, A a b y)
  refine (hbulk.sub hlin).congr_deriv ?_
  rw [hsplit, hDK, hS]
  ring

end Main

end Lightlike
