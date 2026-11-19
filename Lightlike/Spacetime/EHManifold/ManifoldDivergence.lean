import Lightlike.Spacetime.RaychaudhuriManifold
import Lightlike.Spacetime.VolumeMeasure
import Lightlike.Spacetime.VariationInverse
import Lightlike.Spacetime.SchwarzschildManifold
import Lightlike.Spacetime.EHManifold.ChartIntegrable
import Lightlike.Spacetime.EHManifold.LocalDivergence

/-!
# The divergence theorem on a manifold (GE15)

L. H. Loomis, S. Sternberg, *Advanced Calculus* (revised edition), chapter 10, section 6: Theorem 6.1, p. 421, for a domain
with regular boundary (Definition, p. 419), a density and a smooth vector field, `∫_D div⟨X, ρ⟩ = ∫_{∂D} ε_X ρ_X`, and its
form (6.6), p. 424, for the volume density of a metric. Here, for a metric `g` of any signature on a manifold modelled on
`ℝⁿ⁺¹` (second countable, Hausdorff), its Levi-Civita connection (`leviCivita g`), a smooth vector field `X` vanishing outside
a compact set and a measurable `D` given near every point of its closure by a defining function `u` (`D = {u ≥ 0}`, `u ∈ C²`,
`du ≠ 0` where `u = 0`):

* `divergence_theorem_manifold`: `∫_D div X d vol_g` equals the flux of `X` through the boundary of `D`, written with a
  smooth partition of unity `ψ_a` subordinate to charts and, in each chart, graph charts of the boundary
  (`graphFlux` of `√|g| ψ_a X`, `RegularDomainDivergence.lean`). The divergence is `tr(u ↦ ∇_u X)` (`expansionM`).

The proof: the partition of unity splits `X`; the divergence is additive (`expansionM_sum`); in a chart the integral of
`div Y` for the volume measure is `∫ ∂ⱼ(√|g| Yʲ) dy` (`integral_expansionM_chart`, from `sqrt_det_mul_expansion`:
`√|g| ∇ₐYᵃ = ∂ⱼ(√|g| Yʲ)`, and the chart formula of the volume measure); the chart image of `D` has the defining function
`u ∘ φ⁻¹` (`chart_defining_function`), and the divergence theorem in `ℝⁿ⁺¹` (`LocalDivergence.lean`) gives the flux
(`exists_chart_flux`).
-/

open MeasureTheory Set Filter Topology Manifold Matrix
open scoped ContDiff ENNReal

noncomputable section

namespace Lightlike

section Coord
variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)} {v : (Fin n → ℝ) → Fin n → ℝ}

/-- **The divergence in coordinates**: `√|g| ∇ₐ vᵃ = ∂ⱼ(√|g| vʲ)` for the Levi-Civita connection of a coordinate metric. -/
theorem sqrt_det_mul_expansion (hg : IsCoordMetric g U) (hv : ∀ a, ContDiffOn ℝ ∞ (fun y => v y a) U)
    {x : Fin n → ℝ} (hx : x ∈ U) :
    √|(g x).det| * expansion g v x = ∑ j, pd j (fun y => √|(g y).det| * v y j) x := by
  have hd : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) x := fun a b =>
    differentiableAt_of_contDiffOn (hg.smooth a b) hg.isOpen hx
  have hdet : (g x).det ≠ 0 := (hg.isUnit_det x hx).ne_zero
  have hsym : ∀ a b, g x a b = g x b a := fun a b => by
    conv_rhs => rw [← hg.symm x hx]
    rfl
  have hdetd : DifferentiableAt ℝ (fun y => (g y).det) x := differentiableAt_det_of hd
  have hsq : DifferentiableAt ℝ (fun y => √|(g y).det|) x := by
    have habs : DifferentiableAt ℝ (fun y => |(g y).det|) x := by
      rcases lt_or_gt_of_ne hdet with hneg | hpos
      · refine (hdetd.neg).congr_of_eventuallyEq ?_
        filter_upwards [hdetd.continuousAt.eventually (gt_mem_nhds hneg)] with y hy
        exact abs_of_neg hy
      · refine hdetd.congr_of_eventuallyEq ?_
        filter_upwards [hdetd.continuousAt.eventually (lt_mem_nhds hpos)] with y hy
        exact abs_of_pos hy
    exact habs.sqrt (abs_pos.2 hdet).ne'
  have hvd : ∀ j, DifferentiableAt ℝ (fun y => v y j) x := fun j =>
    differentiableAt_of_contDiffOn (hv j) hg.isOpen hx
  -- the symmetrised metric, equal to `g` on `U`
  set g' : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := fun y => (1 / 2 : ℝ) • (g y + (g y)ᵀ) with hg'
  have hgU : ∀ y ∈ U, g' y = g y := fun y hy => by
    simp only [hg', hg.symm y hy]; ext a b; simp; ring
  have hg's : ∀ y a b, g' y a b = g' y b a := fun y a b => by simp [hg', add_comm]
  have hd' : ∀ a b, DifferentiableAt ℝ (fun y => g' y a b) x := fun a b => by
    simp only [hg', Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
    exact ((hd a b).add (hd b a)).const_mul _
  have hdet' : (g' x).det ≠ 0 := by rw [hgU x hx]; exact hdet
  have hev : (fun y => √|(g y).det|) =ᶠ[𝓝 x] fun y => √|(g' y).det| := by
    filter_upwards [hg.isOpen.mem_nhds hx] with y hy
    rw [hgU y hy]
  have hpdsq : ∀ j, pd j (fun y => √|(g y).det|) x = √|(g x).det| * ∑ κ, christoffel g κ κ j x := fun j => by
    rw [pd_congr hev j, pd_sqrt_abs_det g' x hg's hd' hdet' j, hgU x hx]
    congr 1
    exact Finset.sum_congr rfl fun κ _ => christoffel_congr_on hg.isOpen hgU hx κ κ j
  have hterm : ∀ j, pd j (fun y => √|(g y).det| * v y j) x =
      √|(g x).det| * (∑ κ, christoffel g κ κ j x) * v x j + √|(g x).det| * pd j (fun y => v y j) x := fun j => by
    rw [pd_mul hsq (hvd j) j, hpdsq j]
  simp only [hterm, expansion, covD, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
  rw [add_comm]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Coord

section Extend
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function smooth on an open set and zero outside a closed subset of it is smooth. -/
theorem contDiff_of_contDiffOn_of_zero {f : E → ℝ} {U C : Set E} {k : ℕ∞ω} (hU : IsOpen U) (hC : IsClosed C)
    (hCU : C ⊆ U) (hf : ContDiffOn ℝ k f U) (h0 : ∀ y ∉ C, f y = 0) : ContDiff ℝ k f := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hy)
  · have hyC : y ∉ C := fun h => hy (hCU h)
    have hev : f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hC.isOpen_compl.mem_nhds hyC] with z hz
      exact h0 z hz
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The determinant of a matrix with smooth entries is smooth. -/
theorem contDiffOn_det_of {n : ℕ} {f : E → Matrix (Fin n) (Fin n) ℝ} {s : Set E} {k : ℕ∞ω}
    (hf : ∀ i j, ContDiffOn ℝ k (fun y => f y i j) s) : ContDiffOn ℝ k (fun y => (f y).det) s := by
  simp only [Matrix.det_apply]
  refine ContDiffOn.sum fun σ _ => ?_
  exact (contDiffOn_prod fun i _ => hf (σ i) i).const_smul _

end Extend

section ManifoldField
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]

open scoped Classical in
/-- The flux field of `Y` in the chart at `x₀`: `√|det g| Yʲ` on the chart target, `0` outside. -/
def divField (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) (Y : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p)
    (j : Fin n) (y : Fin n → ℝ) : ℝ :=
  if y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target then √|(g.coordMetric x₀ y).det| * chartComp x₀ Y y j else 0

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- The components vanish where the field does. -/
theorem chartComp_eq_zero {Y : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p} (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) (h0 : Y ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) = 0) :
    chartComp x₀ Y y = 0 := by
  have hb := symm_mem_chartTriv_baseSet x₀ hy
  show hv x₀ _ (Y _) = 0
  rw [h0]
  exact ((tTriv (E := Fin n → ℝ) x₀).linear ℝ hb).map_zero

/-- **The flux field is smooth** for a smooth field supported in a compact subset of the chart domain. -/
theorem contDiff_divField (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) {Y : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hY : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
    {S : Set M} (hS : IsCompact S) (hSs : S ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (hYS : ∀ p ∉ S, Y p = 0)
    (j : Fin n) : ContDiff ℝ ∞ (divField g x₀ Y j) := by
  classical
  have hC : IsCompact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' S) :=
    hS.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hSs)
  have hCt : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' S ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
    rintro _ ⟨p, hp, rfl⟩
    exact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (hSs hp)
  refine contDiff_of_contDiffOn_of_zero (isOpen_extChartAt_target x₀) hC.isClosed hCt ?_ ?_
  · have hdet : ∀ y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target, (g.coordMetric x₀ y).det ≠ 0 := fun y hy =>
      (g.coordMetric_isUnit_det x₀ hy).ne_zero
    have h1 : ContDiffOn ℝ ∞ (fun y => √|(g.coordMetric x₀ y).det| * chartComp x₀ Y y j)
        (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
      refine ContDiffOn.mul (ContDiffOn.sqrt ?_ fun y hy => abs_ne_zero.2 (hdet y hy)) (contDiffOn_chartComp hY x₀ j)
      intro y hy
      exact (contDiffAt_abs (hdet y hy)).comp_contDiffWithinAt y
        (contDiffOn_det_of (fun a b => g.coordMetric_smooth x₀ a b) y hy)
    exact h1.congr fun y hy => by rw [divField, ite_eq_left_iff]; exact fun h => absurd hy h
  · intro y hy
    rw [divField, ite_eq_right_iff]
    intro ht
    have hq : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∉ S := fun hq =>
      hy ⟨_, hq, (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv ht⟩
    rw [chartComp_eq_zero x₀ ht (hYS _ hq)]
    simp

end ManifoldField

section ChartPiece
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
variable (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : cov.IsLeviCivita g)
  {Y : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
  (hY : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
    (fun q : M => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
include h hY

/-- The divergence vanishes where the field vanishes near the point. -/
theorem expansionM_eq_zero_of_eventually {p : M} (h0 : ∀ᶠ q in 𝓝 p, Y q = 0) : expansionM cov Y p = 0 := by
  have hps : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).source := mem_extChartAt_source p
  rw [expansionM_eq cov g h hY p hps]
  have hy0 := (extChartAt 𝓘(ℝ, Fin n → ℝ) p).map_source hps
  have hev : ∀ a, (fun y => chartComp p Y y a) =ᶠ[𝓝 (extChartAt 𝓘(ℝ, Fin n → ℝ) p p)] fun _ => 0 := by
    intro a
    have hc : ContinuousAt (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) :=
      continuousAt_extChartAt_symm p
    rw [← ((extChartAt 𝓘(ℝ, Fin n → ℝ) p).left_inv hps)] at h0
    filter_upwards [hc.preimage_mem_nhds h0, (isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) p).mem_nhds hy0]
      with y hy hyt
    rw [chartComp_eq_zero p hyt hy]
    rfl
  have hv0 : ∀ c, chartComp p Y (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) c = 0 := fun c => (hev c).self_of_nhds
  unfold expansion covD
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [pd_congr (hev a), show pd a (fun _ : Fin n → ℝ => (0 : ℝ)) _ = 0 by simp [pd], zero_add]
  exact Finset.sum_eq_zero fun c _ => by rw [hv0 c, mul_zero]

end ChartPiece

section ChartIntegral
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
variable (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : cov.IsLeviCivita g)
  {Y : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
  (hY : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
    (fun q : M => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
include h hY

omit [SecondCountableTopology M] [T2Space M] [MeasurableSpace M] [BorelSpace M] in
/-- The divergence is continuous on a chart domain. -/
theorem continuousOn_expansionM (x₀ : M) :
    ContinuousOn (expansionM cov Y) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source := by
  have hexp : ContinuousOn (expansion (g.coordMetric x₀) (chartComp x₀ Y)) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    fun y hy => (DifferentiableAt.fun_sum fun a _ => differentiableAt_covD (g.isCoordMetric_coordMetric x₀)
      (contDiffOn_chartComp hY x₀) hy a a).continuousAt.continuousWithinAt
  refine (hexp.comp (continuousOn_extChartAt x₀) fun p hp => (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hp).congr ?_
  intro p hp
  exact expansionM_eq cov g h hY x₀ hp

/-- **The integral of the divergence of one chart piece**: for `Y` supported in a compact subset of the chart domain at
`x₀`, `∫_D div Y d vol_g = ∫_{φ(D)} ∂ⱼ(√|g| Yʲ) dy`. -/
theorem integral_expansionM_chart (x₀ : M) {S : Set M} (hS : IsCompact S)
    (hSs : S ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (hYS : ∀ p ∉ S, Y p = 0) {D : Set M} (hD : MeasurableSet D) :
    ∫ p in D, expansionM cov Y p ∂(NondegMetric.volumeMeasure g) =
      ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' (D ∩ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source),
        ∑ j, pd j (divField g x₀ Y j) y := by
  classical
  have hsrc : MeasurableSet (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source :=
    (isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) x₀).measurableSet
  have hK : MeasurableSet (D ∩ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) := hD.inter hsrc
  have h1 : ∫ p in D, expansionM cov Y p ∂(NondegMetric.volumeMeasure g) =
      ∫ p in D ∩ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source, expansionM cov Y p ∂(NondegMetric.volumeMeasure g) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hD inter_subset_left ?_
    intro p hp
    have hpS : p ∉ S := fun hpS => hp.2 ⟨hp.1, hSs hpS⟩
    refine expansionM_eq_zero_of_eventually cov g h hY ?_
    filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hpS] with q hq
    exact hYS q hq
  have hf : AEStronglyMeasurable (expansionM cov Y)
      ((NondegMetric.volumeMeasure g).restrict (D ∩ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)) :=
    ((continuousOn_expansionM cov g h hY x₀).mono inter_subset_right).aestronglyMeasurable hK
  rw [h1, NondegMetric.setIntegral_volumeMeasure_chart g x₀ hK inter_subset_right _ hf]
  refine setIntegral_congr_fun (measurableSet_image_extChartAt x₀ hK inter_subset_right) ?_
  rintro y ⟨p, hp, rfl⟩
  have hy : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hp.2
  show NondegMetric.volDensity g x₀ _ * expansionM cov Y ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm _) = _
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hp.2, expansionM_eq cov g h hY x₀ hp.2]
  show √|(g.coordMetric x₀ _).det| * _ = _
  rw [sqrt_det_mul_expansion (g.isCoordMetric_coordMetric x₀) (contDiffOn_chartComp hY x₀) hy]
  refine Finset.sum_congr rfl fun j _ => (pd_congr ?_ j).symm
  filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x₀).mem_nhds hy] with z hz
  rw [divField, ite_eq_left_iff]
  exact fun h' => absurd hz h'

end ChartIntegral

section ChartFlux
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

omit [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M] in
/-- A defining function of `D` at a point of the chart domain gives one of the chart image of `D`. -/
theorem chart_defining_function (x₀ : M) {D : Set M} {y : Fin (n + 1) → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).target) {u : M → ℝ}
    (hu : ContMDiffAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) 2 u ((extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm y))
    (hdu : u ((extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm y) = 0 →
      mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) u ((extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm y) ≠ 0)
    (hDu : ∀ᶠ q in 𝓝 ((extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm y), (q ∈ D ↔ 0 ≤ u q)) :
    ContDiffAt ℝ 2 (u ∘ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm) y ∧
      ((u ∘ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm) y = 0 →
        fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm) y ≠ 0) ∧
      ∀ᶠ z in 𝓝 y, (z ∈ extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀ '' (D ∩ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).source) ↔
        0 ≤ (u ∘ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).symm) z) := by
  set φ := extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀ with hφ
  have hs : ContMDiffAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, Fin (n + 1) → ℝ) ∞ φ.symm y :=
    (contMDiffOn_extChartAt_symm x₀).contMDiffAt ((isOpen_extChartAt_target x₀).mem_nhds hy)
  have hcomp : ContMDiffAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) 2 (u ∘ φ.symm) y := hu.comp y (hs.of_le (by simp))
  refine ⟨contMDiffAt_iff_contDiffAt.1 hcomp, ?_, ?_⟩
  · intro h0 hd
    apply hdu h0
    have hmd : MDifferentiableAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) u (φ.symm y) := hu.mdifferentiableAt (by simp)
    have hsd : MDifferentiableAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, Fin (n + 1) → ℝ) φ.symm y := hs.mdifferentiableAt (by simp)
    have hchain := mfderiv_comp y hmd hsd
    rw [mfderiv_eq_fderiv, hd, mfderiv_extChartAt_symm_eq x₀ hy] at hchain
    have hb := symm_mem_chartTriv_baseSet x₀ hy
    refine ContinuousLinearMap.ext fun w => ?_
    have e1 := DFunLike.congr_fun hchain (hv x₀ _ w)
    have e2 : (mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) u (φ.symm y))
        ((chartTriv (n + 1) x₀).symmL ℝ (φ.symm y) (hv x₀ _ w)) = 0 := e1.symm
    rw [symmL_hv x₀ hb w] at e2
    exact e2
  · have hc : ContinuousAt φ.symm y := continuousAt_extChartAt_symm'' hy
    filter_upwards [hc.preimage_mem_nhds hDu, (isOpen_extChartAt_target (I := 𝓘(ℝ, Fin (n + 1) → ℝ)) x₀).mem_nhds hy]
      with z hz hzt
    have hz' : (φ.symm z ∈ D ↔ 0 ≤ u (φ.symm z)) := hz
    rw [Function.comp_apply, ← hz']
    constructor
    · rintro ⟨q, ⟨hqD, hqs⟩, rfl⟩
      rwa [φ.left_inv hqs]
    · intro hq
      exact ⟨φ.symm z, ⟨hq, φ.map_target hzt⟩, φ.right_inv hzt⟩

/-- **The divergence theorem for one chart piece**: for `Y` supported in a compact subset of the chart domain at `x₀` and
a domain `D` with regular boundary (by defining functions), `∫_D div Y d vol_g` is the flux of `√|g| Y` through the
boundary of the chart image of `D`, written in graph charts with a partition of unity., with open sets `U b ⊇ tsupport (ρ b)` on which
the chart image of `D` is the graph region. -/
theorem exists_chart_flux_open (cov : Connection 𝓘(ℝ, Fin (n + 1) → ℝ) M) (g : NondegMetric 𝓘(ℝ, Fin (n + 1) → ℝ) M)
    (h : cov.IsLeviCivita g) {Y : Π p : M, TangentSpace 𝓘(ℝ, Fin (n + 1) → ℝ) p}
    (hY : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) (𝓘(ℝ, Fin (n + 1) → ℝ).prod 𝓘(ℝ, Fin (n + 1) → ℝ)) ∞
      (fun q : M => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, Fin (n + 1) → ℝ) M)))
    (x₀ : M) {S : Set M} (hS : IsCompact S) (hSs : S ⊆ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).source)
    (hYS : ∀ p ∉ S, Y p = 0) {D : Set M} (hD : MeasurableSet D)
    (hreg : ∀ p ∈ closure D, ∃ u : M → ℝ, ContMDiffAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) 2 u p ∧
      (u p = 0 → mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) u p ≠ 0) ∧ ∀ᶠ q in 𝓝 p, (q ∈ D ↔ 0 ≤ u q)) :
    ∃ (κ : Type) (_ : Fintype κ) (ρ : κ → (Fin (n + 1) → ℝ) → ℝ) (σ : κ → SignType)
      (γ : κ → (Fin n → ℝ) → ℝ) (i : κ → Fin (n + 1)) (U : κ → Set (Fin (n + 1) → ℝ)),
      (∀ b, ContDiff ℝ ∞ (ρ b)) ∧ (∀ b y, 0 ≤ ρ b y) ∧ (∀ b, ContDiff ℝ 2 (γ b)) ∧
      (∀ b, IsOpen (U b)) ∧ (∀ b, tsupport (ρ b) ⊆ U b) ∧
      (∀ b y, y ∈ U b →
        (y ∈ extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀ '' (D ∩ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).source) ↔
          y ∈ graphRegion (σ b) (γ b) (i b))) ∧
      ∫ p in D, expansionM cov Y p ∂(NondegMetric.volumeMeasure g) =
        -∑ b, (σ b : ℝ) * graphFlux (γ b) (i b) (fun j y => ρ b y * divField g x₀ Y j y) := by
  set φ := extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀ with hφ
  have hsrc : MeasurableSet φ.source := (isOpen_extChartAt_source (I := 𝓘(ℝ, Fin (n + 1) → ℝ)) x₀).measurableSet
  have hDm : MeasurableSet (φ '' (D ∩ φ.source)) := measurableSet_image_extChartAt x₀ (hD.inter hsrc) inter_subset_right
  have hC : IsCompact (φ '' S) := hS.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hSs)
  have hCt : φ '' S ⊆ φ.target := by
    rintro _ ⟨p, hp, rfl⟩
    exact φ.map_source (hSs hp)
  have hF0 : ∀ j y, y ∉ φ '' S → divField g x₀ Y j y = 0 := by
    intro j y hy
    classical
    by_cases ht : y ∈ φ.target
    · have hq : φ.symm y ∉ S := fun hq => hy ⟨_, hq, φ.right_inv ht⟩
      rw [divField, ite_eq_left_iff.2 (fun h' => absurd ht h'), chartComp_eq_zero x₀ ht (hYS _ hq), Pi.zero_apply,
        mul_zero]
    · rw [divField, ite_eq_right_iff.2 (fun h' => absurd h' ht)]
  have hFs : ∀ j, tsupport (divField g x₀ Y j) ⊆ φ '' S := fun j =>
    closure_minimal (fun y hy => by_contra fun h' => hy (hF0 j y h')) hC.isClosed
  obtain ⟨κ, hκ, ρ, σ, γ, i, U, hρ, hρ0, hγ, hUo, hsU, hDE, -, hint⟩ :=
    exists_graph_atlas_integral_divergence_of_defining_function_loc_open (φ '' (D ∩ φ.source)) hDm (divField g x₀ Y)
      (fun j => (contDiff_divField g x₀ hY hS hSs hYS j).of_le (by simp))
      (fun j => HasCompactSupport.intro hC (hF0 j)) (by
        rintro y hy ⟨j, hj⟩
        have hyt : y ∈ φ.target := hCt (hFs j hj)
        have hpD : φ.symm y ∈ closure D := by
          have hcw : ContinuousWithinAt φ.symm (φ '' (D ∩ φ.source)) y :=
            (continuousAt_extChartAt_symm'' hyt).continuousWithinAt
          have := hcw.mem_closure_image hy
          refine closure_mono ?_ this
          rintro _ ⟨z, ⟨q, hq, rfl⟩, rfl⟩
          rw [φ.left_inv hq.2]
          exact hq.1
        obtain ⟨u, hu, hdu, hDu⟩ := hreg _ hpD
        exact ⟨u ∘ φ.symm, chart_defining_function x₀ hyt hu hdu hDu⟩)
  refine ⟨κ, hκ, ρ, σ, γ, i, U, hρ, hρ0, hγ, hUo, hsU, hDE, ?_⟩
  rw [integral_expansionM_chart cov g h hY x₀ hS hSs hYS hD, hint]


/-- **The divergence theorem for one chart piece**: for `Y` supported in a compact subset of the chart domain at `x₀` and
a domain `D` with regular boundary (by defining functions), `∫_D div Y d vol_g` is the flux of `√|g| Y` through the
boundary of the chart image of `D`, written in graph charts with a partition of unity. -/
theorem exists_chart_flux (cov : Connection 𝓘(ℝ, Fin (n + 1) → ℝ) M) (g : NondegMetric 𝓘(ℝ, Fin (n + 1) → ℝ) M)
    (h : cov.IsLeviCivita g) {Y : Π p : M, TangentSpace 𝓘(ℝ, Fin (n + 1) → ℝ) p}
    (hY : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) (𝓘(ℝ, Fin (n + 1) → ℝ).prod 𝓘(ℝ, Fin (n + 1) → ℝ)) ∞
      (fun q : M => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, Fin (n + 1) → ℝ) M)))
    (x₀ : M) {S : Set M} (hS : IsCompact S) (hSs : S ⊆ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).source)
    (hYS : ∀ p ∉ S, Y p = 0) {D : Set M} (hD : MeasurableSet D)
    (hreg : ∀ p ∈ closure D, ∃ u : M → ℝ, ContMDiffAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) 2 u p ∧
      (u p = 0 → mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) u p ≠ 0) ∧ ∀ᶠ q in 𝓝 p, (q ∈ D ↔ 0 ≤ u q)) :
    ∃ (κ : Type) (_ : Fintype κ) (ρ : κ → (Fin (n + 1) → ℝ) → ℝ) (σ : κ → SignType)
      (γ : κ → (Fin n → ℝ) → ℝ) (i : κ → Fin (n + 1)),
      (∀ b, ContDiff ℝ ∞ (ρ b)) ∧ (∀ b y, 0 ≤ ρ b y) ∧ (∀ b, ContDiff ℝ 2 (γ b)) ∧
      (∀ b y, y ∈ tsupport (ρ b) →
        (y ∈ extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀ '' (D ∩ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) x₀).source) ↔
          y ∈ graphRegion (σ b) (γ b) (i b))) ∧
      ∫ p in D, expansionM cov Y p ∂(NondegMetric.volumeMeasure g) =
        -∑ b, (σ b : ℝ) * graphFlux (γ b) (i b) (fun j y => ρ b y * divField g x₀ Y j y) := by
  obtain ⟨κ, hκ, ρ, σ, γ, i, U, hρ, hρ0, hγ, -, hsU, hDE, hint⟩ := exists_chart_flux_open cov g h hY x₀ hS hSs hYS hD hreg
  exact ⟨κ, hκ, ρ, σ, γ, i, hρ, hρ0, hγ, fun b y hy => hDE b y (hsU b hy), hint⟩

end ChartFlux

section Linear
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] (cov : Connection 𝓘(ℝ, Fin n → ℝ) M)

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] in
/-- The divergence is additive. -/
theorem expansionM_add {Y Z : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p} {x : M}
    (hY : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) x)
    (hZ : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, Z q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) x) :
    expansionM cov (fun p => Y p + Z p) x = expansionM cov Y x + expansionM cov Z x := by
  unfold expansionM
  rw [show (fun p => Y p + Z p) = Y + Z from rfl, cov.isCovariantDerivativeOnUniv.add hY hZ,
    ContinuousLinearMap.toLinearMap_add, map_add]

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] in
/-- The divergence of a finite sum of differentiable fields. -/
theorem expansionM_sum {ι : Type*} (s : Finset ι) (Y : ι → Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p) {x : M}
    (hY : ∀ a ∈ s, MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, Y a q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) x) :
    expansionM cov (fun p => ∑ a ∈ s, Y a p) x = ∑ a ∈ s, expansionM cov (Y a) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (fun p => ∑ a ∈ (∅ : Finset ι), Y a p) = 0 := by funext p; simp
    rw [h0, Finset.sum_empty]
    unfold expansionM
    rw [CovariantDerivative.zero]
    simp
  | insert b s hb ih =>
    have hYb := hY b (Finset.mem_insert_self b s)
    have hYs : ∀ a ∈ s, _ := fun a ha => hY a (Finset.mem_insert_of_mem ha)
    simp only [Finset.sum_insert hb]
    rw [expansionM_add cov hYb (MDifferentiableAt.sum_section hYs), ih hYs]

end Linear

section Main
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **The divergence theorem on a manifold** (Loomis–Sternberg, Theorem 6.1, with the volume density of a metric, (6.6)):
for a metric `g` of any signature on a manifold modelled on `ℝⁿ⁺¹`, its Levi-Civita connection, a smooth vector field `X`
vanishing outside a compact set `K`, and a measurable domain `D` with regular boundary (near every point of its closure
`D = {u ≥ 0}` with `u` of class `C²` and `du ≠ 0` where `u = 0`): `∫_D div X d vol_g` is the flux of `X` through the
boundary of `D`, written with a partition of unity `ψ_a` subordinate to charts and, in each chart, graph charts of the
boundary with cut-offs `ρ_{ab}` (the flux of `√|g| ψ_a X` out of the graph region, `graphFlux`).
In the graph charts, the region description holds on open sets `U a b ⊇ tsupport (ρ a b)`. -/
theorem divergence_theorem_manifold_open (g : NondegMetric 𝓘(ℝ, Fin (n + 1) → ℝ) M)
    {X : Π p : M, TangentSpace 𝓘(ℝ, Fin (n + 1) → ℝ) p}
    (hX : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) (𝓘(ℝ, Fin (n + 1) → ℝ).prod 𝓘(ℝ, Fin (n + 1) → ℝ)) ∞
      (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, Fin (n + 1) → ℝ) M)))
    {K : Set M} (hK : IsCompact K) (hXK : ∀ p ∉ K, X p = 0) {D : Set M} (hD : MeasurableSet D)
    (hreg : ∀ p ∈ closure D, ∃ u : M → ℝ, ContMDiffAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) 2 u p ∧
      (u p = 0 → mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) u p ≠ 0) ∧ ∀ᶠ q in 𝓝 p, (q ∈ D ↔ 0 ≤ u q)) :
    ∃ (ι : Type u) (_ : Fintype ι) (c : ι → M) (ψ : ι → M → ℝ) (κ : ι → Type) (_ : ∀ a, Fintype (κ a))
      (ρ : ∀ a, κ a → (Fin (n + 1) → ℝ) → ℝ) (σ : ∀ a, κ a → SignType) (γ : ∀ a, κ a → (Fin n → ℝ) → ℝ)
      (i : ∀ a, κ a → Fin (n + 1)) (U : ∀ a, κ a → Set (Fin (n + 1) → ℝ)),
      (∀ a, ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) ∞ (ψ a)) ∧
      (∀ a, tsupport (ψ a) ⊆ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) (c a)).source) ∧ (∀ p ∈ K, ∑ a, ψ a p = 1) ∧
      (∀ a b, ContDiff ℝ ∞ (ρ a b)) ∧ (∀ a b, ContDiff ℝ 2 (γ a b)) ∧
      (∀ a b, IsOpen (U a b)) ∧ (∀ a b, tsupport (ρ a b) ⊆ U a b) ∧
      (∀ a b y, y ∈ U a b →
        (y ∈ extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) (c a) '' (D ∩ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) (c a)).source) ↔
          y ∈ graphRegion (σ a b) (γ a b) (i a b))) ∧
      ∫ p in D, expansionM (leviCivita g) X p ∂(NondegMetric.volumeMeasure g) =
        -∑ a, ∑ b, (σ a b : ℝ) * graphFlux (γ a b) (i a b)
          (fun j y => ρ a b y * divField g (c a) (fun p => ψ a p • X p) j y) := by
  classical
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Fin (n + 1) → ℝ) M
  have hLC : (leviCivita g).IsLeviCivita g := ⟨leviCivita_torsion g, leviCivita_compat g⟩
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover (fun p => (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) p).source)
    (fun p _ => (isOpen_extChartAt_source (I := 𝓘(ℝ, Fin (n + 1) → ℝ)) p).mem_nhds (mem_extChartAt_source p))
  have hcov : K ⊆ ⋃ a : {x // x ∈ t}, (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) a.1).source := by
    intro p hp
    obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.1 (htK hp)
    exact mem_iUnion.2 ⟨⟨x, hx⟩, hpx⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin (n + 1) → ℝ) hK.isClosed
    (fun a : {x // x ∈ t} => (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) a.1).source)
    (fun a => isOpen_extChartAt_source a.1) hcov
  have hψ : ∀ a, ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) ∞ (f a) := fun a => (f a).contMDiff
  have hsum : ∀ p ∈ K, ∑ a, f a p = 1 := fun p hp => by
    have := f.sum_eq_one hp
    rwa [finsum_eq_sum_of_fintype] at this
  -- the pieces
  have hYsm : ∀ a, ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) (𝓘(ℝ, Fin (n + 1) → ℝ).prod 𝓘(ℝ, Fin (n + 1) → ℝ)) ∞
      (fun q : M => (⟨q, f a q • X q⟩ : TangentBundle 𝓘(ℝ, Fin (n + 1) → ℝ) M)) :=
    fun a => (hψ a).smul_section hX
  have hS : ∀ a, IsCompact (tsupport (f a) ∩ K) := fun a => hK.inter_left (isClosed_tsupport _)
  have hSs : ∀ a, tsupport (f a) ∩ K ⊆ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) a.1).source := fun a =>
    inter_subset_left.trans (hf a)
  have hYS : ∀ a, ∀ p ∉ tsupport (f a) ∩ K, f a p • X p = 0 := by
    intro a p hp
    by_cases hpK : p ∈ K
    · have : p ∉ tsupport (f a) := fun h' => hp ⟨h', hpK⟩
      rw [image_eq_zero_of_notMem_tsupport this, zero_smul]
    · rw [hXK p hpK, smul_zero]
  have hflux := fun a => exists_chart_flux_open (leviCivita g) g hLC (hYsm a) a.1 (hS a) (hSs a) (hYS a) hD hreg
  choose κ hκ ρ σ γ i U hρ hρ0 hγ hUo hsU hDE hint using hflux
  refine ⟨{x // x ∈ t}, inferInstance, fun a => a.1, fun a => f a, κ, hκ, ρ, σ, γ, i, U, hψ, hf, hsum, hρ, hγ,
    hUo, hsU, hDE, ?_⟩
  -- the divergence of `X` is the sum of those of the pieces
  have hXsum : (fun p => ∑ a, f a p • X p) = X := by
    funext p
    by_cases hp : p ∈ K
    · rw [← Finset.sum_smul, hsum p hp, one_smul]
    · simp [hXK p hp]
  have hdiv : ∀ p, expansionM (leviCivita g) X p =
      ∑ a, expansionM (leviCivita g) (fun q => f a q • X q) p := fun p => by
    have := expansionM_sum (leviCivita g) Finset.univ (fun a q => f a q • X q) (x := p)
      (fun a _ => (hYsm a p).mdifferentiableAt (by simp))
    rwa [hXsum] at this
  have hintg : ∀ a, Integrable (fun p => expansionM (leviCivita g) (fun q => f a q • X q) p)
      ((NondegMetric.volumeMeasure g).restrict D) := by
    intro a
    have hon : IntegrableOn (expansionM (leviCivita g) (fun q => f a q • X q)) (tsupport (f a) ∩ K)
        (NondegMetric.volumeMeasure g) :=
      NondegMetric.integrableOn_of_continuousOn g a.1 (hS a) (hSs a)
        ((continuousOn_expansionM (leviCivita g) g hLC (hYsm a) a.1).mono (hSs a)) subset_rfl
    have hall : Integrable (expansionM (leviCivita g) (fun q => f a q • X q)) (NondegMetric.volumeMeasure g) := by
      refine hon.integrable_of_forall_notMem_eq_zero fun p hp => ?_
      refine expansionM_eq_zero_of_eventually (leviCivita g) g hLC (hYsm a) ?_
      filter_upwards [(hS a).isClosed.isOpen_compl.mem_nhds hp] with q hq
      exact hYS a q hq
    exact hall.restrict
  rw [show (fun p => expansionM (leviCivita g) X p) = fun p => ∑ a, expansionM (leviCivita g) (fun q => f a q • X q) p
    from funext hdiv, integral_finsetSum _ fun a _ => hintg a, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a _ => hint a

/-- **The divergence theorem on a manifold** (Loomis–Sternberg, Theorem 6.1, with the volume density of a metric, (6.6)):
for a metric `g` of any signature on a manifold modelled on `ℝⁿ⁺¹`, its Levi-Civita connection, a smooth vector field `X`
vanishing outside a compact set `K`, and a measurable domain `D` with regular boundary (near every point of its closure
`D = {u ≥ 0}` with `u` of class `C²` and `du ≠ 0` where `u = 0`): `∫_D div X d vol_g` is the flux of `X` through the
boundary of `D`, written with a partition of unity `ψ_a` subordinate to charts and, in each chart, graph charts of the
boundary with cut-offs `ρ_{ab}` (the flux of `√|g| ψ_a X` out of the graph region, `graphFlux`). -/
theorem divergence_theorem_manifold (g : NondegMetric 𝓘(ℝ, Fin (n + 1) → ℝ) M)
    {X : Π p : M, TangentSpace 𝓘(ℝ, Fin (n + 1) → ℝ) p}
    (hX : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) (𝓘(ℝ, Fin (n + 1) → ℝ).prod 𝓘(ℝ, Fin (n + 1) → ℝ)) ∞
      (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, Fin (n + 1) → ℝ) M)))
    {K : Set M} (hK : IsCompact K) (hXK : ∀ p ∉ K, X p = 0) {D : Set M} (hD : MeasurableSet D)
    (hreg : ∀ p ∈ closure D, ∃ u : M → ℝ, ContMDiffAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) 2 u p ∧
      (u p = 0 → mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) u p ≠ 0) ∧ ∀ᶠ q in 𝓝 p, (q ∈ D ↔ 0 ≤ u q)) :
    ∃ (ι : Type u) (_ : Fintype ι) (c : ι → M) (ψ : ι → M → ℝ) (κ : ι → Type) (_ : ∀ a, Fintype (κ a))
      (ρ : ∀ a, κ a → (Fin (n + 1) → ℝ) → ℝ) (σ : ∀ a, κ a → SignType) (γ : ∀ a, κ a → (Fin n → ℝ) → ℝ)
      (i : ∀ a, κ a → Fin (n + 1)),
      (∀ a, ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) ∞ (ψ a)) ∧
      (∀ a, tsupport (ψ a) ⊆ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) (c a)).source) ∧ (∀ p ∈ K, ∑ a, ψ a p = 1) ∧
      (∀ a b, ContDiff ℝ ∞ (ρ a b)) ∧ (∀ a b, ContDiff ℝ 2 (γ a b)) ∧
      (∀ a b y, y ∈ tsupport (ρ a b) →
        (y ∈ extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) (c a) '' (D ∩ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) (c a)).source) ↔
          y ∈ graphRegion (σ a b) (γ a b) (i a b))) ∧
      ∫ p in D, expansionM (leviCivita g) X p ∂(NondegMetric.volumeMeasure g) =
        -∑ a, ∑ b, (σ a b : ℝ) * graphFlux (γ a b) (i a b)
          (fun j y => ρ a b y * divField g (c a) (fun p => ψ a p • X p) j y) := by
  obtain ⟨ι, hι, c, ψ, κ, hκ, ρ, σ, γ, i, U, hψ, hψs, hsum, hρ, hγ, -, hsU, hDE, hint⟩ :=
    divergence_theorem_manifold_open g hX hK hXK hD hreg
  exact ⟨ι, hι, c, ψ, κ, hκ, ρ, σ, γ, i, hψ, hψs, hsum, hρ, hγ, fun a b y hy => hDE a b y (hsU a b hy), hint⟩


/-- **The divergence theorem for a density** `ρ = f · dV_g` (Loomis–Sternberg, (6.6), p. 424: every density is `f dV` for
the volume density `dV` of a metric): `div⟨X, f dV_g⟩ = div_g(f X) dV_g`, so `∫_D div⟨X, ρ⟩` is `∫_D div_g(f X) d vol_g`, the
left side here, and the theorem is `divergence_theorem_manifold` for the field `f X`. -/
theorem divergence_theorem_manifold_density (g : NondegMetric 𝓘(ℝ, Fin (n + 1) → ℝ) M)
    {X : Π p : M, TangentSpace 𝓘(ℝ, Fin (n + 1) → ℝ) p}
    (hX : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) (𝓘(ℝ, Fin (n + 1) → ℝ).prod 𝓘(ℝ, Fin (n + 1) → ℝ)) ∞
      (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, Fin (n + 1) → ℝ) M)))
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) ∞ f) {K : Set M} (hK : IsCompact K) (hXK : ∀ p ∉ K, X p = 0) {D : Set M} (hD : MeasurableSet D)
    (hreg : ∀ p ∈ closure D, ∃ u : M → ℝ, ContMDiffAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) 2 u p ∧
      (u p = 0 → mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) u p ≠ 0) ∧ ∀ᶠ q in 𝓝 p, (q ∈ D ↔ 0 ≤ u q)) :
    ∃ (ι : Type u) (_ : Fintype ι) (c : ι → M) (ψ : ι → M → ℝ) (κ : ι → Type) (_ : ∀ a, Fintype (κ a))
      (ρ : ∀ a, κ a → (Fin (n + 1) → ℝ) → ℝ) (σ : ∀ a, κ a → SignType) (γ : ∀ a, κ a → (Fin n → ℝ) → ℝ)
      (i : ∀ a, κ a → Fin (n + 1)),
      (∀ a, ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ) ∞ (ψ a)) ∧
      (∀ a, tsupport (ψ a) ⊆ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) (c a)).source) ∧ (∀ p ∈ K, ∑ a, ψ a p = 1) ∧
      (∀ a b, ContDiff ℝ ∞ (ρ a b)) ∧ (∀ a b, ContDiff ℝ 2 (γ a b)) ∧
      (∀ a b y, y ∈ tsupport (ρ a b) →
        (y ∈ extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) (c a) '' (D ∩ (extChartAt 𝓘(ℝ, Fin (n + 1) → ℝ) (c a)).source) ↔
          y ∈ graphRegion (σ a b) (γ a b) (i a b))) ∧
      ∫ p in D, expansionM (leviCivita g) (fun q => f q • X q) p ∂(NondegMetric.volumeMeasure g) =
        -∑ a, ∑ b, (σ a b : ℝ) * graphFlux (γ a b) (i a b)
          (fun j y => ρ a b y * divField g (c a) (fun p => ψ a p • (f p • X p)) j y) :=
  divergence_theorem_manifold g (hf.smul_section hX) hK (fun p hp => by simp [hXK p hp]) hD hreg

end Main

end Lightlike
