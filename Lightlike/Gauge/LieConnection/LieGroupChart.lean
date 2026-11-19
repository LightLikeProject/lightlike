import Lightlike.Gauge.LieConnection.LieGroup
import Lightlike.Gauge.LieConnection.ChartCalculus

/-!
# A Lie group in the chart at the identity (GC1, general Lie groups, attempt 2, part 1)

For a Lie group `G` modelled on a real Banach space `E` without boundary (`𝓘(ℝ, E)`), with `φ` the extended chart at
`1` and `y₀ = φ(1)`:
* `chartMul y z = φ(φ⁻¹(y) φ⁻¹(z))`, the multiplication in the chart, is `C³` near `(y₀, y₀)`
  (`contDiffAt_chartMul`);
* `mfderiv_apply_eq_fderiv`: a manifold derivative of a map `G → G` is the derivative of the map written in the charts;
* `adjoint_eq_fderiv_chart`: `Ad_{φ⁻¹(y)} w` is the derivative at `y₀` of the conjugation by `φ⁻¹(y)` written in the
  chart at `1`.

* `mpullback_mulInvariant_chart`, `bracket_eq_chart`: the pullback of `X_v` by `φ⁻¹` is `∂_z M(y, y₀) v`, so
  `⁅v, w⁆ = ∂_y(∂_z M(y, y₀) w) v - ∂_y(∂_z M(y, y₀) v) w`;
* `fderiv_adjoint_chart`: **`D(Ad)_1 = ad`** in the chart: the derivative at `y₀` of `y ↦ Ad_{φ⁻¹(y)} w` along `v` is
  `⁅v, w⁆` (by `fderiv_conj_chart`).

Difference from a general Lie group (representation): `G` is modelled on `𝓘(ℝ, E)` (no boundary, the case of every
Lie group).
-/

open Bundle Function VectorField Set Filter
open scoped Manifold Topology

noncomputable section

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup 𝓘(ℝ, E) (minSmoothness ℝ 3) G]

variable (E G) in
/-- The extended chart of `G` at the identity. -/
abbrev chart1 : PartialEquiv G E := extChartAt 𝓘(ℝ, E) (1 : G)

variable (E G) in
/-- The identity in the chart at the identity: `y₀ = φ(1)`. -/
abbrev chartOne : E := chart1 E G 1

variable (E G) in
/-- **The multiplication in the chart at the identity**: `M(y, z) = φ(φ⁻¹(y) φ⁻¹(z))`. -/
def chartMul (y z : E) : E := chart1 E G ((chart1 E G).symm y * (chart1 E G).symm z)

variable (E G) in
/-- The inverse in the chart at the identity: `ι(y) = φ(φ⁻¹(y)⁻¹)`. -/
def chartInv (y : E) : E := chart1 E G ((chart1 E G).symm y)⁻¹

lemma chart1_symm_chartOne : (chart1 E G).symm (chartOne E G) = 1 :=
  (chart1 E G).left_inv (mem_extChartAt_source (I := 𝓘(ℝ, E)) (1 : G))

lemma chartOne_mem_target : chartOne E G ∈ (chart1 E G).target :=
  mem_extChartAt_target (I := 𝓘(ℝ, E)) (1 : G)

lemma target_mem_nhds_chartOne : (chart1 E G).target ∈ 𝓝 (chartOne E G) :=
  extChartAt_target_mem_nhds (I := 𝓘(ℝ, E)) (1 : G)

lemma source_mem_nhds_one : (chart1 E G).source ∈ 𝓝 (1 : G) :=
  extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) (1 : G)

lemma continuousAt_chart1_symm : ContinuousAt (chart1 E G).symm (chartOne E G) :=
  continuousAt_extChartAt_symm (I := 𝓘(ℝ, E)) (1 : G)

/-- The multiplication in the chart is `C³` near `(y₀, y₀)`. -/
theorem contDiffAt_chartMul :
    ContDiffAt ℝ (minSmoothness ℝ 3) (fun p : E × E => chartMul E G p.1 p.2) (chartOne E G, chartOne E G) := by
  have hm := (contMDiff_mul (I := 𝓘(ℝ, E)) (n := minSmoothness ℝ 3) (E := E) (G := G)).contMDiffAt
    (x := ((1 : G), (1 : G)))
  rw [contMDiffAt_iff] at hm
  have h := hm.2
  simp only [extChartAt_prod, ModelWithCorners.range_prod, ModelWithCorners.range_eq_univ, univ_prod_univ,
    contDiffWithinAt_univ, mul_one] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun p => ?_)
  simp [chartMul, PartialEquiv.prod_symm]

/-- **A manifold derivative in the charts**: for `I = 𝓘(ℝ, E)` it is the derivative of the map written in the
extended charts. -/
lemma mfderiv_apply_eq_fderiv {f : G → G} {x : G} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) f x)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v =
      fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) x f) (extChartAt 𝓘(ℝ, E) x x) v := by
  rw [hf.mfderiv, ModelWithCorners.range_eq_univ, fderivWithin_univ]
  rfl

/-- **The adjoint action in the chart at the identity**: `Ad_p w` is the derivative at `y₀` of
`z ↦ φ(p φ⁻¹(z) p⁻¹)`. -/
lemma adjoint_eq_fderiv_chart (p : G) (w : GroupLieAlgebra 𝓘(ℝ, E) G) :
    adjoint 𝓘(ℝ, E) p w =
      fderiv ℝ (fun z : E => chart1 E G (conjMap p ((chart1 E G).symm z))) (chartOne E G) w := by
  have h := mfderiv_apply_eq_fderiv (mdifferentiableAt_conjMap p 1) w
  have hw : writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) (1 : G) (conjMap p) =
      fun z : E => chart1 E G (conjMap p ((chart1 E G).symm z)) := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply, conjMap_one]
  rw [hw] at h
  exact h

/-- Near `(y₀, y₀)` the products `φ⁻¹(y) φ⁻¹(z)` lie in the chart at `1`. -/
lemma eventually_mul_mem_source :
    ∀ᶠ p : E × E in 𝓝 (chartOne E G, chartOne E G),
      (chart1 E G).symm p.1 * (chart1 E G).symm p.2 ∈ (chart1 E G).source := by
  have hm : Continuous (fun q : G × G => q.1 * q.2) :=
    (contMDiff_mul (I := 𝓘(ℝ, E)) (n := minSmoothness ℝ 3) (G := G)).continuous
  have hc : ContinuousAt (fun p : E × E => (chart1 E G).symm p.1 * (chart1 E G).symm p.2)
      (chartOne E G, chartOne E G) :=
    hm.continuousAt.comp (f := fun p : E × E => ((chart1 E G).symm p.1, (chart1 E G).symm p.2))
      (((continuousAt_chart1_symm (E := E) (G := G)).comp (f := Prod.fst)
        (x := (chartOne E G, chartOne E G)) continuousAt_fst).prodMk
      ((continuousAt_chart1_symm (E := E) (G := G)).comp (f := Prod.snd)
        (x := (chartOne E G, chartOne E G)) continuousAt_snd))
  have h1 : (chart1 E G).symm (chartOne E G) * (chart1 E G).symm (chartOne E G) = 1 := by
    rw [chart1_symm_chartOne, mul_one]
  exact hc.preimage_mem_nhds (by rw [h1]; exact source_mem_nhds_one)

/-- Near `(y₀, y₀)`: `φ⁻¹(M(y, z)) = φ⁻¹(y) φ⁻¹(z)`. -/
lemma eventually_chart1_symm_chartMul :
    ∀ᶠ p : E × E in 𝓝 (chartOne E G, chartOne E G),
      (chart1 E G).symm (chartMul E G p.1 p.2) = (chart1 E G).symm p.1 * (chart1 E G).symm p.2 :=
  (eventually_mul_mem_source (E := E) (G := G)).mono fun _ hp => (chart1 E G).left_inv hp


/-- The left unit law in the chart: `M(y₀, z) = z` near `y₀`. -/
lemma eventually_chartMul_one_left : ∀ᶠ z in 𝓝 (chartOne E G), chartMul E G (chartOne E G) z = z := by
  filter_upwards [target_mem_nhds_chartOne (E := E) (G := G)] with z hz
  simp only [chartMul, chart1_symm_chartOne, one_mul]
  exact (chart1 E G).right_inv hz

/-- The right unit law in the chart: `M(y, y₀) = y` near `y₀`. -/
lemma eventually_chartMul_one_right : ∀ᶠ y in 𝓝 (chartOne E G), chartMul E G y (chartOne E G) = y := by
  filter_upwards [target_mem_nhds_chartOne (E := E) (G := G)] with y hy
  simp only [chartMul, chart1_symm_chartOne, mul_one]
  exact (chart1 E G).right_inv hy

lemma chartInv_chartOne : chartInv E G (chartOne E G) = chartOne E G := by
  rw [chartInv, chart1_symm_chartOne, inv_one]

lemma eventually_inv_mem_source :
    ∀ᶠ y in 𝓝 (chartOne E G), ((chart1 E G).symm y)⁻¹ ∈ (chart1 E G).source := by
  have hc : ContinuousAt (fun y => ((chart1 E G).symm y)⁻¹) (chartOne E G) :=
    (contMDiff_inv (I := 𝓘(ℝ, E)) (n := minSmoothness ℝ 3) (G := G)).continuous.continuousAt.comp
      (continuousAt_chart1_symm (E := E) (G := G))
  exact hc.preimage_mem_nhds (by rw [chart1_symm_chartOne, inv_one]; exact source_mem_nhds_one)

/-- The inverse law in the chart: `M(y, ι y) = y₀` near `y₀`. -/
lemma eventually_chartMul_chartInv : ∀ᶠ y in 𝓝 (chartOne E G), chartMul E G y (chartInv E G y) = chartOne E G := by
  filter_upwards [eventually_inv_mem_source (E := E) (G := G)] with y hy
  simp only [chartMul, chartInv, (chart1 E G).left_inv hy, mul_inv_cancel]

/-- The inverse in the chart is differentiable at `y₀`. -/
lemma differentiableAt_chartInv : DifferentiableAt ℝ (chartInv E G) (chartOne E G) := by
  have hs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) (minSmoothness ℝ 3) (chart1 E G).symm (chartOne E G) :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (1 : G)).contMDiffAt (target_mem_nhds_chartOne (E := E) (G := G))
  have hi : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) (minSmoothness ℝ 3) (fun x : G => x⁻¹) ((chart1 E G).symm (chartOne E G)) :=
    (contMDiff_inv (I := 𝓘(ℝ, E)) (n := minSmoothness ℝ 3) (G := G)).contMDiffAt
  have hφ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) (minSmoothness ℝ 3) (chart1 E G)
      ((chart1 E G).symm (chartOne E G))⁻¹ := by
    rw [chart1_symm_chartOne, inv_one]; exact contMDiffAt_extChartAt (I := 𝓘(ℝ, E))
  have h := (hφ.comp (chartOne E G) (hi.comp (chartOne E G) hs)).contDiffAt
  exact h.differentiableAt (by simp)

/-- Off-diagonal in the chart: for `y` near `y₀`, `z ↦ φ(p φ⁻¹(z) p⁻¹)` (`p = φ⁻¹(y)`) agrees near `y₀` with
`z ↦ M(M(y, z), ι y)`. -/
lemma eventually_conj_eq_chartMul :
    ∀ᶠ y in 𝓝 (chartOne E G),
      (fun z : E => chart1 E G (conjMap ((chart1 E G).symm y) ((chart1 E G).symm z))) =ᶠ[𝓝 (chartOne E G)]
        fun z : E => chartMul E G (chartMul E G y z) (chartInv E G y) := by
  have hprod := (eventually_mul_mem_source (E := E) (G := G))
  rw [nhds_prod_eq] at hprod
  filter_upwards [hprod.curry, eventually_inv_mem_source (E := E) (G := G)] with y hy hyinv
  filter_upwards [hy] with z hz
  simp only [chartMul, chartInv, conjMap, (chart1 E G).left_inv hz, (chart1 E G).left_inv hyinv]

/-- **The adjoint action in the chart**, near `y₀`: `Ad_{φ⁻¹(y)} w = ∂_z M(M(y, z), ι y)|_{z = y₀} w`. -/
lemma eventually_adjoint_eq (w : GroupLieAlgebra 𝓘(ℝ, E) G) :
    (fun y : E => adjoint 𝓘(ℝ, E) ((chart1 E G).symm y) w) =ᶠ[𝓝 (chartOne E G)]
      fun y => fderiv ℝ (fun z : E => chartMul E G (chartMul E G y z) (chartInv E G y)) (chartOne E G) w := by
  filter_upwards [eventually_conj_eq_chartMul (E := E) (G := G)] with y hy
  rw [adjoint_eq_fderiv_chart, hy.fderiv_eq]

lemma inverse_mfderiv_chart1_symm {y : E} (hy : y ∈ (chart1 E G).target) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chart1 E G).symm y).inverse =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chart1 E G) ((chart1 E G).symm y) := by
  have A := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := 𝓘(ℝ, E)) (x := (1 : G)) hy
  have B := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, E)) (x := (1 : G)) hy
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at A B
  exact ContinuousLinearMap.inverse_eq A B

/-- **The left-invariant vector fields in the chart**: near `y₀`, the pullback of `X_v` by `φ⁻¹` is
`y ↦ ∂_z M(y, y₀) v`. -/
lemma mpullback_mulInvariant_chart (v : GroupLieAlgebra 𝓘(ℝ, E) G) {y : E} (hy : y ∈ (chart1 E G).target) :
    mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (chart1 E G).symm (mulInvariantVectorField v) y =
      fderiv ℝ (chartMul E G y) (chartOne E G) v := by
  set p := (chart1 E G).symm y with hp
  have hpS : p ∈ (chartAt E (1 : G)).source := by
    have := (chart1 E G).map_target hy
    rwa [extChartAt_source] at this
  have hφ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (chart1 E G) (p * 1) := by
    rw [mul_one]; exact mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E)) hpS
  have hL : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (p * ·) (1 : G) := mdifferentiableAt_mul_left' p 1
  rw [mpullback, inverse_mfderiv_chart1_symm hy, ← hp, mulInvariantVectorField]
  have hc := mfderiv_comp (I' := 𝓘(ℝ, E)) (1 : G) hφ hL
  rw [show (p * 1) = p from mul_one p] at hc
  have happ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chart1 E G) p (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (p * ·) 1 v) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chart1 E G ∘ (p * ·)) 1 v := by
    rw [hc]; rfl
  refine happ.trans ?_
  rw [(hφ.comp (1 : G) hL).mfderiv, ModelWithCorners.range_eq_univ, fderivWithin_univ]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp]
  rfl

/-- **The bracket in the chart**: `⁅v, w⁆ = ∂_y(∂_z M(y, y₀) w) v - ∂_y(∂_z M(y, y₀) v) w`. -/
theorem bracket_eq_chart [CompleteSpace E] (v w : GroupLieAlgebra 𝓘(ℝ, E) G) :
    ⁅v, w⁆ = fderiv ℝ (fun y : E => fderiv ℝ (chartMul E G y) (chartOne E G) w) (chartOne E G) v -
      fderiv ℝ (fun y : E => fderiv ℝ (chartMul E G y) (chartOne E G) v) (chartOne E G) w := by
  have hV : ∀ u : GroupLieAlgebra 𝓘(ℝ, E) G,
      mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (chart1 E G).symm (mulInvariantVectorField u) =ᶠ[𝓝 (chartOne E G)]
        fun y => fderiv ℝ (chartMul E G y) (chartOne E G) u := fun u => by
    filter_upwards [target_mem_nhds_chartOne (E := E) (G := G)] with y hy
    exact mpullback_mulInvariant_chart u hy
  have h0 : ∀ u : GroupLieAlgebra 𝓘(ℝ, E) G, fderiv ℝ (chartMul E G (chartOne E G)) (chartOne E G) u = u := by
    intro u
    have he : chartMul E G (chartOne E G) =ᶠ[𝓝 (chartOne E G)] id := eventually_chartMul_one_left (E := E) (G := G)
    rw [he.fderiv_eq, fderiv_id]; rfl
  rw [GroupLieAlgebra.bracket_def, ← mlieBracketWithin_univ, mlieBracketWithin_apply,
    mfderiv_extChartAt_self]
  erw [ContinuousLinearMap.inverse_id]
  rw [ModelWithCorners.range_eq_univ, Set.preimage_univ, Set.univ_inter]
  erw [lieBracketWithin_univ, mpullbackWithin_univ, mpullbackWithin_univ, lieBracket_eq]
  simp only [ContinuousLinearMap.id_apply]
  rw [(hV w).fderiv_eq, (hV v).fderiv_eq, (hV v).eq_of_nhds, (hV w).eq_of_nhds, h0, h0]
  rfl

/-- **`D(Ad)_1 = ad`**, in the chart at the identity: the derivative at `y₀` of `y ↦ Ad_{φ⁻¹(y)} w` along `v` is
`⁅v, w⁆`. -/
theorem fderiv_adjoint_chart [CompleteSpace E] (v w : GroupLieAlgebra 𝓘(ℝ, E) G) :
    fderiv ℝ (fun y : E => adjoint 𝓘(ℝ, E) ((chart1 E G).symm y) w) (chartOne E G) v = ⁅v, w⁆ := by
  rw [bracket_eq_chart, (eventually_adjoint_eq w).fderiv_eq]
  have hM : ContDiffAt ℝ 2 (fun p : E × E => chartMul E G p.1 p.2) (chartOne E G, chartOne E G) :=
    (contDiffAt_chartMul (E := E) (G := G)).of_le (by simp; norm_num)
  exact fderiv_conj_chart (M := fun p : E × E => chartMul E G p.1 p.2) (ι := chartInv E G) hM
    (eventually_chartMul_one_left (E := E) (G := G)) (eventually_chartMul_one_right (E := E) (G := G))
    (differentiableAt_chartInv (E := E) (G := G)) chartInv_chartOne (eventually_chartMul_chartInv (E := E) (G := G)) v w

end Lightlike.Gauge
