import Lightlike.Regge.Geodesic.Metric

/-!
# The chart distance is Mathlib's Riemannian distance

The remainder of step 1 of RC6a. An open set `U ⊆ ℝⁿ` is a manifold in Mathlib
(`TopologicalSpace.Opens`, modelled on `ℝⁿ`), and a Riemannian metric `g` on `U`
(`IsRiemMetric g U`) makes its tangent bundle a Riemannian bundle: the inner product on the tangent
space at `x` is `g_x(v, w) = v ⬝ g(x) w`. Mathlib's `Manifold.riemannianEDist` is then the infimum
of the lengths of `C¹` paths in `U`, measured with these norms. This file proves that it agrees
with the distance `dist g U` of `Metric.lean`, so that the expansion of the squared distance
(`DistExpansion.lean`) is a statement about Mathlib's Riemannian distance.

The two definitions differ in two details, both handled here. Mathlib's paths are defined on
`[0, 1]` and are `C¹` as maps of manifolds with boundary; `IsAdmissible` asks for a `C¹` map on all
of `ℝ` that stays in `U` on `[0, 1]`. And `dist` is a real infimum, so it is the junk value `0`
when no admissible curve joins the two points, where `riemannianEDist` is `⊤`.

## Definitions

* `bilin A`: the bilinear form `(v, w) ↦ v ⬝ A w` of a matrix, as a continuous bilinear map.
* `IsRiemMetric.riemannianMetric`, `IsRiemMetric.riemannianBundle`: the Riemannian structure of
  the tangent bundle of `U` given by `g`. It depends on `g`, so it is not a global instance; the
  statements install it with `letI`.

## Main results

* `IsRiemMetric.enorm_tangent`: the norm of a tangent vector is `√(g_x(v, v))`.
* `mfderiv_eq_deriv`: the manifold derivative of a curve in `U` is its ordinary derivative.
* `IsRiemMetric.pathELength_eq`: Mathlib's length of a curve is `length g`.
* `IsRiemMetric.riemannianEDist_eq_iInf`: `riemannianEDist` is the infimum of the lengths of
  admissible curves.
* `IsRiemMetric.riemannianEDist_eq`: if an admissible curve joins `x` and `y`, then
  `riemannianEDist x y = dist g U x y`; otherwise `riemannianEDist x y = ⊤`
  (`IsRiemMetric.riemannianEDist_eq_top`).
* `IsRiemMetric.dist_eq_toReal_riemannianEDist`: `dist g U x y = (riemannianEDist x y).toReal`,
  with no hypothesis.
* `IsRiemMetric.exists_isAdmissible`, `IsRiemMetric.riemannianEDist_eq_of_isPreconnected`: on a
  connected `U` any two points are joined by an admissible curve, so the two distances agree
  everywhere.
-/

open Matrix Real MeasureTheory Set Manifold Bundle Filter Topology
open scoped ContDiff Manifold

namespace Lightlike.Geodesic

variable {n : ℕ}

/-! ## The Riemannian bundle of `g` -/

/-- The bilinear form `(v, w) ↦ v ⬝ A w` of a matrix `A`, as a continuous bilinear map. -/
noncomputable def bilin (A : Matrix (Fin n) (Fin n) ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((Fin n → ℝ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      Matrix.toLinearMap₂' ℝ A)

/-- `bilin A v w = v ⬝ A w`. -/
theorem bilin_apply (A : Matrix (Fin n) (Fin n) ℝ) (v w : Fin n → ℝ) :
    bilin A v w = v ⬝ᵥ (A *ᵥ w) := by
  simp [bilin, Matrix.toLinearMap₂'_apply']

/-- The sup norm of `ℝⁿ` is at most the Euclidean norm. -/
theorem norm_le_sqrt_eNormSq (v : Fin n → ℝ) : ‖v‖ ≤ √(eNormSq v) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  unfold eNormSq dotProduct
  rw [sq]
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
    (Finset.mem_univ i)

/-- The form of a symmetric matrix is symmetric. -/
theorem bilin_symm {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) (v w : Fin n → ℝ) :
    bilin A v w = bilin A w v := by
  rw [bilin_apply, bilin_apply, dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : TopologicalSpace.Opens (Fin n → ℝ)}

/-- The **Riemannian metric** of `g` on the tangent bundle of `U`: at `x` the inner product
`g_x(v, w) = v ⬝ g(x) w`. It is positive definite because `g` is, and it defines the topology of
`ℝⁿ` on each tangent space because `g(x) ≥ λ |·|²` for some `λ > 0`. -/
noncomputable def IsRiemMetric.riemannianMetric (hg : IsRiemMetric g U) :
    RiemannianMetric (fun x : U => TangentSpace 𝓘(ℝ, Fin n → ℝ) x) where
  inner x := bilin (g x)
  symm x v w := bilin_symm (hg.coord.symm x x.2) v w
  pos x v hv := (bilin_apply (g x) v v).symm ▸ hg.normSq_pos x.2 hv
  continuousAt x := by
    change ContinuousAt (fun v : Fin n → ℝ => bilin (g x) v v) 0
    fun_prop
  isVonNBounded x := by
    change Bornology.IsVonNBounded ℝ {v : Fin n → ℝ | bilin (g x) v v < 1}
    rw [NormedSpace.isVonNBounded_iff]
    obtain ⟨l, L, hl, -, hb⟩ := hg.exists_bounds_of_isCompact isCompact_singleton
      (singleton_subset_iff.mpr x.2)
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨√(1 / l), fun v hv => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (norm_le_sqrt_eNormSq v).trans (Real.sqrt_le_sqrt ?_)
    have h1 := (hb x rfl v).1
    have h2 : normSq g x v < 1 := by rw [normSq, ← bilin_apply]; exact hv
    rw [le_div_iff₀ hl]
    nlinarith

/-- The tangent bundle of `U` as a **Riemannian bundle** with the metric `g`. It is not a global
instance (it depends on `g`); statements install it with `letI`. -/
@[instance_reducible]
noncomputable def IsRiemMetric.riemannianBundle (hg : IsRiemMetric g U) :
    RiemannianBundle (fun x : U => TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :=
  ⟨hg.riemannianMetric⟩

/-- In the Riemannian bundle of `g` the norm of a tangent vector `v` at `x` is `√(g_x(v, v))`. -/
theorem IsRiemMetric.enorm_tangent (hg : IsRiemMetric g U) (x : U)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    letI := hg.riemannianBundle
    ‖v‖ₑ = ENNReal.ofReal √(normSq g x v) := by
  let := hg.riemannianBundle
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  exact congrArg (fun r => ENNReal.ofReal √r) (bilin_apply (g x) v v)

/-- The manifold derivative of a curve `γ` in `U`, applied to `1`, is the ordinary derivative of
the curve in `ℝⁿ`: the charts of `U` are restrictions of the identity. -/
theorem mfderiv_eq_deriv {γ : ℝ → U} {t : ℝ}
    (hd : DifferentiableAt ℝ (fun s => (γ s : Fin n → ℝ)) t) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ t 1 = deriv (fun s => (γ s : Fin n → ℝ)) t := by
  have hγ : ContinuousAt γ t :=
    Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hd.continuousAt
  have hm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ t :=
    (mdifferentiableAt_iff _ _).mpr ⟨hγ, by
      change DifferentiableWithinAt ℝ (fun s => (γ s : Fin n → ℝ)) (range id) t
      exact hd.differentiableWithinAt⟩
  rw [hm.mfderiv]
  change fderivWithin ℝ (fun s => (γ s : Fin n → ℝ)) (range id) t 1 = _
  rw [range_id, fderivWithin_univ, fderiv_apply_one_eq_deriv]

/-! ## Lengths and distances -/

/-- **Mathlib's length is `length g`.** If a curve `γ` in `U` agrees near every point of
`(0, 1)` with a `C¹` curve `c` that stays in `U` on `[0, 1]`, then Mathlib's length of `γ` on
`[0, 1]` is the length `length g c 0 1`. -/
theorem IsRiemMetric.pathELength_eq (hg : IsRiemMetric g U) {γ : ℝ → U} {c : ℝ → Fin n → ℝ}
    (hc : ContDiff ℝ 1 c) (hmem : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ (U : Set (Fin n → ℝ)))
    (hγ : ∀ t ∈ Ioo (0 : ℝ) 1, (fun s => (γ s : Fin n → ℝ)) =ᶠ[𝓝 t] c) :
    letI := hg.riemannianBundle
    pathELength 𝓘(ℝ, Fin n → ℝ) γ 0 1 = ENNReal.ofReal (length g c 0 1) := by
  let := hg.riemannianBundle
  have hadm : IsAdmissible (U : Set (Fin n → ℝ)) c (c 0) (c 1) := ⟨hc, hmem, rfl, rfl⟩
  have hint := hg.intervalIntegrable_speed hadm
  rw [pathELength_eq_lintegral_mfderiv_Ioo, length, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, ofReal_integral_eq_lintegral_ofReal]
  · refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have hd : DifferentiableAt ℝ (fun s => (γ s : Fin n → ℝ)) t :=
      (hγ t ht).differentiableAt_iff.mpr ((hc.differentiable one_ne_zero) t)
    rw [mfderiv_eq_deriv hd]
    refine (hg.enorm_tangent (γ t) _).trans ?_
    rw [(hγ t ht).deriv_eq, (hγ t ht).eq_of_nhds]
  · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hint).mono_set
      Ioo_subset_Ioc_self
  · exact Eventually.of_forall fun t => Real.sqrt_nonneg _

/-- Mathlib's Riemannian distance is at most the length of every admissible curve. -/
theorem IsRiemMetric.riemannianEDist_le_length (hg : IsRiemMetric g U) {x y : U}
    {c : ℝ → Fin n → ℝ} (hc : IsAdmissible (U : Set (Fin n → ℝ)) c x y) :
    letI := hg.riemannianBundle
    riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y ≤ ENNReal.ofReal (length g c 0 1) := by
  let := hg.riemannianBundle
  classical
  let γ : ℝ → U := fun t => if h : c t ∈ (U : Set (Fin n → ℝ)) then ⟨c t, h⟩ else x
  have hloc : ∀ t ∈ Icc (0 : ℝ) 1, (fun s => (γ s : Fin n → ℝ)) =ᶠ[𝓝 t] c := fun t ht => by
    filter_upwards [(U.isOpen.preimage hc.smooth.continuous).mem_nhds (hc.mem t ht)] with s hs
    simp only [γ]
    split_ifs with h
    · rfl
    · exact absurd hs h
  have hsm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) 1 γ (Icc 0 1) := fun t ht => by
    have h1 : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) 1 (Subtype.val ∘ γ) t :=
      contMDiffAt_iff_contDiffAt.mpr (hc.smooth.contDiffAt.congr_of_eventuallyEq (hloc t ht))
    have h2 : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) 1 γ t :=
      (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff γ univ t).mp h1
    exact h2.contMDiffWithinAt
  calc riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y ≤ pathELength 𝓘(ℝ, Fin n → ℝ) γ 0 1 :=
        riemannianEDist_le_pathELength hsm
          (Subtype.ext ((hloc 0 ⟨le_rfl, zero_le_one⟩).eq_of_nhds.trans hc.start))
          (Subtype.ext ((hloc 1 ⟨zero_le_one, le_rfl⟩).eq_of_nhds.trans hc.finish)) zero_le_one
    _ = ENNReal.ofReal (length g c 0 1) :=
        hg.pathELength_eq hc.smooth hc.mem fun t ht => hloc t (Ioo_subset_Icc_self ht)

/-- If Mathlib's Riemannian distance is less than `r`, some admissible curve is shorter than `r`.
Mathlib provides a `C¹` path on all of `ℝ` (constant near the endpoints); in `ℝⁿ` it is an
admissible curve. -/
theorem IsRiemMetric.exists_isAdmissible_of_riemannianEDist_lt (hg : IsRiemMetric g U)
    {x y : U} {r : ENNReal}
    (hr : letI := hg.riemannianBundle; riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y < r) :
    ∃ c, IsAdmissible (U : Set (Fin n → ℝ)) c x y ∧ ENNReal.ofReal (length g c 0 1) < r := by
  let := hg.riemannianBundle
  obtain ⟨γ, h0, h1, hγ, hlen, -, -⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
  have hc : ContDiff ℝ 1 (fun s => (γ s : Fin n → ℝ)) :=
    contMDiff_iff_contDiff.mp (contMDiff_subtype_val.comp hγ)
  refine ⟨fun s => γ s, ⟨hc, fun t _ => (γ t).2, by simp [h0], by simp [h1]⟩, ?_⟩
  rwa [← hg.pathELength_eq hc (fun t _ => (γ t).2) fun t _ => EventuallyEq.rfl]

/-- **Mathlib's Riemannian distance is the infimum of the lengths of admissible curves**, with no
hypothesis on `x` and `y` (the infimum of the empty family is `⊤`). -/
theorem IsRiemMetric.riemannianEDist_eq_iInf (hg : IsRiemMetric g U) (x y : U) :
    letI := hg.riemannianBundle
    riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y
      = ⨅ (c : ℝ → Fin n → ℝ) (_ : IsAdmissible (U : Set (Fin n → ℝ)) c x y),
          ENNReal.ofReal (length g c 0 1) := by
  let := hg.riemannianBundle
  refine le_antisymm (le_iInf₂ fun c hc => hg.riemannianEDist_le_length hc) ?_
  refine le_of_forall_gt fun r hr => ?_
  obtain ⟨c, hc, hlt⟩ := hg.exists_isAdmissible_of_riemannianEDist_lt hr
  exact (iInf₂_le c hc).trans_lt hlt

/-- If no admissible curve joins `x` and `y`, Mathlib's Riemannian distance is `⊤` (while
`dist g U x y` is the junk value `0`). -/
theorem IsRiemMetric.riemannianEDist_eq_top (hg : IsRiemMetric g U) {x y : U}
    (hxy : ¬ ∃ c, IsAdmissible (U : Set (Fin n → ℝ)) c x y) :
    letI := hg.riemannianBundle
    riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y = ⊤ := by
  let := hg.riemannianBundle
  by_contra h
  obtain ⟨c, hc, -⟩ := hg.exists_isAdmissible_of_riemannianEDist_lt (lt_top_iff_ne_top.mpr h)
  exact hxy ⟨c, hc⟩

/-- **The chart distance is Mathlib's Riemannian distance.** If an admissible curve joins `x`
and `y`, then `riemannianEDist x y = dist g U x y` for the Riemannian bundle of `g` on `U`. -/
theorem IsRiemMetric.riemannianEDist_eq (hg : IsRiemMetric g U) {x y : U}
    (hxy : ∃ c, IsAdmissible (U : Set (Fin n → ℝ)) c x y) :
    letI := hg.riemannianBundle
    riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y = ENNReal.ofReal (dist g U x y) := by
  let := hg.riemannianBundle
  have hne : {L | ∃ c, IsAdmissible (U : Set (Fin n → ℝ)) c x y ∧ length g c 0 1 = L}.Nonempty :=
    let ⟨c, hc⟩ := hxy; ⟨_, c, hc, rfl⟩
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨L, ⟨c, hc, rfl⟩, hL⟩ := exists_lt_of_csInf_lt hne
      (lt_add_of_pos_right (dist g U x y) (NNReal.coe_pos.mpr hε))
    calc riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y ≤ ENNReal.ofReal (length g c 0 1) :=
          hg.riemannianEDist_le_length hc
      _ ≤ ENNReal.ofReal (dist g U x y + ε) := ENNReal.ofReal_le_ofReal hL.le
      _ = ENNReal.ofReal (dist g U x y) + ε := by
          rw [ENNReal.ofReal_add (dist_nonneg (g := g) (U := (U : Set (Fin n → ℝ)))) ε.coe_nonneg,
            ENNReal.ofReal_coe_nnreal]
  · refine le_of_forall_gt fun r hr => ?_
    obtain ⟨c, hc, hlt⟩ := hg.exists_isAdmissible_of_riemannianEDist_lt hr
    exact (ENNReal.ofReal_le_ofReal (dist_le_length hc)).trans_lt hlt

/-- `dist g U x y = (riemannianEDist x y).toReal` for all `x, y ∈ U`: when no admissible curve
exists, both sides are `0`. -/
theorem IsRiemMetric.dist_eq_toReal_riemannianEDist (hg : IsRiemMetric g U) (x y : U) :
    letI := hg.riemannianBundle
    dist g U x y = (riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y).toReal := by
  let := hg.riemannianBundle
  by_cases hxy : ∃ c, IsAdmissible (U : Set (Fin n → ℝ)) c x y
  · rw [hg.riemannianEDist_eq hxy, ENNReal.toReal_ofReal dist_nonneg]
  · rw [hg.riemannianEDist_eq_top hxy, ENNReal.toReal_top, dist]
    convert Real.sInf_empty
    exact eq_empty_iff_forall_notMem.mpr fun _ ⟨c, hc, _⟩ => hxy ⟨c, hc⟩

/-! ## Connected domains -/

/-- The straight segment from `x` to `y` is admissible in a convex set containing both. -/
theorem isAdmissible_segment {V : Set (Fin n → ℝ)} (hV : Convex ℝ V) {x y : Fin n → ℝ}
    (hx : x ∈ V) (hy : y ∈ V) : IsAdmissible V (fun t => x + t • (y - x)) x y := by
  refine ⟨by fun_prop, fun t ht => ?_, by simp, by simp⟩
  have : x + t • (y - x) = (1 - t) • x + t • y := by
    simp only [smul_sub, sub_smul, one_smul]
    abel
  rw [this]
  exact hV hx hy (by linarith [ht.2]) ht.1 (by ring)

/-- An admissible curve in `V` is admissible in every larger set. -/
theorem IsAdmissible.mono {V W : Set (Fin n → ℝ)} (hVW : V ⊆ W) {c : ℝ → Fin n → ℝ}
    {x y : Fin n → ℝ} (hc : IsAdmissible V c x y) : IsAdmissible W c x y :=
  ⟨hc.smooth, fun t ht => hVW (hc.mem t ht), hc.start, hc.finish⟩

/-- On a connected `U` Mathlib's Riemannian distance is finite. Points of a small ball are joined
by a segment, and the relation "finite distance" is transitive (Mathlib's triangle inequality),
so it holds on all of the connected set `U`. -/
theorem IsRiemMetric.riemannianEDist_lt_top (hg : IsRiemMetric g U)
    (hU : IsPreconnected (U : Set (Fin n → ℝ))) (x y : U) :
    letI := hg.riemannianBundle
    riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y < ⊤ := by
  let := hg.riemannianBundle
  have : PreconnectedSpace U := Subtype.preconnectedSpace hU
  refine PreconnectedSpace.induction₂' (fun a b : U => riemannianEDist 𝓘(ℝ, Fin n → ℝ) a b < ⊤)
    (fun a => ?_) ⟨fun a b c hab hbc => (riemannianEDist_triangle (I := 𝓘(ℝ, Fin n → ℝ))
      (x := a) (y := b) (z := c)).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hab, hbc⟩)⟩ x y
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp U.isOpen a a.2
  filter_upwards [continuous_subtype_val.continuousAt.eventually (Metric.ball_mem_nhds _ hr)]
    with b hb
  have hab : riemannianEDist 𝓘(ℝ, Fin n → ℝ) a b < ⊤ :=
    (hg.riemannianEDist_le_length ((isAdmissible_segment (convex_ball (a : Fin n → ℝ) r)
      (Metric.mem_ball_self hr) hb).mono hball)).trans_lt ENNReal.ofReal_lt_top
  exact ⟨hab, (riemannianEDist_comm (I := 𝓘(ℝ, Fin n → ℝ)) (x := b) (y := a)).trans_lt hab⟩

/-- On a connected `U` any two points are joined by an admissible curve, so `dist g U` takes no
junk values there. -/
theorem IsRiemMetric.exists_isAdmissible (hg : IsRiemMetric g U)
    (hU : IsPreconnected (U : Set (Fin n → ℝ))) (x y : U) :
    ∃ c, IsAdmissible (U : Set (Fin n → ℝ)) c x y :=
  let ⟨c, hc, _⟩ := hg.exists_isAdmissible_of_riemannianEDist_lt (hg.riemannianEDist_lt_top hU x y)
  ⟨c, hc⟩

/-- **The chart distance is Mathlib's Riemannian distance on a connected `U`**, for all
`x, y ∈ U`. -/
theorem IsRiemMetric.riemannianEDist_eq_of_isPreconnected (hg : IsRiemMetric g U)
    (hU : IsPreconnected (U : Set (Fin n → ℝ))) (x y : U) :
    letI := hg.riemannianBundle
    riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y = ENNReal.ofReal (dist g U x y) :=
  hg.riemannianEDist_eq (hg.exists_isAdmissible hU x y)

end Lightlike.Geodesic
