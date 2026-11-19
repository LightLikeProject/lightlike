import Lightlike.Spacetime.Causal.SmoothOrientation
import Lightlike.Spacetime.Causal.BasicRelations
import Lightlike.Spacetime.CausalLadder.ChartCurve

/-!
# Straight lines in a chart are timelike curves

Around a point `p`, a constant vector `w` of the model space that is close to the coordinates of the
time orientation at `p` is, transported by the tangent-bundle trivialization, future timelike at
every point of a neighbourhood (`exists_timelike_nhds`). Hence a straight line in the chart with such
a direction is a future-directed timelike, so causal, curve (`chartLine_isFutureCausalCurve`).
Consequently there is a point in the causal future of every point near `p` (`exists_future_point`),
and a point in the causal past of every point near `p` (`exists_past_point`).

Supporting lemmas for the causal ladder; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- Continuity at a point of a finite sum. -/
theorem continuousAt_sum' {X ι : Type*} [TopologicalSpace X] (s : Finset ι) {f : ι → X → ℝ} {x : X}
    (h : ∀ i ∈ s, ContinuousAt (f i) x) : ContinuousAt (fun y => ∑ i ∈ s, f i y) x :=
  tendsto_finsetSum s h

/-- **Future timelike on a neighbourhood.** If `V` is future timelike at `p` (transported by the
trivialization), then every `w` near `V` is future timelike at every point near `p`. -/
theorem exists_timelike_nhds (p : M) (V : E)
    (hV1 : g.g p (localField (I := I) p V p) (localField (I := I) p V p) < 0)
    (hV2 : g.g p (localField (I := I) p V p) (T.X p) < 0) :
    ∃ N ∈ 𝓝 p, N ⊆ (tTriv I M p).baseSet ∧ ∃ ε > 0, ∀ q ∈ N, ∀ w : E, ‖w - V‖ < ε →
      g.g q (localField (I := I) p w q) (localField (I := I) p w q) < 0 ∧
      g.g q (localField (I := I) p w q) (T.X q) < 0 := by
  have hp : p ∈ (tTriv I M p).baseSet :=
    mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) p
  obtain ⟨e, -⟩ := g.lorentzian p
  let L : ∀ q ∈ (tTriv I M p).baseSet, TangentSpace I q ≃ₗ[ℝ] E :=
    fun q hq => (tTriv I M p).linearEquivAt ℝ q hq
  let ξ : Module.Basis (Fin n) ℝ E := e.map (L p hp)
  have : FiniteDimensional ℝ E := Module.Finite.of_basis ξ
  let Y : Fin n → ∀ q : M, TangentSpace I q := fun i q => localField (I := I) p (ξ i) q
  have hYsymm : ∀ i q (hq : q ∈ (tTriv I M p).baseSet), Y i q = (L q hq).symm (ξ i) := by
    intro i q hq
    exact ((tTriv I M p).linearEquivAt_symm_apply (R := ℝ) q hq (ξ i)).symm
  have hsm : ∀ w : E, ∀ q ∈ (tTriv I M p).baseSet,
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) 0
        (fun q ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) q
          (localField (I := I) p w q)) q := by
    intro w q hq
    exact (((localField_contMDiffOn (I := I) p w).contMDiffAt
      ((tTriv I M p).open_baseSet.mem_nhds hq)).of_le (by norm_num))
  have hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 0
      (fun q ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) q (T.X q)) p :=
    T.contMDiff p
  let G : M → Fin n → Fin n → ℝ := fun q i j => g.g q (Y i q) (Y j q)
  let b : M → Fin n → ℝ := fun q i => g.g q (Y i q) (T.X q)
  have hG : ContinuousAt G p :=
    continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
      continuousAt_metric_apply (hsm (ξ i) p hp) (hsm (ξ j) p hp)
  have hb : ContinuousAt b p :=
    continuousAt_pi.2 fun i => continuousAt_metric_apply (hsm (ξ i) p hp) hX
  -- expansions
  have hexp1 : ∀ q (hq : q ∈ (tTriv I M p).baseSet) (w : E),
      g.g q (localField (I := I) p w q) (localField (I := I) p w q) =
        ∑ i, ∑ j, ξ.repr w i * ξ.repr w j * G q i j := by
    intro q hq w
    have hw : localField (I := I) p w q = (L q hq).symm w :=
      ((tTriv I M p).linearEquivAt_symm_apply (R := ℝ) q hq w).symm
    rw [hw]
    conv_lhs => rw [← ξ.sum_repr w]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, G, hYsymm _ q hq,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [g.symm q ((L q hq).symm (ξ j)) ((L q hq).symm (ξ i))]; ring
  have hexp2 : ∀ q (hq : q ∈ (tTriv I M p).baseSet) (w : E),
      g.g q (localField (I := I) p w q) (T.X q) = ∑ i, ξ.repr w i * b q i := by
    intro q hq w
    have hw : localField (I := I) p w q = (L q hq).symm w :=
      ((tTriv I M p).linearEquivAt_symm_apply (R := ℝ) q hq w).symm
    rw [hw]
    conv_lhs => rw [← ξ.sum_repr w]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, b, hYsymm _ q hq]
  -- joint continuity at `(p, V)`
  have hcr : Continuous fun w : E => fun i => ξ.repr w i := by
    have : Continuous ⇑(ξ.equivFun : E →ₗ[ℝ] (Fin n → ℝ)) :=
      LinearMap.continuous_of_finiteDimensional _
    exact this
  have hF1 : ContinuousAt (fun qw : M × E => ∑ i, ∑ j, ξ.repr qw.2 i * ξ.repr qw.2 j * G qw.1 i j)
      (p, V) := by
    refine continuousAt_sum' _ fun i _ => continuousAt_sum' _ fun j _ => ?_
    have h1 : ContinuousAt (fun qw : M × E => ξ.repr qw.2 i) (p, V) :=
      ((continuous_apply i).comp hcr).continuousAt.comp continuousAt_snd
    have h2 : ContinuousAt (fun qw : M × E => ξ.repr qw.2 j) (p, V) :=
      ((continuous_apply j).comp hcr).continuousAt.comp continuousAt_snd
    have h3 : ContinuousAt (fun qw : M × E => G qw.1 i j) (p, V) :=
      ContinuousAt.comp (g := fun q => G q i j) (f := Prod.fst) (x := (p, V))
        (continuousAt_pi.1 (continuousAt_pi.1 hG i) j) continuousAt_fst
    exact (h1.mul h2).mul h3
  have hF2 : ContinuousAt (fun qw : M × E => ∑ i, ξ.repr qw.2 i * b qw.1 i) (p, V) := by
    refine continuousAt_sum' _ fun i _ => ?_
    have h1 : ContinuousAt (fun qw : M × E => ξ.repr qw.2 i) (p, V) :=
      ((continuous_apply i).comp hcr).continuousAt.comp continuousAt_snd
    have h2 : ContinuousAt (fun qw : M × E => b qw.1 i) (p, V) :=
      ContinuousAt.comp (g := fun q => b q i) (f := Prod.fst) (x := (p, V))
        (continuousAt_pi.1 hb i) continuousAt_fst
    exact h1.mul h2
  have e1 : (∑ i, ∑ j, ξ.repr V i * ξ.repr V j * G p i j) < 0 := by rw [← hexp1 p hp V]; exact hV1
  have e2 : (∑ i, ξ.repr V i * b p i) < 0 := by rw [← hexp2 p hp V]; exact hV2
  have hev : ∀ᶠ qw : M × E in 𝓝 (p, V), (∑ i, ∑ j, ξ.repr qw.2 i * ξ.repr qw.2 j * G qw.1 i j) < 0 ∧
      (∑ i, ξ.repr qw.2 i * b qw.1 i) < 0 :=
    (hF1.eventually (gt_mem_nhds e1)).and (hF2.eventually (gt_mem_nhds e2))
  rw [nhds_prod_eq, Filter.eventually_prod_iff] at hev
  obtain ⟨pa, hpa, pb, hpb, hall⟩ := hev
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpb
  refine ⟨pa ∩ (tTriv I M p).baseSet, inter_mem hpa ((tTriv I M p).open_baseSet.mem_nhds hp),
    inter_subset_right, ε, hε, ?_⟩
  rintro q ⟨hqa, hqb⟩ w hw
  have := hall (x := q) hqa (y := w) (hball (by simpa [dist_eq_norm] using hw))
  rw [hexp1 q hqb w, hexp2 q hqb w]
  exact this

/-- **A straight line in the chart is a future causal curve.** Let `N ⊆ (tTriv p).baseSet` and let
`w` be future timelike (transported by the trivialization) at every point of `N`. If the segment
`u₀ + t w`, `t ∈ [0, 1]`, lies in the target of the chart at `p` and its preimages lie in `N`, then
`t ↦ (extChartAt I p).symm (u₀ + t w)` is a future-directed causal curve on `[0, 1]`. -/
theorem chartLine_isFutureCausalCurve (p : M) {N : Set M} (hNb : N ⊆ (tTriv I M p).baseSet)
    (u₀ w : E)
    (hw : ∀ q ∈ N, g.g q (localField (I := I) p w q) (localField (I := I) p w q) < 0 ∧
      g.g q (localField (I := I) p w q) (T.X q) < 0)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, u₀ + t • w ∈ (extChartAt I p).target ∧
      (extChartAt I p).symm (u₀ + t • w) ∈ N) :
    IsFutureCausalCurve T (fun t => (extChartAt I p).symm (u₀ + t • w)) (Icc 0 1) := by
  set u : ℝ → E := fun t => u₀ + t • w with hu
  have hulip : LipschitzWith ‖w‖₊ u := LipschitzWith.of_dist_le_mul fun s t => by
    simp only [hu, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
      Real.norm_eq_abs, coe_nnnorm, Real.dist_eq]
    rw [mul_comm]
  have htarget : ∀ t ∈ Icc (0 : ℝ) 1, u t ∈ (extChartAt I p).target := fun t ht => (hseg t ht).1
  refine ⟨ordConnected_Icc, ?_, ?_⟩
  · exact isLocallyLipschitzOn_chart_symm hulip.lipschitzOnWith p htarget
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ),
      MeasureTheory.Measure.ae_ne MeasureTheory.volume (1 : ℝ)] with t h0 h1 ht
    have hsd : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) t := (uniqueDiffOn_Icc zero_lt_one) t ht
    have hder : HasDerivWithinAt u w (Icc (0 : ℝ) 1) t :=
      by simpa [hu] using (((hasDerivAt_id t).smul_const w).const_add u₀).hasDerivWithinAt
    obtain ⟨hmd, hcoord⟩ := mdifferentiableWithinAt_chart_symm p hsd ht hder htarget
    refine ⟨hmd, ?_⟩
    have hqN := (hseg t ht).2
    have hγb : ((extChartAt I p).symm ∘ u) t ∈ (tTriv I M p).baseSet := hNb hqN
    have := (tTriv I M p).symm_apply_apply_mk hγb
      (velocity I ((extChartAt I p).symm ∘ u) (Icc 0 1) t)
    rw [hcoord] at this
    show T.IsFutureCausal (velocity I ((extChartAt I p).symm ∘ u) (Icc 0 1) t)
    rw [← this]
    exact TimeOrientation.isFutureCausal_of_isFutureTimelike T (hw _ hqN)

/-- In a manifold without boundary the chart target is a neighbourhood of the image of the base
point (`isInteriorPoint_iff`). -/
theorem target_mem_nhds_of_boundaryless [BoundarylessManifold I M] (p : M) :
    (extChartAt I p).target ∈ 𝓝 (extChartAt I p p) := by
  have := (ModelWithCorners.isInteriorPoint_iff (I := I) (x := p)).1
    (BoundarylessManifold.isInteriorPoint' p)
  exact mem_of_superset (isOpen_interior.mem_nhds this) interior_subset

/-- The transported constant field is homogeneous in the constant. -/
theorem localField_smul (p : M) (r : ℝ) (w : E) {q : M} (hq : q ∈ (tTriv I M p).baseSet) :
    localField (I := I) p (r • w) q = r • localField (I := I) p w q := by
  have h1 : localField (I := I) p (r • w) q =
      ((tTriv I M p).linearEquivAt ℝ q hq).symm (r • w) :=
    ((tTriv I M p).linearEquivAt_symm_apply (R := ℝ) q hq (r • w)).symm
  have h2 : localField (I := I) p w q = ((tTriv I M p).linearEquivAt ℝ q hq).symm w :=
    ((tTriv I M p).linearEquivAt_symm_apply (R := ℝ) q hq w).symm
  rw [h1, h2, map_smul]

/-- **A chart segment gives a causal curve, at every small scale.** Around `p` (manifold without
boundary) there are a vector `V`, a radius `r₀ > 0` and `ε > 0` with the chart ball of radius `r₀`
inside the chart target, such that for every `s > 0` with `‖s V‖ < r₀ / 2`, any two points `a`, `b`
of the ball with `‖b - a - s V‖ < s ε` are joined by a future causal curve: the point
`(extChartAt I p).symm b` lies in the causal future of `(extChartAt I p).symm a`. -/
theorem exists_line_scale [BoundarylessManifold I M] (p : M) :
    ∃ (V : E) (r₀ ε : ℝ), V ≠ 0 ∧ 0 < r₀ ∧ 0 < ε ∧
      Metric.ball (extChartAt I p p) r₀ ⊆ (extChartAt I p).target ∧
      ∀ s : ℝ, 0 < s → ‖s • V‖ < r₀ / 2 →
        ∀ a ∈ Metric.ball (extChartAt I p p) r₀, ∀ b ∈ Metric.ball (extChartAt I p p) r₀,
          ‖b - a - s • V‖ < s * ε →
            (extChartAt I p).symm b ∈ causalFuture T ((extChartAt I p).symm a) := by
  have hp : p ∈ (tTriv I M p).baseSet :=
    mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) p
  set V : E := (tTriv I M p ⟨p, T.X p⟩).2 with hV
  have hUV : localField (I := I) p V p = T.X p := (tTriv I M p).symm_apply_apply_mk hp (T.X p)
  obtain ⟨N, hN, hNb, ε, hε, hnb⟩ := exists_timelike_nhds T p V
    (by rw [hUV]; exact T.timelike p) (by rw [hUV]; exact T.timelike p)
  -- a chart ball inside the target whose preimage lies in `N`
  have hpre : (extChartAt I p).symm ⁻¹' N ∈ 𝓝 (extChartAt I p p) := by
    have hcont : ContinuousAt (extChartAt I p).symm (extChartAt I p p) :=
      continuousAt_extChartAt_symm p
    exact hcont.preimage_mem_nhds (by rwa [(extChartAt I p).left_inv (mem_extChartAt_source p)])
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.1
    (inter_mem hpre (target_mem_nhds_of_boundaryless (I := I) p))
  have hV0 : V ≠ 0 := by
    intro h0
    have h1 : T.X p = 0 := by
      rw [← hUV, h0]
      have := (tTriv I M p).linearEquivAt_symm_apply (R := ℝ) p hp (0 : E)
      rw [show localField (I := I) p (0 : E) p = (tTriv I M p).symm p 0 from rfl, ← this]
      exact map_zero _
    have := T.timelike p
    rw [h1] at this
    simp at this
  refine ⟨V, r₀, ε, hV0, hr₀, hε, fun e he => (hball he).2, ?_⟩
  intro s hspos hsV a ha b hb hab
  set w : E := b - a with hw
  -- the segment from `a` to `b` stays in the ball
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, a + t • w ∈ Metric.ball (extChartAt I p p) r₀ := by
    intro t ht
    have : a + t • (b - a) = (1 - t) • a + t • b := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [hw, this]
    exact (convex_ball _ _) ha hb (by linarith [ht.1, ht.2]) ht.1 (by ring)
  have hsegN : ∀ t ∈ Icc (0 : ℝ) 1, (extChartAt I p).symm (a + t • w) ∈ N := fun t ht =>
    (hball (hseg t ht)).1
  have hsegT : ∀ t ∈ Icc (0 : ℝ) 1, a + t • w ∈ (extChartAt I p).target := fun t ht =>
    (hball (hseg t ht)).2
  -- the velocity is future timelike on `N`
  have hwt : ∀ q ∈ N, g.g q (localField (I := I) p w q) (localField (I := I) p w q) < 0 ∧
      g.g q (localField (I := I) p w q) (T.X q) < 0 := by
    intro q hq
    have hnorm : ‖s⁻¹ • w - V‖ < ε := by
      have : s⁻¹ • w - V = s⁻¹ • (w - s • V) := by
        rw [smul_sub s⁻¹ w (s • V), smul_smul, inv_mul_cancel₀ hspos.ne', one_smul]
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hspos)]
      have h2 : ‖w - s • V‖ < s * ε := by simpa [hw] using hab
      calc s⁻¹ * ‖w - s • V‖ < s⁻¹ * (s * ε) := mul_lt_mul_of_pos_left h2 (inv_pos.2 hspos)
        _ = ε := by field_simp
    obtain ⟨h1, h2⟩ := hnb q hq (s⁻¹ • w) hnorm
    have hqb := hNb hq
    have hsc : localField (I := I) p w q = s • localField (I := I) p (s⁻¹ • w) q := by
      rw [← localField_smul p s _ hqb, smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]
    rw [hsc]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact ⟨by nlinarith [mul_pos hspos hspos], by nlinarith⟩
  have hcurve := chartLine_isFutureCausalCurve T p hNb a w hwt (fun t ht => ⟨hsegT t ht, hsegN t ht⟩)
  refine ⟨_, 0, 1, zero_le_one, hcurve, ?_, ?_⟩
  · simp
  · have hbt : b ∈ (extChartAt I p).target := by
      simpa [hw] using hsegT 1 ⟨zero_le_one, le_rfl⟩
    simp [hw]


/-- **A chart segment gives a causal curve.** Around `p` (manifold without boundary) there are a
radius `r₀`, a scale `s > 0`, `ε > 0` and a vector `V` such that any two points `a`, `b` of the chart
ball of radius `r₀` with `‖b - a - s V‖ < s ε` are joined by a future causal curve: the point
`(extChartAt I p).symm b` lies in the causal future of `(extChartAt I p).symm a`. -/
theorem exists_line_between [BoundarylessManifold I M] (p : M) :
    ∃ (V : E) (s r₀ : ℝ), 0 < s ∧ 0 < r₀ ∧ ‖s • V‖ < r₀ / 2 ∧
      ∃ ε > 0, ∀ a ∈ Metric.ball (extChartAt I p p) r₀, ∀ b ∈ Metric.ball (extChartAt I p p) r₀,
        ‖b - a - s • V‖ < s * ε →
          (extChartAt I p).symm b ∈ causalFuture T ((extChartAt I p).symm a) := by
  obtain ⟨V, r₀, ε, -, hr₀, hε, -, h⟩ := exists_line_scale T p
  set s : ℝ := r₀ / (4 * (‖V‖ + 1)) with hs
  have hspos : 0 < s := by positivity
  have hsV : ‖s • V‖ < r₀ / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos, hs]
    have : ‖V‖ < ‖V‖ + 1 := by linarith
    calc r₀ / (4 * (‖V‖ + 1)) * ‖V‖ ≤ r₀ / (4 * (‖V‖ + 1)) * (‖V‖ + 1) :=
          mul_le_mul_of_nonneg_left this.le (by positivity)
      _ = r₀ / 4 := by field_simp
      _ < r₀ / 2 := by linarith
  exact ⟨V, s, r₀, hspos, hr₀, hsV, ε, hε, h s hspos hsV⟩

/-- Points near `p` in the chart: a neighbourhood on which the chart image is within `δ` of that of
`p`. -/
theorem eventually_chart_near (p : M) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q in 𝓝 p, q ∈ (extChartAt I p).source ∧ ‖extChartAt I p q - extChartAt I p p‖ < δ := by
  have hc : ContinuousAt (extChartAt I p) p := continuousAt_extChartAt p
  have h0 : ‖extChartAt I p p - extChartAt I p p‖ < δ := by simpa using hδ
  filter_upwards [extChartAt_source_mem_nhds (I := I) p,
    (hc.sub continuousAt_const).norm.eventually (gt_mem_nhds h0)] with q h1 h2
    using ⟨h1, h2⟩

/-- **A point in the causal future of every point near `p`** (boundaryless model). -/
theorem exists_future_point [BoundarylessManifold I M] (p : M) :
    ∃ z : M, ∀ᶠ y in 𝓝 p, z ∈ causalFuture T y := by
  obtain ⟨V, s, r₀, hs, hr₀, hsV, ε, hε, hline⟩ := exists_line_between T p
  refine ⟨(extChartAt I p).symm (extChartAt I p p + s • V), ?_⟩
  filter_upwards [eventually_chart_near (I := I) p (show 0 < min (r₀ / 2) (s * ε) by positivity)]
    with y ⟨hy, hyd⟩
  have hyd1 : ‖extChartAt I p y - extChartAt I p p‖ < r₀ / 2 := hyd.trans_le (min_le_left _ _)
  have hyd2 : ‖extChartAt I p y - extChartAt I p p‖ < s * ε := hyd.trans_le (min_le_right _ _)
  have h := hline (extChartAt I p y) (by rw [Metric.mem_ball, dist_eq_norm]; linarith)
    (extChartAt I p p + s • V) (by rw [Metric.mem_ball, dist_eq_norm]; simp; linarith)
    (by rw [show extChartAt I p p + s • V - extChartAt I p y - s • V =
        -(extChartAt I p y - extChartAt I p p) by abel, norm_neg]; exact hyd2)
  rwa [(extChartAt I p).left_inv hy] at h

/-- **A point in the causal past of every point near `p`** (boundaryless model). -/
theorem exists_past_point [BoundarylessManifold I M] (p : M) :
    ∃ z : M, ∀ᶠ y in 𝓝 p, y ∈ causalFuture T z := by
  obtain ⟨V, s, r₀, hs, hr₀, hsV, ε, hε, hline⟩ := exists_line_between T p
  refine ⟨(extChartAt I p).symm (extChartAt I p p - s • V), ?_⟩
  filter_upwards [eventually_chart_near (I := I) p (show 0 < min (r₀ / 2) (s * ε) by positivity)]
    with y ⟨hy, hyd⟩
  have hyd1 : ‖extChartAt I p y - extChartAt I p p‖ < r₀ / 2 := hyd.trans_le (min_le_left _ _)
  have hyd2 : ‖extChartAt I p y - extChartAt I p p‖ < s * ε := hyd.trans_le (min_le_right _ _)
  have h := hline (extChartAt I p p - s • V) (by rw [Metric.mem_ball, dist_eq_norm]; simp; linarith)
    (extChartAt I p y) (by rw [Metric.mem_ball, dist_eq_norm]; linarith)
    (by rw [show extChartAt I p y - (extChartAt I p p - s • V) - s • V =
        extChartAt I p y - extChartAt I p p by abel]; exact hyd2)
  rwa [(extChartAt I p).left_inv hy] at h

end Lightlike.Causal
