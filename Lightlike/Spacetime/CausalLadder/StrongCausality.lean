import Lightlike.Spacetime.CausalLadder.ExitDiamond
import Lightlike.Spacetime.CausalLadder.LimitCurve
import Lightlike.Spacetime.Causal.Ladder

/-!
# Stable causality implies strong causality

Hawking–Ellis, Chapter 6 (the comparison with the book at a location is pending: the chapter was
not read for this statement). The proof uses a chart box around the point, the diamond of `ExitDiamond.lean`, and the
limit-curve theorem in one chart: if no diamond is causally convex, causal curves leave the box and
return; the exit points accumulate at a point of the future of `x` that has the same value of the
time function as `x` or a smaller one, which contradicts the strict monotonicity of the time function.

Supporting lemma for the causal ladder; the statement is the task `T-GE2-P10`.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- A sequence of points of the chart source whose chart images converge to the image of a point
of the source converges to that point. -/
theorem tendsto_of_chart {u : ℕ → M} {v : M} (p : M) (hv : v ∈ (extChartAt I p).source)
    (hu : ∀ k, u k ∈ (extChartAt I p).source)
    (h : Tendsto (fun k => extChartAt I p (u k)) atTop (𝓝 (extChartAt I p v))) :
    Tendsto u atTop (𝓝 v) := by
  have hs : ContinuousWithinAt (extChartAt I p).symm (extChartAt I p).target (extChartAt I p v) :=
    (continuousOn_extChartAt_symm p) _ ((extChartAt I p).map_source hv)
  have h2 : Tendsto (fun k => extChartAt I p (u k)) atTop
      (𝓝[(extChartAt I p).target] (extChartAt I p v)) :=
    tendsto_nhdsWithin_iff.2 ⟨h, Eventually.of_forall fun k => (extChartAt I p).map_source (hu k)⟩
  have := hs.tendsto.comp h2
  rw [(extChartAt I p).left_inv hv] at this
  refine this.congr fun k => ?_
  exact (extChartAt I p).left_inv (hu k)

/-- The endpoints of a `ReachIn` step lie in `K`. -/
theorem ReachIn.left_mem {K : Set M} {a b : M} (h : ReachIn T K a b) : a ∈ K := by
  obtain ⟨γ, s, t, hst, -, hK, e1, -⟩ := h
  rw [← e1]; exact hK s ⟨le_rfl, hst⟩

/-- The endpoints of a `ReachIn` step lie in `K`. -/
theorem ReachIn.right_mem {K : Set M} {a b : M} (h : ReachIn T K a b) : b ∈ K := by
  obtain ⟨γ, s, t, hst, -, hK, -, e2⟩ := h
  rw [← e2]; exact hK t ⟨hst, le_rfl⟩

/-- **Stable causality implies strong causality.** -/
theorem isStronglyCausal_of_isStablyCausal_aux [T2Space M] (h : IsStablyCausal T) :
    IsStronglyCausal T := by
  obtain ⟨τ, hτc, hτm⟩ := h
  intro x U hU
  obtain ⟨W, hW, hWb, ℓ, C, hC, hcone, hest⟩ := exists_cone_estimate_curve T x
  set φ := extChartAt I x with hφ
  have hxsrc : x ∈ φ.source := mem_extChartAt_source x
  have hfin : FiniteDimensional ℝ E := by
    obtain ⟨e, -⟩ := g.lorentzian x
    exact Module.Finite.of_basis (e.map ((tTriv I M x).linearEquivAt ℝ x
      (mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) x)))
  have hprop : ProperSpace E := FiniteDimensional.proper_real E
  -- a chart ball inside the neighbourhood
  have hN0 : interior W ∩ U ∈ 𝓝 x := inter_mem (interior_mem_nhds.2 hW) hU
  have htm : φ.target ∈ 𝓝[range I] (φ x) := extChartAt_target_mem_nhdsWithin x
  have hnhds : 𝓝[φ.target] (φ x) = 𝓝[range I] (φ x) := by
    rw [← nhdsWithin_inter_of_mem htm, inter_eq_left.2 (extChartAt_target_subset_range x)]
  have hpre : φ.symm ⁻¹' (interior W ∩ U) ∈ 𝓝[range I] (φ x) := by
    rw [← hnhds]
    have hcont := (continuousOn_extChartAt_symm x) (φ x) (φ.map_source hxsrc)
    refine hcont.preimage_mem_nhdsWithin ?_
    rw [φ.left_inv hxsrc]; exact hN0
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.1 (inter_mem htm hpre)
  set ρ : ℝ := r / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  set Kc : Set E := Metric.closedBall (φ x) ρ ∩ range I with hKc
  have hKcc : IsCompact Kc := (isCompact_closedBall _ _).inter_right I.isClosed_range
  have hKcsub : ∀ e ∈ Kc, e ∈ φ.target ∧ φ.symm e ∈ interior W ∩ U := by
    intro e he
    have : e ∈ Metric.ball (φ x) r ∩ range I :=
      ⟨Metric.closedBall_subset_ball (by rw [hρ]; linarith) he.1, he.2⟩
    exact hrsub this
  set K : Set M := φ.symm '' Kc with hK
  set O : Set M := {q | q ∈ φ.source ∧ ‖φ q - φ x‖ < ρ} with hO
  have hKcpt : IsCompact K := hKcc.image_of_continuousOn
    ((continuousOn_extChartAt_symm x).mono fun e he => (hKcsub e he).1)
  have hOopen : IsOpen O := by
    have : ContinuousOn (fun q => ‖φ q - φ x‖) φ.source :=
      ((continuousOn_extChartAt x).sub continuousOn_const).norm
    exact this.isOpen_inter_preimage (isOpen_extChartAt_source x) (isOpen_Iio (a := ρ))
  have hxO : x ∈ O := ⟨hxsrc, by simpa using hρpos⟩
  have hKφ : ∀ q ∈ K, q ∈ φ.source ∧ φ q ∈ Kc := by
    rintro q ⟨e, he, rfl⟩
    have ht := (hKcsub e he).1
    exact ⟨φ.map_target ht, by rwa [φ.right_inv ht]⟩
  have hOK : O ⊆ K := by
    rintro q ⟨hq, hlt⟩
    refine ⟨φ q, ⟨?_, ?_⟩, φ.left_inv hq⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]; exact hlt.le
    · exact extChartAt_target_subset_range x (φ.map_source hq)
  have hKint : K ⊆ interior W := by
    rintro _ ⟨e, he, rfl⟩; exact (hKcsub e he).2.1
  have hKU : K ⊆ U := by
    rintro _ ⟨e, he, rfl⟩; exact (hKcsub e he).2.2
  have hKW : K ⊆ W := hKint.trans interior_subset
  have hclK : closure O ⊆ K := closure_minimal hOK hKcpt.isClosed
  -- the diamonds
  set Vd : ℝ → Set M := fun δ => {q | q ∈ O ∧ ℓ (φ q) - ℓ (φ x) + ‖φ q - φ x‖ / C < δ ∧
      -(ℓ (φ q) - ℓ (φ x)) + ‖φ q - φ x‖ / C < δ} with hVd
  have hVO : ∀ δ, Vd δ ⊆ O := fun δ q hq => hq.1
  have hVnhds : ∀ δ, 0 < δ → Vd δ ∈ 𝓝 x := by
    intro δ hδ
    have hc : ContinuousAt φ x := continuousAt_extChartAt x
    have hc1 : ContinuousAt (fun q => ℓ (φ q) - ℓ (φ x) + ‖φ q - φ x‖ / C) x :=
      (((ℓ.continuous.continuousAt.comp hc).sub continuousAt_const).add
        ((hc.sub continuousAt_const).norm.div_const C))
    have hc2 : ContinuousAt (fun q => -(ℓ (φ q) - ℓ (φ x)) + ‖φ q - φ x‖ / C) x :=
      (((ℓ.continuous.continuousAt.comp hc).sub continuousAt_const).neg.add
        ((hc.sub continuousAt_const).norm.div_const C))
    have e1 : ℓ (φ x) - ℓ (φ x) + ‖φ x - φ x‖ / C < δ := by simpa using hδ
    have e2 : -(ℓ (φ x) - ℓ (φ x)) + ‖φ x - φ x‖ / C < δ := by simpa using hδ
    filter_upwards [hOopen.mem_nhds hxO, hc1.eventually (gt_mem_nhds e1),
      hc2.eventually (gt_mem_nhds e2)] with q h1 h2 h3 using ⟨h1, h2, h3⟩
  have hVchart : ∀ δ, ∀ q ∈ Vd δ, ‖φ q - φ x‖ < C * δ := by
    intro δ q hq
    have : ‖φ q - φ x‖ / C < δ := by linarith [hq.2.1, hq.2.2]
    rwa [div_lt_iff₀ hC, mul_comm] at this
  have key : ∃ δ > 0, ∀ y ∈ Vd δ, ∀ z ∈ Vd δ, ∀ w, w ∈ causalFuture T y → z ∈ causalFuture T w →
      w ∈ Vd δ := by
    by_contra hne
    push Not at hne
    set δk : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hδk
    have hδkpos : ∀ k, 0 < δk k := fun k => by simp only [hδk]; positivity
    have hδk0 : Tendsto δk atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    haveI : Nonempty M := ⟨x⟩
    choose! yk hyk zk hzk wk hwk using hne
    have hexit : ∀ k, ∃ m q : M, ReachIn T K (yk (δk k)) m ∧ ReachIn T K m q ∧ q ∈ K ∧ q ∉ O ∧
        zk (δk k) ∈ causalFuture T q := by
      intro k
      have hd := hδkpos k
      obtain ⟨h1, h2, h3⟩ := hwk (δk k) hd
      exact (exit_or_diamond T x hC hest hOopen hOK hKW hclK x (Vd := Vd (δk k)) rfl
        (hyk _ hd) (hzk _ hd) h1 h2).resolve_left h3
    choose m q hr1 hr2 hqK hqO hzq using hexit
    set y' : ℕ → M := fun k => yk (δk k) with hy'
    set z' : ℕ → M := fun k => zk (δk k) with hz'
    have hy'V : ∀ k, y' k ∈ Vd (δk k) := fun k => hyk _ (hδkpos k)
    have hz'V : ∀ k, z' k ∈ Vd (δk k) := fun k => hzk _ (hδkpos k)
    have hchart_tendsto : ∀ u : ℕ → M, (∀ k, u k ∈ Vd (δk k)) →
        Tendsto (fun k => φ (u k)) atTop (𝓝 (φ x)) := by
      intro u hu
      have : Tendsto (fun k => φ (u k) - φ x) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun k => (hVchart _ _ (hu k)).le) ?_
        simpa using hδk0.const_mul C
      exact tendsto_sub_nhds_zero_iff.1 this
    have hy'src : ∀ k, y' k ∈ φ.source := fun k => (hy'V k).1.1
    have hz'src : ∀ k, z' k ∈ φ.source := fun k => (hz'V k).1.1
    have hz'x : Tendsto z' atTop (𝓝 x) :=
      tendsto_of_chart x hxsrc hz'src (hchart_tendsto z' hz'V)
    -- compactness of the exit data
    have hmem : ∀ k, (φ (m k), φ (q k)) ∈ Kc ×ˢ Kc := fun k =>
      ⟨(hKφ _ (hr1 k).right_mem).2, (hKφ _ (hqK k)).2⟩
    obtain ⟨⟨em, eq⟩, ⟨hem, heq⟩, ψ, hψ, hlim⟩ := (hKcc.prod hKcc).tendsto_subseq hmem
    have hmlim : Tendsto (fun k => φ (m (ψ k))) atTop (𝓝 em) :=
      (continuous_fst.tendsto (em, eq)).comp hlim
    have hqlim : Tendsto (fun k => φ (q (ψ k))) atTop (𝓝 eq) :=
      (continuous_snd.tendsto (em, eq)).comp hlim
    have hmt := (hKcsub em hem).1
    have hqt := (hKcsub eq heq).1
    set mL : M := φ.symm em with hmL
    set qL : M := φ.symm eq with hqL
    have hmLK : mL ∈ K := ⟨em, hem, rfl⟩
    have hqLK : qL ∈ K := ⟨eq, heq, rfl⟩
    have hφm : φ mL = em := φ.right_inv hmt
    have hφq : φ qL = eq := φ.right_inv hqt
    have hψtop : Tendsto ψ atTop atTop := hψ.tendsto_atTop
    have hxK : x ∈ K := hOK hxO
    have hlc := limit_curve_of_cone_estimate T x hWb hC hcone hest K hKcpt hKint
    -- first step: `mL ∈ J⁺(x)`
    choose γ₁ s₁ t₁ hst₁ hγ₁ hK₁ hs₁ ht₁ using hr1
    have hJ1 : mL ∈ causalFuture T x := by
      obtain ⟨σ, α, β, hαβ, hσ, h1, h2⟩ := hlc (fun k => γ₁ (ψ k)) (fun k => s₁ (ψ k))
        (fun k => t₁ (ψ k)) x mL hxK hmLK (fun k => hst₁ _) (fun k => hγ₁ _) (fun k => hK₁ _)
        (((hchart_tendsto y' hy'V).comp hψtop).congr fun k => by
          simp only [Function.comp, hs₁, hy']; rfl)
        (by rw [hφm]; exact hmlim.congr fun k => by simp only [ht₁]; rfl)
      exact ⟨σ, α, β, hαβ, hσ, h1, h2⟩
    -- second step: `qL ∈ J⁺(mL)`
    choose γ₂ s₂ t₂ hst₂ hγ₂ hK₂ hs₂ ht₂ using hr2
    have hJ2 : qL ∈ causalFuture T mL := by
      obtain ⟨σ, α, β, hαβ, hσ, h1, h2⟩ := hlc (fun k => γ₂ (ψ k)) (fun k => s₂ (ψ k))
        (fun k => t₂ (ψ k)) mL qL hmLK hqLK (fun k => hst₂ _) (fun k => hγ₂ _) (fun k => hK₂ _)
        (by rw [hφm]; exact hmlim.congr fun k => by simp only [hs₂]; rfl)
        (by rw [hφq]; exact hqlim.congr fun k => by simp only [ht₂]; rfl)
      exact ⟨σ, α, β, hαβ, hσ, h1, h2⟩
    have hJ : qL ∈ causalFuture T x := causal_trans T hJ1 hJ2
    -- the limit of the exit points is outside `O`
    have hqsrc : ∀ k, q k ∈ φ.source := fun k => (hKφ _ (hqK k)).1
    have hqM : Tendsto (fun k => q (ψ k)) atTop (𝓝 qL) := by
      refine tendsto_of_chart x (hKφ _ hqLK).1 (fun k => hqsrc _) ?_
      rw [hφq]; exact hqlim
    have hqLO : qL ∉ O := fun hin => by
      have : qL ∈ Oᶜ := hOopen.isClosed_compl.mem_of_tendsto hqM
        (Eventually.of_forall fun k => hqO _)
      exact this hin
    have hne : qL ≠ x := fun h => hqLO (h ▸ hxO)
    have hlt : τ x < τ qL := hτm x qL hJ hne
    have hineq : ∀ k, τ (q (ψ k)) ≤ τ (z' (ψ k)) := by
      intro k
      by_cases hz : z' (ψ k) = q (ψ k)
      · rw [hz]
      · exact (hτm _ _ (hzq (ψ k)) hz).le
    have hle : τ qL ≤ τ x :=
      le_of_tendsto_of_tendsto (hτc.continuousAt.tendsto.comp hqM)
        (hτc.continuousAt.tendsto.comp (hz'x.comp hψtop)) (Eventually.of_forall hineq)
    linarith
  obtain ⟨δ, hδ, hconv⟩ := key
  exact ⟨Vd δ, hVnhds δ hδ, fun q hq => hKU (hOK (hVO δ hq)), hconv⟩

end Lightlike.Causal
