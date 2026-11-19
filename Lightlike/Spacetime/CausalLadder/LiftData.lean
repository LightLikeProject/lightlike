import Lightlike.Spacetime.CausalLadder.ConeLift
import Lightlike.Spacetime.CausalLadder.BoundarylessChart
import Lightlike.Spacetime.CausalLadder.ChartModel
import Lightlike.Spacetime.Causal.CausalCurve

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- The metric evaluated on two `C¹` sections of the tangent bundle is `C¹`. -/
lemma contMDiffAt_one_metric_apply {s t : ∀ q : M, TangentSpace I q} {q₀ : M}
    (hs : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun q ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) q (s q)) q₀)
    (ht : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun q ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) q (t q)) q₀) :
    ContMDiffAt I 𝓘(ℝ, ℝ) 1 (fun q ↦ g.g q (s q) (t q)) q₀ := by
  have hg : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) q (g.g q)) q₀ :=
    (g.contMDiff q₀).of_le (by norm_num)
  have := ContMDiffAt.clm_bundle_apply₂ (E₃ := Bundle.Trivial M ℝ) (F₃ := ℝ) (b := id) hg hs ht
  simp only [contMDiffAt_totalSpace] at this
  exact this.2

/-- **The metric on chart-constant fields is `C¹` in the chart.** -/
lemma contDiffAt_frame_metric [BoundarylessManifold I M] (p : M) (w w' : E) :
    ContDiffAt ℝ 1 (fun x : E ↦ g.g ((extChartAt I p).symm x) (localField (I := I) p w ((extChartAt I p).symm x))
      (localField (I := I) p w' ((extChartAt I p).symm x))) (extChartAt I p p) := by
  have hb : (tTriv I M p).baseSet ∈ 𝓝 p :=
    (tTriv I M p).open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) p)
  have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) 1 (fun q ↦ g.g q (localField (I := I) p w q) (localField (I := I) p w' q)) p :=
    contMDiffAt_one_metric_apply
      (((localField_contMDiffOn (I := I) p w).contMDiffAt hb).of_le (by norm_num))
      (((localField_contMDiffOn (I := I) p w').contMDiffAt hb).of_le (by norm_num))
  have h2 : ContMDiffAt 𝓘(ℝ, E) I 1 (extChartAt I p).symm (extChartAt I p p) :=
    (((contMDiffOn_extChartAt_symm (I := I) (n := ∞) p).contMDiffAt
      (extChartAt_target_mem_nhds_of_boundaryless p))).of_le (by norm_num)
  have hleft : (extChartAt I p).symm (extChartAt I p p) = p :=
    (extChartAt I p).left_inv (mem_extChartAt_source p)
  have h1' : ContMDiffAt I 𝓘(ℝ, ℝ) 1 (fun q ↦ g.g q (localField (I := I) p w q) (localField (I := I) p w' q))
      ((extChartAt I p).symm (extChartAt I p p)) := by rw [hleft]; exact h1
  exact contMDiffAt_iff_contDiffAt.1 (h1'.comp (extChartAt I p p) h2)


set_option maxHeartbeats 1000000 in
/-- **Data for lifting causal curves in the chart at `p`.** See the module docstring. -/
theorem exists_lift_data [BoundarylessManifold I M] (p : M) :
    ∃ (lam : E →L[ℝ] ℝ) (ē : E) (m₀ r₁ : ℝ), 0 < m₀ ∧ 0 < r₁ ∧
      Metric.ball (extChartAt I p p) r₁ ⊆ (extChartAt I p).target ∧
      (∀ x ∈ Metric.ball (extChartAt I p p) r₁, (extChartAt I p).symm x ∈ (tTriv I M p).baseSet) ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∃ ε > 0, ∀ x ∈ Metric.ball (extChartAt I p p) r₁,
        ∀ x' ∈ Metric.ball (extChartAt I p p) r₁, dist x' x ≤ ν * m₀ → ∀ w : E,
          T.IsFutureCausal (localField (I := I) p w ((extChartAt I p).symm x)) →
            0 < lam w ∧ T.IsFutureTimelikeWith ε
              (localField (I := I) p (w + (ν * lam w) • ē) ((extChartAt I p).symm x')) := by
  classical
  obtain ⟨ξ, -⟩ := exists_chart_model T p
  set φ := extChartAt I p with hφ
  have hp : p ∈ (tTriv I M p).baseSet :=
    mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) p
  have hleft : φ.symm (φ p) = p := by exact (extChartAt I p).left_inv (mem_extChartAt_source p)
  -- frame matrices
  let Y : Fin n → ∀ q : M, TangentSpace I q := fun i q => localField (I := I) p (ξ i) q
  let Am : M → Fin n → Fin n → ℝ := fun q i j => g.g q (Y i q) (Y j q)
  let Bm : M → Fin n → ℝ := fun q i => g.g q (Y i q) (T.X q)
  let A : E → Fin n → Fin n → ℝ := fun x => Am (φ.symm x)
  let B : E → Fin n → ℝ := fun x => Bm (φ.symm x)
  have hL : ∀ q (hq : q ∈ (tTriv I M p).baseSet) (w : E),
      localField (I := I) p w q = ((tTriv I M p).linearEquivAt ℝ q hq).symm w := fun q hq w =>
    ((tTriv I M p).linearEquivAt_symm_apply (R := ℝ) q hq w).symm
  have hloc : ∀ q (hq : q ∈ (tTriv I M p).baseSet) (w : E),
      localField (I := I) p w q = ∑ i, ξ.repr w i • Y i q := fun q hq w => by
    rw [hL q hq]
    conv_lhs => rw [← ξ.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    simp only [Y, hL q hq]
  have hbilF : ∀ q (hq : q ∈ (tTriv I M p).baseSet) (w w' : E),
      g.g q (localField (I := I) p w q) (localField (I := I) p w' q) =
        bilForm (Am q) (fun i => ξ.repr w i) (fun i => ξ.repr w' i) := fun q hq w w' => by
    rw [hloc q hq w, hloc q hq w']
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
      smul_eq_mul, bilForm, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Am]; ring
  have hlinF : ∀ q (hq : q ∈ (tTriv I M p).baseSet) (w : E),
      g.g q (localField (I := I) p w q) (T.X q) = linForm (Bm q) (fun i => ξ.repr w i) :=
    fun q hq w => by
    rw [hloc q hq w]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
      smul_eq_mul, linForm]
    rfl
  have hrepr : ∀ (c : Fin n → ℝ) i, ξ.repr (ξ.equivFun.symm c) i = c i := fun c i => by
    rw [← Module.Basis.equivFun_apply, ξ.equivFun.apply_symm_apply]
  have hvec : ∀ c : Fin n → ℝ, (fun i => ξ.repr (ξ.equivFun.symm c) i) = c := fun c =>
    funext (hrepr c)
  obtain ⟨vec, hvecdef⟩ : ∃ vec : (Fin n → ℝ) → E, vec = ξ.equivFun.symm := ⟨_, rfl⟩
  have hvec' : ∀ c : Fin n → ℝ, (fun i => ξ.repr (vec c) i) = c := fun c => by
    rw [hvecdef]; exact hvec c
  have hQ : ∀ q (hq : q ∈ (tTriv I M p).baseSet) (c : Fin n → ℝ),
      quadForm (Am q) c = g.g q (localField (I := I) p (vec c) q) (localField (I := I) p (vec c) q) :=
    fun q hq c => by
    rw [hbilF q hq, hvec' c]; rfl
  have hLn : ∀ q (hq : q ∈ (tTriv I M p).baseSet) (c : Fin n → ℝ),
      linForm (Bm q) c = g.g q (localField (I := I) p (vec c) q) (T.X q) := fun q hq c => by
    rw [hlinF q hq, hvec' c]
  -- orthogonality
  have horth : ∀ q (hq : q ∈ (tTriv I M p).baseSet) (w : E),
      g.g q (localField (I := I) p w q) (localField (I := I) p w q) ≤ 0 →
      g.g q (localField (I := I) p w q) (T.X q) = 0 → w = 0 := fun q hq w h1 h2 => by
    have h3 := (g.lorentzian q).eq_zero_of_orthogonal_timelike (T.timelike q) h2 h1
    rw [hL q hq w] at h3
    exact (LinearEquiv.map_eq_zero_iff _).1 h3
  -- regularity of the frame matrices in the chart
  have hdiff : ∀ i j, ContDiffAt ℝ 1 (fun x => A x i j) (φ p) := fun i j => by
    exact contDiffAt_frame_metric (I := I) (g := g) p (ξ i) (ξ j)
  have hAc : ContinuousAt A (φ p) :=
    continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => (hdiff i j).continuousAt
  have hsymm : ∀ x i j, A x i j = A x j i := fun x i j => g.symm _ _ _
  have hBc : ContinuousAt B (φ p) := by
    refine continuousAt_pi.2 fun i => ?_
    have hb : (tTriv I M p).baseSet ∈ 𝓝 p := (tTriv I M p).open_baseSet.mem_nhds hp
    have h1 : ContinuousAt (fun q => g.g q (Y i q) (T.X q)) p :=
      continuousAt_metric_apply
        (((localField_contMDiffOn (I := I) p (ξ i)).contMDiffAt hb).of_le (by norm_num))
        (T.contMDiff p)
    have h2 : ContinuousAt φ.symm (φ p) := continuousAt_extChartAt_symm p
    exact h1.comp_of_eq h2 hleft
  have hlip : ∀ i j, ∃ K : NNReal, ∃ t ∈ 𝓝 (φ p), LipschitzOnWith K (fun x => A x i j) t :=
    fun i j => (hdiff i j).exists_lipschitzOnWith
  choose K t ht hK using hlip
  obtain ⟨K0, hK0⟩ : ∃ K0 : NNReal, ∀ i j, K i j ≤ K0 :=
    ⟨Finset.univ.sup fun i => Finset.univ.sup fun j => K i j, fun i j =>
      le_trans (Finset.le_sup (f := fun j => K i j) (Finset.mem_univ j))
        (Finset.le_sup (f := fun i => Finset.univ.sup fun j => K i j) (Finset.mem_univ i))⟩
  have ht0 : (⋂ i, ⋂ j, t i j) ∈ 𝓝 (φ p) :=
    Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => ht i j
  have hcover : {x | x ∈ φ.target ∧ φ.symm x ∈ coverSet T p} ∈ 𝓝 (φ p) := by
    refine inter_mem (extChartAt_target_mem_nhds_of_boundaryless (I := I) p) ?_
    have h2 : ContinuousAt φ.symm (φ p) := continuousAt_extChartAt_symm p
    exact h2.preimage_mem_nhds (by rw [hleft]; exact (isOpen_coverSet T p).mem_nhds (mem_coverSet_self T p))
  obtain ⟨r₀, hr₀, hsub0⟩ := Metric.mem_nhds_iff.1 (inter_mem ht0 hcover)
  have hbase : ∀ x ∈ Metric.ball (φ p) r₀, φ.symm x ∈ (tTriv I M p).baseSet := fun x hx =>
    (hsub0 hx).2.2.1
  have hKent : ∀ x ∈ Metric.ball (φ p) r₀, ∀ x' ∈ Metric.ball (φ p) r₀, ∀ i j,
      |A x' i j - A x i j| ≤ (K0 : ℝ) * dist x' x := fun x hx x' hx' i j => by
    have h1 : x ∈ t i j := Set.mem_iInter.1 (Set.mem_iInter.1 (hsub0 hx).1 i) j
    have h1' : x' ∈ t i j := Set.mem_iInter.1 (Set.mem_iInter.1 (hsub0 hx').1 i) j
    have := ((hK i j).weaken (hK0 i j)).dist_le_mul x' h1' x h1
    simpa [Real.dist_eq] using this
  obtain ⟨ē, hē⟩ : ∃ ē : E, ē = (tTriv I M p ⟨p, T.X p⟩).2 := ⟨_, rfl⟩
  obtain ⟨ec, hec⟩ : ∃ ec : Fin n → ℝ, ec = fun i => ξ.repr ē i := ⟨_, rfl⟩
  have hēp : localField (I := I) p ē p = T.X p := by rw [hē]; exact fieldAt_self T p
  have hA0 : A (φ p) = Am p := by show Am (φ.symm (φ p)) = Am p; rw [hleft]
  have hB0 : B (φ p) = Bm p := by show Bm (φ.symm (φ p)) = Bm p; rw [hleft]
  have hvec0 : ∀ q (hq : q ∈ (tTriv I M p).baseSet), localField (I := I) p (0 : E) q = 0 :=
    fun q hq => by rw [hL q hq]; exact map_zero _
  have h0 : ∀ c : Fin n → ℝ, c ≠ 0 → quadForm (A (φ p)) c ≤ 0 → linForm (B (φ p)) c ≠ 0 := by
    intro c hc hq hl
    rw [hA0, hQ p hp c] at hq
    rw [hB0, hLn p hp c] at hl
    have h1 := horth p hp (vec c) hq hl
    apply hc
    rw [← hvec' c, h1]; funext i; simp
  have hbilE : ∀ q (hq : q ∈ (tTriv I M p).baseSet) (c : Fin n → ℝ),
      bilForm (Am q) c ec = g.g q (localField (I := I) p (vec c) q) (localField (I := I) p ē q) := by
    intro q hq c; rw [hbilF q hq, hvec' c, hec]
  have h0e : ∀ c : Fin n → ℝ, c ≠ 0 → quadForm (A (φ p)) c ≤ 0 → bilForm (A (φ p)) c ec ≠ 0 := by
    intro c hc hq hb
    apply h0 c hc hq
    rw [hA0] at hb
    rw [hB0, hLn p hp c]
    rw [hbilE p hp c, hēp] at hb
    exact hb
  have hbil : ∀ x ∈ Metric.ball (φ p) r₀, ∀ c : Fin n → ℝ, quadForm (A x) c ≤ 0 →
      linForm (B x) c < 0 → bilForm (A x) c ec < 0 := by
    intro x hx c hq hl
    have hqb := hbase x hx
    obtain ⟨hy1, hy2⟩ := (hsub0 hx).2.2.2
    change quadForm (Am (φ.symm x)) c ≤ 0 at hq
    change linForm (Bm (φ.symm x)) c < 0 at hl
    rw [hQ _ hqb c] at hq
    rw [hLn _ hqb c] at hl
    show bilForm (Am (φ.symm x)) c ec < 0
    rw [hbilE _ hqb c]
    have hy1' : g.g (φ.symm x) (localField (I := I) p ē (φ.symm x))
        (localField (I := I) p ē (φ.symm x)) < 0 := by rw [hē]; exact hy1
    have hy2' : g.g (φ.symm x) (localField (I := I) p ē (φ.symm x)) (T.X (φ.symm x)) < 0 := by
      rw [hē]; exact hy2
    have hnp := (g.lorentzian (φ.symm x)).nonpos_of_futureCausal (T.timelike _) hq hy1'.le hl hy2'
    rcases lt_or_eq_of_le hnp with h | h
    · exact h
    · exfalso
      have h3 := (g.lorentzian (φ.symm x)).eq_zero_of_orthogonal_timelike hy1' h hq
      rw [h3] at hl
      simp at hl
  have hsgn : ∀ x ∈ Metric.ball (φ p) r₀, ∀ z : Fin n → ℝ, quadForm (A x) z < 0 →
      linForm (B x) z ≠ 0 := by
    intro x hx z hq hl
    have hqb := hbase x hx
    change quadForm (Am (φ.symm x)) z < 0 at hq
    change linForm (Bm (φ.symm x)) z = 0 at hl
    rw [hQ _ hqb z] at hq
    rw [hLn _ hqb z] at hl
    have h1 := horth _ hqb (vec z) hq.le hl
    rw [h1, hvec0 _ hqb] at hq
    simp at hq
  have heq : quadForm (A (φ p)) ec < 0 := by
    have h1 := hbilF p hp ē ē
    rw [hēp] at h1
    rw [hA0, hec]
    exact lt_of_eq_of_lt h1.symm (T.timelike p)
  have hel : linForm (B (φ p)) ec < 0 := by
    have h1 := hlinF p hp ē
    rw [hēp] at h1
    rw [hB0, hec]
    exact lt_of_eq_of_lt h1.symm (T.timelike p)
  obtain ⟨m₀, hm₀, r₁, hr₁, hr₁r₀, hres⟩ := cone_lift_estimate (A := A) (B := B) (e := ec) hAc hBc
    hsymm (K := (K0 : ℝ)) K0.coe_nonneg hr₀ hKent h0 h0e hbil hsgn heq hel
  have hfd : FiniteDimensional ℝ E := Module.Finite.of_basis ξ
  let lamL : E →ₗ[ℝ] ℝ := -(∑ i, Bm p i • (ξ.coord i : E →ₗ[ℝ] ℝ))
  let lam : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap lamL
  have hlam : ∀ w, lam w = -linForm (Bm p) (fun i => ξ.repr w i) := by
    intro w
    simp [lam, lamL, linForm, Module.Basis.coord_apply, mul_comm]
  have hball : Metric.ball (φ p) r₁ ⊆ Metric.ball (φ p) r₀ := Metric.ball_subset_ball hr₁r₀
  refine ⟨lam, ē, m₀, r₁, hm₀, hr₁, ?_, ?_, ?_⟩
  · intro x hx; exact (hsub0 (hball hx)).2.1
  · intro x hx; exact hbase x (hball hx)
  · intro ν hν hν1
    obtain ⟨ε, hε, hall⟩ := hres ν hν hν1
    refine ⟨ε, hε, fun x hx x' hx' hd w hw => ?_⟩
    have hxb := hbase x (hball hx)
    have hx'b := hbase x' (hball hx')
    obtain ⟨-, hw1, hw2⟩ := hw
    have hq : quadForm (A x) (fun i => ξ.repr w i) ≤ 0 := by
      have := hbilF _ hxb w w
      change quadForm (Am (φ.symm x)) _ ≤ 0
      exact le_of_eq_of_le this.symm hw1
    have hl : linForm (B x) (fun i => ξ.repr w i) < 0 := by
      have := hlinF _ hxb w
      change linForm (Bm (φ.symm x)) _ < 0
      exact lt_of_eq_of_lt this.symm hw2
    obtain ⟨hp', hQ', hL'⟩ := hall x hx x' hx' hd _ hq hl
    rw [hB0] at hp' hQ' hL'
    have hlw : lam w = -linForm (Bm p) (fun i => ξ.repr w i) := hlam w
    refine ⟨by rw [hlw]; exact hp', ?_⟩
    have hrep : (fun i => ξ.repr (w + (ν * lam w) • ē) i) =
        (fun i => ξ.repr w i) + (ν * -linForm (Bm p) (fun i => ξ.repr w i)) • ec := by
      funext i
      simp [hlw, hec]
    have e1 := hbilF _ hx'b (w + (ν * lam w) • ē) (w + (ν * lam w) • ē)
    have e2 := hlinF _ hx'b (w + (ν * lam w) • ē)
    rw [hrep] at e1 e2
    show g.g _ _ _ ≤ -ε * (g.g _ _ (T.X _)) ^ 2 ∧ g.g _ _ (T.X _) < 0
    rw [e1, e2]
    exact ⟨hQ', hL'⟩

end Lightlike.Causal
