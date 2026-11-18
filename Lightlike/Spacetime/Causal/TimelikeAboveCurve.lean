import Lightlike.Spacetime.Causal.ChainCurve
import Lightlike.Spacetime.Causal.ChainSequence
import Lightlike.Spacetime.Causal.CauchySeparation
import Lightlike.Spacetime.Causal.CauchyCover
import Lightlike.Spacetime.CausalLadder.CurveContinuity

/-!
# An inextendible causal curve through `I⁺(S)` that misses `S` gives an inextendible timelike curve that misses `S`

Let `S` be achronal such that every point lies in `S`, `I⁺(S)` or `I⁻(S)`. Let `λ` be an inextendible future
causal curve through a point of `I⁺(S)` that does not meet `S` at parameters up to that point. Then
`λ` stays in `I⁺(S)` in the past of that point (a preconnected set that misses `S`, `I⁺(S)` and `I⁻(S)`
being disjoint open sets), and a descending chain of points `q k ∈ I⁺(λ (t k))` joined by timelike pieces,
followed by the future half of an inextendible timelike curve through `q 0`, is an inextendible
future-directed timelike curve that lies in `I⁺(S)`, hence misses `S` (`exists_timelike_missing`).
The push-up `J⁺ then I⁺ ⊆ I⁺` (the statement of `T-GE2-P6`) is a hypothesis `hpush` of the theorem, so
this is conditional library code, with no task file and no catalogue claim. This is the perturbation step of the
proof that a Cauchy surface has full domain of dependence.

Supporting lemma for the causal structure; no catalogue entry.
-/

open Set Bundle Manifold Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

omit [IsManifold I ∞ M] in
/-- A curve without endpoints has no least parameter. -/
lemma noEndpoints_no_min {γ : ℝ → M} {s : Set ℝ} (h : NoEndpoints γ s) :
    ∀ t ∈ s, ∃ u ∈ s, u < t := by
  intro t ht
  by_contra hcon
  push Not at hcon
  exact h.2.2 (γ t) fun U hU => ⟨t, ht, fun t' ht' ht'le => by
    have : t' = t := le_antisymm ht'le (hcon t' ht')
    rw [this]; exact mem_of_mem_nhds hU⟩

omit [IsManifold I ∞ M] in
/-- A curve without endpoints has no greatest parameter. -/
lemma noEndpoints_no_max {γ : ℝ → M} {s : Set ℝ} (h : NoEndpoints γ s) :
    ∀ t ∈ s, ∃ u ∈ s, t < u := by
  intro t ht
  by_contra hcon
  push Not at hcon
  exact h.2.1 (γ t) fun U hU => ⟨t, ht, fun t' ht' hle => by
    have : t' = t := le_antisymm (hcon t' ht') hle
    rw [this]; exact mem_of_mem_nhds hU⟩

/-- The parameter set of a curve without endpoints is open. -/
lemma isOpen_of_noEndpoints {γ : ℝ → M} {s : Set ℝ} (hs : s.OrdConnected) (h : NoEndpoints γ s) :
    IsOpen s := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  obtain ⟨u, hu, hut⟩ := noEndpoints_no_min h t ht
  obtain ⟨v, hv, htv⟩ := noEndpoints_no_max h t ht
  exact mem_of_superset (Ioo_mem_nhds hut htv) fun x hx => hs.out hu hv ⟨hx.1.le, hx.2.le⟩

/-- A causal curve runs into the causal future. -/
lemma lam_mem_causalFuture {lam : ℝ → M} {s : Set ℝ}
    (h : IsCurveWith (I := I) (fun _ v ↦ T.IsFutureCausal v) lam s) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≤ b) : lam b ∈ causalFuture T (lam a) := by
  rcases hab.lt_or_eq with hlt | heq
  · exact ⟨lam, a, b, hab, IsCurveWith.restrict h (fun r hr => h.ordConnected.out ha hb hr) hlt, rfl, rfl⟩
  · subst heq; exact self_mem_causalFuture T _

/-- Later points of a timelike curve are in the chronological future of earlier ones. -/
lemma mem_chronFuture_of_lt {c : ℝ → M} {s : Set ℝ} (h : IsFutureTimelikeCurve T c s) {u v : ℝ}
    (hu : u ∈ s) (hv : v ∈ s) (huv : u < v) : c v ∈ chronFuture T (c u) :=
  ⟨c, u, v, huv, h.restrict T (fun r hr => h.1.ordConnected.out hu hv hr) huv, rfl, rfl⟩

section Main

variable [T2Space M] [SecondCountableTopology M] [BoundarylessManifold I M]

/-- **An inextendible causal curve through `I⁺(S)` that misses `S` in the past yields an inextendible
timelike curve that misses `S`.** See the module docstring. -/
theorem exists_timelike_missing
    (hpush : ∀ x y z : M, y ∈ causalFuture T x → z ∈ chronFuture T y → z ∈ chronFuture T x)
    {S : Set M} (hA : IsAchronal T S)
    (hcov : ∀ p : M, p ∈ S ∨ p ∈ chronFutureSet T S ∨ p ∈ chronPastSet T S)
    {lam : ℝ → M} {s : Set ℝ}
    (hlam : IsInextendibleWith (I := I) (fun _ v ↦ T.IsFutureCausal v) lam s)
    {t₁ : ℝ} (ht₁ : t₁ ∈ s) (hp : lam t₁ ∈ chronFutureSet T S)
    (hmiss : ∀ t ∈ s, t ≤ t₁ → lam t ∉ S) :
    ∃ (G : ℝ → M) (s' : Set ℝ), IsInextendibleFutureTimelike T G s' ∧ ∀ u ∈ s', G u ∉ S := by
  obtain ⟨hlc, hne, hnf, hnp⟩ := hlam
  have hNE : NoEndpoints lam s := ⟨hne, hnf, hnp⟩
  have hso : s.OrdConnected := hlc.ordConnected
  have hcont : ContinuousOn lam s := hlc.lipschitz.continuousOn
  -- the past part
  set sP : Set ℝ := s ∩ Iic t₁ with hsP
  have hsPo : sP.OrdConnected := hso.inter ordConnected_Iic
  have ht₁sP : t₁ ∈ sP := ⟨ht₁, mem_Iic.2 le_rfl⟩
  have hnm : ∀ t ∈ sP, ∃ u ∈ sP, u < t := by
    intro t ht
    obtain ⟨u, hu, hut⟩ := noEndpoints_no_min hNE t ht.1
    exact ⟨u, ⟨hu, hut.le.trans ht.2⟩, hut⟩
  have hFo : IsOpen (chronFutureSet T S) :=
    isOpen_biUnion fun x _ => isOpen_chronFuture_of_reach T x
  have hPo : IsOpen (chronPastSet T S) :=
    isOpen_biUnion fun x _ => isOpen_chronPast T x
  -- `λ` stays in `I⁺(S)` in the past of `t₁`
  have hpastF : ∀ t ∈ sP, lam t ∈ chronFutureSet T S := by
    have hC : IsPreconnected (lam '' sP) :=
      (hsPo.isPreconnected).image lam (hcont.mono inter_subset_left)
    have hsub := subset_chronFutureSet_of_preconnected T hA hFo hPo (C := lam '' sP)
      (fun p hp => by
        obtain ⟨t, ht, rfl⟩ := hp
        rcases hcov (lam t) with h | h | h
        · exact absurd h (hmiss t ht.1 ht.2)
        · exact Or.inl h
        · exact Or.inr h) hC ⟨t₁, ht₁sP, rfl⟩ hp
    exact fun t ht => hsub ⟨t, ht, rfl⟩
  -- the chain above `λ`
  obtain ⟨q₀, -, hq₀⟩ := exists_mem_chronFuture_near T (lam t₁) (V := univ) univ_mem
  obtain ⟨t, q, ht0, hq0, hanti, hts, hexh, hqf, hqlt, hqend⟩ :=
    exists_chain T hpush hsPo (hcont.mono inter_subset_left) hnm
      (fun a ha b hb hab => lam_mem_causalFuture T hlc ha.1 hb.1 hab) ht₁sP hq₀
  have hqS : ∀ k, q k ∈ chronFutureSet T S := by
    intro k
    obtain ⟨x, hx, hlx⟩ := Set.mem_iUnion₂.1 (hpastF (t k) (hts k))
    exact Set.mem_iUnion₂.2 ⟨x, hx, chron_trans T hlx (hqf k)⟩
  obtain ⟨G, β, hβ0, hβanti, hGβ, hGt⟩ := exists_chain_curve T hqlt
  have hG0 : G 0 = q₀ := by
    have := hGβ 0
    rw [hβ0, hq0] at this
    exact this
  -- the future part
  obtain ⟨R, sR, tR, hR, htR, hRq⟩ := exists_inextendible_through T q₀
  have hsRo : IsOpen sR := isOpen_of_noEndpoints hR.1.1.ordConnected hR.2
  let F : ℝ → M := fun σ => if σ ≤ 0 then G σ else R (σ + tR)
  let s' : Set ℝ := {σ | (σ < 0 ∧ ∃ K, β (K + 1) < σ) ∨ (0 ≤ σ ∧ σ + tR ∈ sR)}
  have h0s' : (0 : ℝ) ∈ s' := Or.inr ⟨le_rfl, by simpa using htR⟩
  have hβneg : ∀ K, β (K + 1) < 0 := fun K => by rw [← hβ0]; exact hβanti (Nat.succ_pos K)
  -- `s'` is an interval and open
  have hsRord := hR.1.1.ordConnected
  have hs'ord : s'.OrdConnected := by
    refine ⟨fun x hx y hy z hz => ?_⟩
    rcases hx with ⟨hx0, K, hK⟩ | ⟨hx0, hxR⟩
    · rcases hy with ⟨hy0, -⟩ | ⟨hy0, hyR⟩
      · exact Or.inl ⟨lt_of_le_of_lt hz.2 hy0, K, lt_of_lt_of_le hK hz.1⟩
      · rcases lt_or_ge z 0 with hz0 | hz0
        · exact Or.inl ⟨hz0, K, lt_of_lt_of_le hK hz.1⟩
        · exact Or.inr ⟨hz0, hsRord.out htR hyR ⟨by linarith, by linarith [hz.2]⟩⟩
    · rcases hy with ⟨hy0, -⟩ | ⟨hy0, hyR⟩
      · exact absurd (hz.1.trans hz.2) (by linarith)
      · exact Or.inr ⟨hx0.trans hz.1, hsRord.out hxR hyR ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩
  have hs'o : IsOpen s' := by
    rw [isOpen_iff_mem_nhds]
    intro σ hσ
    rcases hσ with ⟨hσ0, K, hK⟩ | ⟨hσ0, hσR⟩
    · refine mem_of_superset (Ioo_mem_nhds hK hσ0) fun x hx => Or.inl ⟨hx.2, K, hx.1⟩
    · have hcont' : Continuous fun x : ℝ => x + tR := continuous_id.add continuous_const
      have hRn : (fun x : ℝ => x + tR) ⁻¹' sR ∈ 𝓝 σ := hcont'.continuousAt.preimage_mem_nhds
        (hsRo.mem_nhds hσR)
      rcases hσ0.lt_or_eq with hpos | hz
      · refine mem_of_superset (inter_mem hRn (Ioi_mem_nhds hpos)) fun x hx => ?_
        exact Or.inr ⟨hx.2.le, hx.1⟩
      · subst hz
        have hn1 : Ioo (β 1) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (hβneg 0) one_pos
        refine mem_of_superset (inter_mem hRn hn1) fun x hx => ?_
        rcases lt_or_ge x 0 with hx0 | hx0
        · exact Or.inl ⟨hx0, 0, hx.2.1⟩
        · exact Or.inr ⟨hx0, hx.1⟩
  -- the chain part and the future part are timelike curves
  have hchain : ∀ a b : ℝ, a < b → b ≤ 0 → Icc a b ⊆ s' → IsFutureTimelikeCurve T G (Icc a b) := by
    intro a b hab hb0 hsub
    have ha : a ∈ s' := hsub ⟨le_rfl, hab.le⟩
    rcases ha with ⟨ha0, K, hK⟩ | ⟨ha0, -⟩
    · exact (hGt K).restrict T (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) hab
    · exact absurd (ha0.trans_lt hab) (by linarith)
  have hfut : ∀ a b : ℝ, 0 ≤ a → a < b → Icc a b ⊆ s' →
      IsFutureTimelikeCurve T (fun σ => R (σ + tR)) (Icc a b) := by
    intro a b ha0 hab hsub
    have hsubR : Icc (a + tR) (b + tR) ⊆ sR := fun x hx => by
      have : x - tR ∈ s' := hsub ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
      · exfalso
        have : 0 ≤ x - tR := by linarith [hx.1]
        linarith
      · simpa using h2
    have := (hR.1.restrict T hsubR (by linarith)).shift T (by linarith : a + tR < b + tR) tR
    simp only [add_sub_cancel_right] at this
    exact this
  have hFeq0 : ∀ σ : ℝ, 0 ≤ σ → F σ = R (σ + tR) := by
    intro σ hσ
    rcases hσ.lt_or_eq with hpos | hz
    · simp [F, not_le.2 hpos]
    · subst hz
      simp [F, hG0, hRq]
  have hFcurve : IsFutureTimelikeCurve T F s' := by
    refine isFutureTimelikeCurve_of_Icc T hs'o hs'ord fun a b hab hsub => ?_
    by_cases hb0 : b ≤ 0
    · exact (hchain a b hab hb0 hsub).congr_Icc T fun x hx => by
        simp [F, hx.2.trans hb0]
    · push Not at hb0
      by_cases ha0 : 0 ≤ a
      · exact (hfut a b ha0 hab hsub).congr_Icc T fun x hx => hFeq0 x (ha0.trans hx.1)
      · push Not at ha0
        have h1 := hchain a 0 ha0 le_rfl (fun x hx => hsub ⟨hx.1, hx.2.trans hb0.le⟩)
        have h2 := hfut 0 b le_rfl hb0 (fun x hx => hsub ⟨by linarith [hx.1], hx.2⟩)
        have hj : G 0 = (fun σ => R (σ + tR)) 0 := by simp [hG0, hRq]
        exact IsFutureTimelikeCurve.glue T h1 h2 ha0 hb0 hj
  -- `F` lies in `I⁺(S)`
  have hFS : ∀ u ∈ s', F u ∈ chronFutureSet T S := by
    intro u hu
    rcases hu with ⟨hu0, K, hK⟩ | ⟨hu0, huR⟩
    · obtain ⟨x, hx, hqx⟩ := Set.mem_iUnion₂.1 (hqS (K + 1))
      have hlt := mem_chronFuture_of_lt T (hGt K) (u := β (K + 1)) (v := u)
        ⟨le_rfl, (hβneg K).le⟩ ⟨hK.le, hu0.le⟩ hK
      rw [hGβ (K + 1)] at hlt
      have : F u = G u := by simp [F, hu0.le]
      rw [this]
      exact Set.mem_iUnion₂.2 ⟨x, hx, chron_trans T hqx hlt⟩
    · rcases hu0.lt_or_eq with hpos | hz
      · obtain ⟨x, hx, hqx⟩ := Set.mem_iUnion₂.1 (hqS 0)
        have hlt := mem_chronFuture_of_lt T hR.1 htR huR (by linarith : tR < u + tR)
        rw [hRq] at hlt
        rw [hFeq0 u hu0]
        rw [hq0] at hqx
        exact Set.mem_iUnion₂.2 ⟨x, hx, chron_trans T hqx hlt⟩
      · subst hz
        rw [hFeq0 0 le_rfl]
        simp only [zero_add]
        rw [hRq, ← hq0]
        exact hqS 0
  have hmissS : ∀ u ∈ s', F u ∉ S := by
    intro u hu hS
    obtain ⟨x, hx, hFx⟩ := Set.mem_iUnion₂.1 (hFS u hu)
    exact hA x hx (F u) hS hFx
  -- no endpoints
  have hβs' : ∀ k, β k ∈ s' := by
    intro k
    rcases k with _ | j
    · rw [hβ0]; exact h0s'
    · exact Or.inl ⟨hβneg j, j + 1, hβanti (Nat.lt_succ_self _)⟩
  have hFβ : ∀ k, F (β k) = q k := by
    intro k
    have : β k ≤ 0 := by rw [← hβ0]; exact hβanti.antitone (Nat.zero_le k)
    simp [F, this, hGβ k]
  refine ⟨F, s', ⟨hFcurve, ⟨0, h0s'⟩, ?_, ?_⟩, hmissS⟩
  · -- no future endpoint
    intro p hf
    refine hR.2.2.1 p fun U hU => ?_
    obtain ⟨c, hc, hcU⟩ := hf U hU
    have hc0 : max c 0 ∈ s' := by
      rcases le_total c 0 with h | h
      · rw [max_eq_right h]; exact h0s'
      · rw [max_eq_left h]; exact hc
    have hc0R : max c 0 + tR ∈ sR := by
      rcases hc0 with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 (by linarith [le_max_right c 0])
      · exact h2
    refine ⟨max c 0 + tR, hc0R, fun x hx hle => ?_⟩
    have hxs' : x - tR ∈ s' := Or.inr ⟨by linarith [le_max_right c 0], by simpa using hx⟩
    have := hcU (x - tR) hxs' (by linarith [le_max_left c 0])
    rw [hFeq0 (x - tR) (by linarith [le_max_right c 0])] at this
    simpa using this
  · -- no past endpoint
    intro p hp'
    have htend : Tendsto q atTop (𝓝 p) := by
      refine tendsto_nhds.2 fun U hU hUp => ?_
      obtain ⟨c, hc, hcU⟩ := hp' U (hU.mem_nhds hUp)
      obtain ⟨K₁, hK₁⟩ : ∃ K₁, β K₁ ≤ c := by
        rcases hc with ⟨hc0, K, hK⟩ | ⟨hc0, -⟩
        · exact ⟨K + 1, hK.le⟩
        · exact ⟨0, by rw [hβ0]; exact hc0⟩
      filter_upwards [eventually_ge_atTop K₁] with k hk
      show q k ∈ U
      rw [← hFβ k]
      exact hcU (β k) (hβs' k) ((hβanti.antitone hk).trans hK₁)
    have hend := hqend p htend
    refine hnp p fun N hN => ?_
    obtain ⟨c, hc, hcN⟩ := hend N hN
    exact ⟨c, hc.1, fun x hx hxc => hcN x ⟨hx, hxc.trans hc.2⟩ hxc⟩

end Main

end Lightlike.Causal
