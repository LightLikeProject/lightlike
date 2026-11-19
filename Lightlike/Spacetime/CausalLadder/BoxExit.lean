import Lightlike.Spacetime.CausalLadder.FirstExit
import Lightlike.Spacetime.CausalLadder.CurveContinuity
import Lightlike.Spacetime.CausalLadder.ChartLipschitz
import Lightlike.Spacetime.CausalLadder.ConeCurve
import Lightlike.Spacetime.Causal.CurveOps

/-!
# A future-inextendible causal curve leaves every chart box

Step of the proof of the limit-curve theorem (task `T-GE2-P20`, Hawking–Ellis Lemma 6.2.1): with the cone estimate of a
chart box (`ConeBox`), a future causal curve whose chart images stay in a closed ball for all large parameters has a future
endpoint (the time functional increases and is bounded, the chart images are Cauchy by the cone estimate, hence converge),
so a future-inextendible curve starting inside the open ball reaches the sphere: there is a first exit time
(`exists_exit_of_not_tendsto`).

Supporting lemma for the limit-curve theorem; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology MeasureTheory Metric
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- The hypotheses of a chart box: the cone estimate of `exists_cone_estimate_curve`, for curves with values in `W`. -/
def ConeBox (p : M) (W : Set M) (ℓ : E →L[ℝ] ℝ) (C : ℝ) : Prop :=
  ∀ (γ : ℝ → M) (a b : ℝ), IsFutureCausalCurve T γ (Icc a b) → (∀ t ∈ Icc a b, γ t ∈ W) →
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      ℓ (extChartAt I p (γ s)) ≤ ℓ (extChartAt I p (γ t)) ∧
      ‖extChartAt I p (γ t) - extChartAt I p (γ s)‖ ≤
        C * (ℓ (extChartAt I p (γ t)) - ℓ (extChartAt I p (γ s)))

/-- **A curve that stays in a closed chart box has an endpoint**, for the future end: if a future causal curve on `s`
has chart images in the closed ball of radius `r` around `c` from the parameter `t₀` on, and the ball is in the target of
the chart with its preimage in `W`, then `γ t` converges as `t` tends to the top of `s`. -/
theorem tendsto_of_stays_in_box [FiniteDimensional ℝ E] [T2Space M] (p : M) {W : Set M} {ℓ : E →L[ℝ] ℝ} {C : ℝ}
    (hC : 0 < C) (hbox : ConeBox T p W ℓ C) {c : E} {r : ℝ}
    (hr : ∀ y ∈ closedBall c r, y ∈ (extChartAt I p).target ∧ (extChartAt I p).symm y ∈ W)
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsFutureCausalCurve T γ s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hin : ∀ t ∈ s, t₀ ≤ t → γ t ∈ (extChartAt I p).source ∧ extChartAt I p (γ t) ∈ closedBall c r) :
    ∃ y : M, Tendsto (fun t : s => γ t) atTop (𝓝 y) := by
  classical
  have hs_nonempty : Nonempty s := ⟨⟨t₀, ht₀⟩⟩
  set φ := extChartAt I p with hφ
  -- the monotone estimate along sub-arcs after `t₀`
  have hW : ∀ t ∈ s, t₀ ≤ t → γ t ∈ W := fun t ht ht0 => by
    obtain ⟨hsrc, hb⟩ := hin t ht ht0
    have := (hr _ hb).2
    rwa [φ.left_inv hsrc] at this
  have hest : ∀ a ∈ s, ∀ b ∈ s, t₀ ≤ a → a ≤ b →
      ℓ (φ (γ a)) ≤ ℓ (φ (γ b)) ∧ ‖φ (γ b) - φ (γ a)‖ ≤ C * (ℓ (φ (γ b)) - ℓ (φ (γ a))) := by
    intro a ha b hb hta hab
    rcases hab.eq_or_lt with rfl | hlt
    · simp
    · have hsub : Icc a b ⊆ s := fun u hu => hγ.ordConnected.out ha hb hu
      have hcur : IsFutureCausalCurve T γ (Icc a b) := IsCurveWith.restrict hγ hsub hlt
      exact hbox γ a b hcur (fun u hu => hW u (hsub hu) (hta.trans hu.1)) a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  -- the functional along the curve converges
  let t₀' : s := ⟨t₀, ht₀⟩
  let G : s → E := fun t => φ (γ ((max t t₀' : s) : ℝ))
  have hGmem : ∀ t : s, G t ∈ closedBall c r := fun t => by
    have ht : t₀ ≤ ((max t t₀' : s) : ℝ) := (le_max_right t t₀' : t₀' ≤ max t t₀')
    exact (hin _ (max t t₀' : s).2 ht).2
  let F : s → ℝ := fun t => ℓ (G t)
  have hFmono : Monotone F := by
    intro a b hab
    exact (hest _ (max a t₀' : s).2 _ (max b t₀' : s).2 (le_max_right a t₀' : t₀' ≤ max a t₀')
      (max_le_max hab le_rfl : max a t₀' ≤ max b t₀')).1
  have hFbdd : BddAbove (range F) := by
    refine ⟨‖ℓ‖ * (‖c‖ + r), ?_⟩
    rintro _ ⟨t, rfl⟩
    have h1 := hGmem t
    have h2 : ‖G t‖ ≤ ‖c‖ + r := by
      have := norm_le_norm_add_norm_sub' (G t) c
      rw [mem_closedBall, dist_eq_norm] at h1
      linarith
    calc F t ≤ ‖ℓ (G t)‖ := Real.le_norm_self _
      _ ≤ ‖ℓ‖ * ‖G t‖ := ℓ.le_opNorm _
      _ ≤ ‖ℓ‖ * (‖c‖ + r) := by gcongr
  have hFlim : Tendsto F atTop (𝓝 (⨆ t, F t)) := tendsto_atTop_ciSup hFmono hFbdd
  -- the chart images are Cauchy
  have hGc : Cauchy (map G atTop) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨a, ha⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 hFlim (ε / (2 * C)) (by positivity))
    refine ⟨G '' Ici a, image_mem_map (Ici_mem_atTop a), ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have key : ∀ x y : s, a ≤ x → x ≤ y → ‖G y - G x‖ ≤ C * (F y - F x) := fun x y hax hxy =>
      (hest _ (max x t₀' : s).2 _ (max y t₀' : s).2 (le_max_right x t₀' : t₀' ≤ max x t₀')
        (max_le_max hxy le_rfl : max x t₀' ≤ max y t₀')).2
    have hxa := ha x hx
    have hya := ha y hy
    rw [Real.dist_eq] at hxa hya
    rw [dist_eq_norm]
    rcases le_total x y with hxy | hxy
    · have := key x y hx hxy
      rw [norm_sub_rev]
      have h3 : F y - F x < ε / C := by
        have := abs_lt.1 hxa; have := abs_lt.1 hya
        have : ε / C = 2 * (ε / (2 * C)) := by field_simp
        linarith
      calc ‖G y - G x‖ ≤ C * (F y - F x) := key x y hx hxy
        _ < C * (ε / C) := by gcongr
        _ = ε := by field_simp
    · have h3 : F x - F y < ε / C := by
        have := abs_lt.1 hxa; have := abs_lt.1 hya
        have : ε / C = 2 * (ε / (2 * C)) := by field_simp
        linarith
      calc ‖G x - G y‖ ≤ C * (F x - F y) := key y x hy hxy
        _ < C * (ε / C) := by gcongr
        _ = ε := by field_simp
  obtain ⟨yE, hyE⟩ := cauchy_map_iff_exists_tendsto.1 hGc
  have hyEmem : yE ∈ closedBall c r :=
    isClosed_closedBall.mem_of_tendsto hyE (Eventually.of_forall hGmem)
  refine ⟨φ.symm yE, ?_⟩
  have hcont : ContinuousAt φ.symm yE := continuousAt_extChartAt_symm'' (hr _ hyEmem).1
  have h1 : Tendsto (fun t : s => φ.symm (G t)) atTop (𝓝 (φ.symm yE)) := hcont.tendsto.comp hyE
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop t₀'] with t ht
  have hmax : max t t₀' = t := max_eq_left ht
  show φ.symm (φ (γ ((max t t₀' : s) : ℝ))) = γ t
  rw [hmax]
  exact φ.left_inv (hin t t.2 ht).1


/-- **A future-inextendible causal curve leaves every chart box**: if `γ` on `s` is a future causal curve without future
endpoint, and `γ t₀` is in the open ball of radius `r` around `c` in the chart, there is a first `t₁ ≥ t₀` where the chart image
reaches the sphere of radius `r`, the curve staying in the closed ball between `t₀` and `t₁`. -/
theorem exists_exit_of_not_tendsto [FiniteDimensional ℝ E] [T2Space M] (p : M) {W : Set M} {ℓ : E →L[ℝ] ℝ} {C : ℝ}
    (hC : 0 < C) (hbox : ConeBox T p W ℓ C) {c : E} {r : ℝ}
    (hr : ∀ y ∈ closedBall c r, y ∈ (extChartAt I p).target ∧ (extChartAt I p).symm y ∈ W)
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsFutureCausalCurve T γ s)
    (hne : ∀ y : M, ¬ Tendsto (fun t : s => γ t) atTop (𝓝 y)) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hs₀ : γ t₀ ∈ (extChartAt I p).source) (hin₀ : extChartAt I p (γ t₀) ∈ ball c r) :
    ∃ t₁ ∈ s, t₀ ≤ t₁ ∧ (∀ u ∈ Icc t₀ t₁, γ u ∈ (extChartAt I p).source ∧ extChartAt I p (γ u) ∈ closedBall c r) ∧
      ‖extChartAt I p (γ t₁) - c‖ = r := by
  classical
  set φ := extChartAt I p with hφ
  set O : Set M := φ.source ∩ φ ⁻¹' ball c r with hO
  have hOopen : IsOpen O := by
    rw [hO, hφ, extChartAt_source]
    exact isOpen_extChartAt_preimage (I := I) p isOpen_ball
  have hγ0 : γ t₀ ∈ O := ⟨hs₀, hin₀⟩
  have hcont : ContinuousOn γ s := hγ.lipschitz.continuousOn
  have hOsub : O ⊆ φ.symm '' closedBall c r := by
    rintro x ⟨hxs, hxb⟩
    exact ⟨φ x, ball_subset_closedBall hxb, φ.left_inv hxs⟩
  have hcomp : IsCompact (φ.symm '' closedBall c r) := by
    refine (isCompact_closedBall c r).image_of_continuousOn ?_
    exact (continuousOn_extChartAt_symm p).mono fun y hy => (hr y hy).1
  have hclosure : closure O ⊆ φ.symm '' closedBall c r := closure_minimal hOsub hcomp.isClosed
  by_cases hex : ∃ t' ∈ s, t₀ ≤ t' ∧ γ t' ∉ O
  · obtain ⟨t', ht's, ht'0, ht'O⟩ := hex
    have hsub : Icc t₀ t' ⊆ s := fun u hu => hγ.ordConnected.out ht₀ ht's hu
    obtain ⟨t₁, ht₁, ht₁O, hbefore, hcl⟩ := exists_first_exit (hcont.mono hsub) hOopen hγ0
      ⟨t', ⟨ht'0, le_rfl⟩, ht'O⟩
    have ht₁s : t₁ ∈ s := hsub ⟨ht₁.1.le, ht₁.2⟩
    obtain ⟨y, hy, hyeq⟩ := hclosure hcl
    have hytarget := (hr y hy).1
    have hγt₁ : φ (γ t₁) = y := by rw [← hyeq]; exact φ.right_inv hytarget
    have hγs : γ t₁ ∈ φ.source := by rw [← hyeq]; exact φ.map_target hytarget
    have hle : ‖φ (γ t₁) - c‖ ≤ r := by rw [hγt₁]; exact mem_closedBall_iff_norm.1 hy
    have hge : r ≤ ‖φ (γ t₁) - c‖ := by
      by_contra hlt
      exact ht₁O ⟨hγs, by rw [mem_preimage, mem_ball_iff_norm]; exact not_le.1 hlt⟩
    refine ⟨t₁, ht₁s, ht₁.1.le, fun u hu => ?_, le_antisymm hle hge⟩
    rcases hu.2.eq_or_lt with rfl | hlt
    · exact ⟨hγs, mem_closedBall_iff_norm.2 hle⟩
    · have := hbefore u ⟨hu.1, hlt⟩
      exact ⟨this.1, ball_subset_closedBall this.2⟩
  · push_neg at hex
    exfalso
    obtain ⟨y, hy⟩ := tendsto_of_stays_in_box T p hC hbox hr hγ ht₀ (fun t ht ht0 => by
      have := hex t ht ht0
      exact ⟨this.1, ball_subset_closedBall this.2⟩)
    exact hne y hy

end Lightlike.Causal
