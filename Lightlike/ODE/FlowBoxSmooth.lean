import Lightlike.ODE.FlowContDiff

/-!
# Every flow box of a `C^k` field has a `C^k` flow

`Lightlike.ODE.exists_isFlowBox_contDiffOn` produces one flow box with a `C^k` flow. Here the
same regularity is shown for an arbitrary flow box of a `C^k` field, on its whole domain
`(-T, T) × B(x₀, r)` (`Lightlike.ODE.IsFlowBox.contDiffOn_uncurry`), and hence `C^∞` regularity
for a smooth field (`IsFlowBox.contDiffOn_uncurry_infty`).

The proof is a continuation in the time. Near a point `Φ t₁ x` of a trajectory there is a small
flow box with a `C^k` flow `Ψ`, and `Φ (s, x') = Ψ (s - t', Φ (t', x'))` for `s`, `t'` near `t₁`
by uniqueness of solutions; so regularity at one time near `t₁` gives regularity at all times near
`t₁`. The set of times of regularity is therefore open with open complement in the interval.

## References

* `teschl-2012`: G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, Theorem 2.10,
  page 46 of the author's version (regularity on a neighbourhood; the continuation is the usual
  argument for extending it along a solution).
-/

open Set Metric Filter Topology
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.ODE

namespace IsFlowBox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {V : E → E} {x₀ : E} {a r T : ℝ} {K : ℝ≥0} {Φ : ℝ → E → E}

/-- The local step of the continuation: near a time `t₁`, regularity of `x' ↦ Φ t' x'` at `x`
for one time `t'` gives regularity of `(t, x') ↦ Φ t x'` at `(t, x)` for all times `t`. -/
theorem exists_step (h : IsFlowBox V x₀ a r T K Φ) (k : ℕ)
    (hV : ContDiffOn ℝ ((k : ℕ∞ω) + 1) V (ball x₀ a)) {x : E} (hx : x ∈ ball x₀ r) {t₁ : ℝ}
    (ht₁ : t₁ ∈ Ioo (-T) T) :
    ∃ ε > 0, ∀ t' ∈ Ioo (-T) T, |t' - t₁| < ε → ContDiffAt ℝ ((k : ℕ∞ω) + 1) (Φ t') x →
      ∀ t ∈ Ioo (-T) T, |t - t₁| < ε →
        ContDiffAt ℝ ((k : ℕ∞ω) + 1) (fun p : ℝ × E => Φ p.1 p.2) (t, x) := by
  have ht₁' : t₁ ∈ Icc (-T) T := Ioo_subset_Icc_self ht₁
  set y : E := Φ t₁ x with hy
  have hya : y ∈ ball x₀ a := h.flow_mem x hx t₁ ht₁'
  have hVy : ContDiffAt ℝ ((k : ℕ∞ω) + 1) V y := hV.contDiffAt (isOpen_ball.mem_nhds hya)
  obtain ⟨a', r₀, T', K', Ψ, hΨ₀, -, hΨc₀⟩ := exists_isFlowBox_contDiffOn k hVy
  have ha'0 : 0 < a' := lt_of_le_of_lt dist_nonneg
    (mem_ball.1 (hΨ₀.initial_mem (mem_ball_self hΨ₀.r_pos)))
  set r' : ℝ := min r₀ a' with hr'
  have hr'a' : r' ≤ a' := min_le_right _ _
  have hΨ : IsFlowBox V y a' r' T' K' Ψ :=
    hΨ₀.mono (lt_min hΨ₀.r_pos ha'0) (min_le_left _ _) hΨ₀.T_pos le_rfl
  have hΨc : ContDiffOn ℝ ((k : ℕ∞ω) + 1) (fun p : ℝ × E => Ψ p.1 p.2)
      (Ioo (-T') T' ×ˢ ball y r') :=
    hΨc₀.mono (prod_mono subset_rfl (ball_subset_ball (min_le_left _ _)))
  set M : ℝ := ‖V x₀‖ + K * a with hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (h.norm_field_le (h.initial_mem hx))
  have hM1 : 0 < 2 * (M + 1) := by linarith
  set d : ℝ := min (T - t₁) (t₁ + T) with hd
  have hd0 : 0 < d := lt_min (by linarith [ht₁.2]) (by linarith [ht₁.1])
  set τ : ℝ := min (min T' (r' / (2 * (M + 1)))) (d / 2) with hτ
  have hτ0 : 0 < τ := lt_min (lt_min hΨ.T_pos (div_pos hΨ.r_pos hM1)) (half_pos hd0)
  have hτT' : τ ≤ T' := (min_le_left _ _).trans (min_le_left _ _)
  have hτd : τ ≤ d / 2 := min_le_right _ _
  have hMτ : M * τ ≤ r' / 2 := by
    have h1 : M * τ ≤ M * (r' / (2 * (M + 1))) :=
      mul_le_mul_of_nonneg_left ((min_le_left _ _).trans (min_le_right _ _)) hM0
    have h2 : M * (r' / (2 * (M + 1))) ≤ r' / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ hM1]
      nlinarith [hΨ.r_pos]
    linarith
  have hΨ' : IsFlowBox V y a' r' τ K' Ψ := hΨ.mono hΨ.r_pos le_rfl hτ0 hτT'
  refine ⟨τ / 2, half_pos hτ0, fun t' ht' htt' hQ t ht htt => ?_⟩
  have ht'I : t' ∈ Icc (-T) T := Ioo_subset_Icc_self ht'
  have habs' := abs_lt.1 htt'
  have habs := abs_lt.1 htt
  have hdT : d ≤ T - t₁ := min_le_left _ _
  have hdT' : d ≤ t₁ + T := min_le_right _ _
  -- times `t' + u` with `|u| ≤ τ` stay in `[-T, T]`
  have hshift : ∀ u ∈ Icc (-τ) τ, t' + u ∈ Icc (-T) T := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  -- the identity `Φ (t' + u) x' = Ψ u (Φ t' x')`
  have hid : ∀ x' ∈ ball x₀ r, Φ t' x' ∈ ball y (r' / 2) → ∀ u ∈ Icc (-τ) τ,
      Φ (t' + u) x' = Ψ u (Φ t' x') := by
    intro x' hx' hmem u hu
    have hmem' : Φ t' x' ∈ ball y r' := ball_subset_ball (by linarith [hΨ.r_pos]) hmem
    have hc : ∀ v ∈ Icc (-τ) τ, HasDerivWithinAt (fun v => Φ (t' + v) x')
        (V (Φ (t' + v) x')) (Icc (-τ) τ) v := by
      intro v hv
      have h1 := (h.hasDerivAt x' hx' (t' + v) (hshift v hv)).scomp v
        ((hasDerivAt_id v).const_add t')
      have h2 : HasDerivAt (fun v => Φ (t' + v) x') (V (Φ (t' + v) x')) v := by
        simpa [Function.comp_def] using h1
      exact h2.hasDerivWithinAt
    have hcs : ∀ v ∈ Icc (-τ) τ, Φ (t' + v) x' ∈ ball y a' := by
      intro v hv
      have h1 : ‖Φ (t' + v) x' - Φ t' x'‖ ≤ M * |t' + v - t'| :=
        h.norm_flow_sub_time_le hx' ht'I (hshift v hv)
      have h2 : |t' + v - t'| ≤ τ := by
        rw [add_sub_cancel_left]; exact abs_le.2 hv
      have h3 : M * |t' + v - t'| ≤ r' / 2 :=
        (mul_le_mul_of_nonneg_left h2 hM0).trans hMτ
      rw [mem_ball]
      calc dist (Φ (t' + v) x') y ≤ dist (Φ (t' + v) x') (Φ t' x') + dist (Φ t' x') y :=
            dist_triangle _ _ _
        _ < r' / 2 + r' / 2 := by
            rw [dist_eq_norm]
            exact add_lt_add_of_le_of_lt (h1.trans h3) (mem_ball.1 hmem)
        _ = r' := add_halves r'
        _ ≤ a' := hr'a'
    have h0 : (fun v => Φ (t' + v) x') 0 = (fun v => Ψ v (Φ t' x')) 0 := by
      simp only [add_zero, hΨ'.flow_zero _ hmem']
    exact eqOn_of_trajectories hΨ'.lipschitzOnWith hc hcs (hΨ'.hasDerivWithinAt hmem')
      (hΨ'.flow_mem _ hmem') h0 hu
  -- `Φ t' x` is close to `y`
  have hyt' : Φ t' x ∈ ball y (r' / 2) := by
    rw [mem_ball, dist_eq_norm]
    have h1 : ‖Φ t' x - Φ t₁ x‖ ≤ M * |t' - t₁| := h.norm_flow_sub_time_le hx ht₁' ht'I
    have h2 : M * |t' - t₁| ≤ M * (τ / 2) := mul_le_mul_of_nonneg_left htt'.le hM0
    have h3 : M * (τ / 2) < r' / 2 := by nlinarith [hΨ.r_pos]
    exact lt_of_le_of_lt (h1.trans h2) h3
  have hcontx : ContinuousAt (Φ t') x := hQ.continuousAt
  -- near `(t, x)` the flow is `Ψ (s - t') (Φ t' x')`
  have hev : (fun p : ℝ × E => Φ p.1 p.2) =ᶠ[𝓝 (t, x)]
      fun p : ℝ × E => Ψ (p.1 - t') (Φ t' p.2) := by
    have hτtt : |t - t'| < τ := by
      rw [abs_lt]; constructor <;> linarith [habs.1, habs.2, habs'.1, habs'.2]
    have h1 : ∀ᶠ p : ℝ × E in 𝓝 (t, x), |p.1 - t'| < τ :=
      ((continuous_fst.sub continuous_const).abs.continuousAt.eventually
        (Iio_mem_nhds hτtt) : ∀ᶠ p : ℝ × E in 𝓝 (t, x), |p.1 - t'| ∈ Iio τ)
    have h2 : ∀ᶠ p : ℝ × E in 𝓝 (t, x), p.2 ∈ ball x₀ r :=
      continuous_snd.continuousAt.eventually (isOpen_ball.mem_nhds hx)
    have h3 : ∀ᶠ p : ℝ × E in 𝓝 (t, x), Φ t' p.2 ∈ ball y (r' / 2) :=
      (hcontx.comp continuous_snd.continuousAt :
        ContinuousAt (fun p : ℝ × E => Φ t' p.2) (t, x)).eventually
        (isOpen_ball.mem_nhds hyt')
    filter_upwards [h1, h2, h3] with p hp1 hp2 hp3
    have := hid p.2 hp2 hp3 (p.1 - t') (abs_le.1 hp1.le)
    simpa using this
  have hinner : ContDiffAt ℝ ((k : ℕ∞ω) + 1) (fun p : ℝ × E => (p.1 - t', Φ t' p.2)) (t, x) :=
    (contDiffAt_fst.sub contDiffAt_const).prodMk (hQ.comp (t, x) contDiffAt_snd)
  have hmemΨ : ((t - t', Φ t' x) : ℝ × E) ∈ Ioo (-T') T' ×ˢ ball y r' := by
    refine ⟨?_, ball_subset_ball (by linarith [hΨ.r_pos]) hyt'⟩
    constructor <;> linarith [habs.1, habs.2, habs'.1, habs'.2]
  have hΨat : ContDiffAt ℝ ((k : ℕ∞ω) + 1) (fun q : ℝ × E => Ψ q.1 q.2) (t - t', Φ t' x) :=
    hΨc.contDiffAt ((isOpen_Ioo.prod isOpen_ball).mem_nhds hmemΨ)
  have hcomp : ContDiffAt ℝ ((k : ℕ∞ω) + 1)
      (fun p : ℝ × E => Ψ (p.1 - t') (Φ t' p.2)) (t, x) :=
    ContDiffAt.comp (g := fun q : ℝ × E => Ψ q.1 q.2) (t, x) hΨat hinner
  exact hcomp.congr_of_eventuallyEq hev

/-- **Every flow box of a `C^{k+1}` field has a `C^{k+1}` flow**, on all of
`(-T, T) × B(x₀, r)`. -/
theorem contDiffOn_uncurry (h : IsFlowBox V x₀ a r T K Φ) (k : ℕ)
    (hV : ContDiffOn ℝ ((k : ℕ∞ω) + 1) V (ball x₀ a)) :
    ContDiffOn ℝ ((k : ℕ∞ω) + 1) (fun p : ℝ × E => Φ p.1 p.2) (Ioo (-T) T ×ˢ ball x₀ r) := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  refine ContDiffAt.contDiffWithinAt ?_
  have hne : ((k : ℕ∞ω) + 1) ≠ ∞ := by
    have hc : ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 := by push_cast; rfl
    rw [← hc]
    intro hh
    have h2 : (((k + 1 : ℕ) : ℕ∞) : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) := hh
    exact ENat.natCast_ne_top (k + 1) (WithTop.coe_injective h2)
  set P : ℝ → Prop := fun s =>
    ContDiffAt ℝ ((k : ℕ∞ω) + 1) (fun p : ℝ × E => Φ p.1 p.2) (s, x) with hP
  have hQ : ∀ s, P s → ContDiffAt ℝ ((k : ℕ∞ω) + 1) (Φ s) x := fun s hs =>
    ContDiffAt.comp (g := fun p : ℝ × E => Φ p.1 p.2) (f := fun x' : E => (s, x')) x hs
      (contDiffAt_const.prodMk contDiffAt_id)
  have hQ0 : ContDiffAt ℝ ((k : ℕ∞ω) + 1) (Φ 0) x := by
    have hev : Φ 0 =ᶠ[𝓝 x] id := by
      filter_upwards [isOpen_ball.mem_nhds hx] with x' hx' using h.flow_zero x' hx'
    exact contDiffAt_id.congr_of_eventuallyEq hev
  have h0 : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith [h.T_pos], h.T_pos⟩
  choose ε hε hstep using fun t₁ : Ioo (-T) T => h.exists_step k hV hx t₁.2
  have hP0 : P 0 := hstep ⟨0, h0⟩ 0 h0 (by simpa using hε ⟨0, h0⟩) hQ0 0 h0
    (by simpa using hε ⟨0, h0⟩)
  by_contra hnot
  set u : Set ℝ := {s | P s} with hu
  set v : Set ℝ := ⋃ (t₁ : Ioo (-T) T) (_ : ¬ P t₁), ball (t₁ : ℝ) (ε t₁) with hv
  have huo : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have h1 : ∀ᶠ q in 𝓝 (s, x), ContDiffAt ℝ ((k : ℕ∞ω) + 1)
        (fun p : ℝ × E => Φ p.1 p.2) q := ContDiffAt.eventually hs hne
    have h2 : Tendsto (fun s' : ℝ => (s', x)) (𝓝 s) (𝓝 (s, x)) :=
      (continuous_id.prodMk continuous_const).tendsto s
    exact h2.eventually h1
  have hvo : IsOpen v := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  have hcover : Ioo (-T) T ⊆ u ∪ v := by
    intro s hs
    by_cases hPs : P s
    · exact Or.inl hPs
    · exact Or.inr (mem_iUnion₂.2 ⟨⟨s, hs⟩, hPs, mem_ball_self (hε ⟨s, hs⟩)⟩)
  obtain ⟨s, hs, hsu, hsv⟩ := isPreconnected_Ioo u v huo hvo hcover ⟨0, h0, hP0⟩
    ⟨t, ht, mem_iUnion₂.2 ⟨⟨t, ht⟩, hnot, mem_ball_self (hε ⟨t, ht⟩)⟩⟩
  obtain ⟨t₁, hnP, hball⟩ := mem_iUnion₂.1 hsv
  rw [mem_ball, Real.dist_eq] at hball
  exact hnP (hstep t₁ s hs hball (hQ s hsu) t₁ t₁.2 (by simpa using hε t₁))

/-- **Every flow box of a smooth field has a smooth flow**, on all of `(-T, T) × B(x₀, r)`. -/
theorem contDiffOn_uncurry_infty (h : IsFlowBox V x₀ a r T K Φ)
    (hV : ContDiffOn ℝ ∞ V (ball x₀ a)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) (Ioo (-T) T ×ˢ ball x₀ r) := by
  refine contDiffOn_infty.2 fun n => ?_
  have hc : ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 := by push_cast; rfl
  have hVn : ContDiffOn ℝ ((n : ℕ∞ω) + 1) V (ball x₀ a) := by
    rw [← hc]; exact contDiffOn_infty.1 hV (n + 1)
  exact (h.contDiffOn_uncurry n hVn).of_le le_self_add

end IsFlowBox

end Lightlike.ODE
