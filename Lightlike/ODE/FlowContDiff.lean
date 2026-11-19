import Lightlike.ODE.FlowJoint
import Lightlike.ODE.LocalFlow
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The solution of a `C^k` equation is `C^k` in time, initial time and initial point

Teschl's Theorem 2.10: for `f` of class `C^k`, `k ≥ 1`, the solution `φ (t, s, x)` of
`ẋ = f (t, x)`, `x (s) = x`, is `C^k` in `(t, s, x)` near each point, and so is its time
derivative.

## Main results

* `Lightlike.ODE.IsFlowBox.contDiffOn_one_uncurry`: in a flow box the flow is `C¹` in `(t, x)`.
* `Lightlike.ODE.IsFlowBox.contDiffOn_succ_uncurry`: one more order of smoothness for the flow
  from `V`, `Φ` and `D_x Φ`.
* `Lightlike.ODE.exists_isFlowBox_contDiffOn`: an autonomous field that is `C^{k+1}` at a point
  has a flow box there with a `C^{k+1}` flow. The induction is the source's: `(Φ, D_x Φ)` is the
  flow of the prolonged field `(x, U) ↦ (V x, DV(x) ∘ U)` (`prolong`), which is `C^k`.
* `Lightlike.ODE.exists_solution_contDiffOn`: the theorem for a time-dependent `f`, with the
  initial time, by adding the time to the dependent variables.

## References

* `teschl-2012`: G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, Theorem 2.10
  and its proof, pages 46–47 of the author's version. Differences from the source: a real Banach
  space instead of `ℝⁿ`; `f` is assumed `C^k` at the point `(t₀, x₀)` (hence near it) instead of
  on an open set `U`. The last sentence of the theorem (the higher order variational
  equations) is `Lightlike.ODE.exists_solution_contDiffOn_variational` in
  `Lightlike.ODE.HigherVariational`.
-/

open Set Metric Filter Topology
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.ODE

namespace IsFlowBox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {V : E → E} {x₀ : E} {a r T : ℝ} {K : ℝ≥0} {Φ : ℝ → E → E}

/-- **One more order of smoothness for the flow.** In a flow box, if `V`, the flow
`(t, x) ↦ Φ t x` and its derivative in the initial point `(t, x) ↦ D_x Φ_t` are `C^n`, then the
flow is `C^{n+1}` on `(-T, T) × B(x₀, r)`. -/
theorem contDiffOn_succ_uncurry (h : IsFlowBox V x₀ a r T K Φ) {n : ℕ∞ω} (hn : n ≠ ω)
    (hV : ContDiffOn ℝ n V (ball x₀ a))
    (hΦ : ContDiffOn ℝ n (fun p : ℝ × E => Φ p.1 p.2) (Ioo (-T) T ×ˢ ball x₀ r))
    (hD : ContDiffOn ℝ n (fun p : ℝ × E => fderiv ℝ (Φ p.1) p.2) (Ioo (-T) T ×ˢ ball x₀ r)) :
    ContDiffOn ℝ (n + 1) (fun p : ℝ × E => Φ p.1 p.2) (Ioo (-T) T ×ˢ ball x₀ r) := by
  rw [contDiffOn_succ_iff_fderiv_of_isOpen (isOpen_Ioo.prod isOpen_ball)]
  refine ⟨fun p hp => (h.hasFDerivAt_uncurry hp.2 hp.1).differentiableAt.differentiableWithinAt,
    fun hn' => absurd hn' hn, ?_⟩
  have hmaps : MapsTo (fun p : ℝ × E => Φ p.1 p.2) (Ioo (-T) T ×ˢ ball x₀ r) (ball x₀ a) :=
    fun p hp => h.flow_mem p.2 hp.2 p.1 (Ioo_subset_Icc_self hp.1)
  have h1 : ContDiffOn ℝ n (fun p : ℝ × E =>
      (ContinuousLinearMap.fst ℝ ℝ E).smulRight (V (Φ p.1 p.2)) +
        (fderiv ℝ (Φ p.1) p.2).comp (ContinuousLinearMap.snd ℝ ℝ E))
      (Ioo (-T) T ×ˢ ball x₀ r) :=
    (contDiffOn_const.smulRight (hV.comp hΦ hmaps)).add (hD.clm_comp contDiffOn_const)
  exact h1.congr fun p hp => (h.hasFDerivAt_uncurry hp.2 hp.1).fderiv

/-- **In a flow box the flow is `C¹` in `(t, x)`** on `(-T, T) × B(x₀, r)` (Teschl, Theorem 2.10,
`k = 1`, for an autonomous field). -/
theorem contDiffOn_one_uncurry (h : IsFlowBox V x₀ a r T K Φ) :
    ContDiffOn ℝ 1 (fun p : ℝ × E => Φ p.1 p.2) (Ioo (-T) T ×ˢ ball x₀ r) := by
  have hV : ContDiffOn ℝ 0 V (ball x₀ a) :=
    contDiffOn_zero.2 fun y hy => (h.differentiableAt y hy).continuousAt.continuousWithinAt
  have hΦ : ContDiffOn ℝ 0 (fun p : ℝ × E => Φ p.1 p.2) (Ioo (-T) T ×ˢ ball x₀ r) :=
    contDiffOn_zero.2 fun p hp =>
      (h.hasFDerivAt_uncurry hp.2 hp.1).continuousAt.continuousWithinAt
  have hD : ContDiffOn ℝ 0 (fun p : ℝ × E => fderiv ℝ (Φ p.1) p.2)
      (Ioo (-T) T ×ˢ ball x₀ r) :=
    contDiffOn_zero.2 (h.continuousOn_fderiv_flow.mono (prod_mono Ioo_subset_Icc_self subset_rfl))
  have := h.contDiffOn_succ_uncurry (n := 0) (by simp) hV hΦ hD
  simpa using this

/-- In a flow box the derivative of the flow in the initial point stays within
`K e^{K T} |t|` of the identity. -/
theorem norm_fderiv_flow_sub_id_le (h : IsFlowBox V x₀ a r T K Φ) {x : E} (hx : x ∈ ball x₀ r)
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    ‖fderiv ℝ (Φ t) x - ContinuousLinearMap.id ℝ E‖ ≤ K * Real.exp (K * T) * |t| := by
  have hb : ∀ u ∈ Icc (-T) T,
      ‖(fderiv ℝ V (Φ u x)).comp (fderiv ℝ (Φ u) x)‖ ≤ K * Real.exp (K * T) := fun u hu =>
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (h.norm_fderiv_le _ (h.flow_mem x hx u hu)) (h.norm_fderiv_flow_le hx hu)
        (norm_nonneg _) K.2)
  have := (convex_Icc (-T) T).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => fderiv ℝ (Φ t) x)
    (f' := fun t => (fderiv ℝ V (Φ t x)).comp (fderiv ℝ (Φ t) x))
    (fun u hu => h.hasDerivWithinAt_fderiv_flow hx hu) hb h.zero_mem ht
  simpa [h.fderiv_flow_zero hx, Real.norm_eq_abs] using this

end IsFlowBox

/-- The first-order prolongation of a vector field `V` on `E` to `E × (E →L[ℝ] E)`:
`(x, U) ↦ (V x, DV(x) ∘ U)`. Its integral curves are the pairs of an integral curve of `V` and a
solution of the variational equation along it. -/
def prolong {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : E → E)
    (p : E × (E →L[ℝ] E)) : E × (E →L[ℝ] E) :=
  (V p.1, (fderiv ℝ V p.1).comp p.2)

/-- **The local flow of a `C^k` field is `C^k` in time and initial point** (Teschl, Theorem 2.10,
for an autonomous field): a vector field that is `C^{k+1}` at `x₀` (`k` a natural number) has a
flow box about `x₀` whose flow `(t, x) ↦ Φ t x` is `C^{k+1}` on `(-T, T) × B(x₀, r)`.

The proof is the induction of the source: the pair `(Φ, D_x Φ)` is the flow of the prolonged
field `prolong V`, which is `C^k`. -/
theorem exists_isFlowBox_contDiffOn.{u} (k : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {V : E → E}
      {x₀ : E}, ContDiffAt ℝ ((k : ℕ∞ω) + 1) V x₀ →
      ∃ (a r T : ℝ) (K : ℝ≥0) (Φ : ℝ → E → E), IsFlowBox V x₀ a r T K Φ ∧
        ContDiffOn ℝ ((k : ℕ∞ω) + 1) V (ball x₀ a) ∧
        ContDiffOn ℝ ((k : ℕ∞ω) + 1) (fun p : ℝ × E => Φ p.1 p.2)
          (Ioo (-T) T ×ˢ ball x₀ r) := by
  induction k with
  | zero =>
    intro E _ _ _ V x₀ hV
    have hV1 : ContDiffAt ℝ 1 V x₀ := by simpa using hV
    obtain ⟨A, hA, H⟩ := exists_isFlowBox hV1
    obtain ⟨a₂, ha₂, hVon⟩ := Metric.eventually_nhds_iff_ball.1 (hV1.eventually (by simp))
    obtain ⟨r, T, K, Φ, h⟩ := H (min A a₂) (lt_min hA ha₂) (min_le_left _ _)
    refine ⟨min A a₂, r, T, K, Φ, h, ?_, by simpa using h.contDiffOn_one_uncurry⟩
    have hVc : ContDiffOn ℝ 1 V (ball x₀ (min A a₂)) := fun y hy =>
      (hVon y (ball_subset_ball (min_le_right _ _) hy)).contDiffWithinAt
    simpa using hVc
  | succ k ih =>
    intro E _ _ _ V x₀ hV
    have hcast : ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 := by push_cast; rfl
    rw [hcast] at hV ⊢
    have hne : ((k : ℕ∞ω) + 1) ≠ ω := by
      rw [← hcast]
      exact WithTop.natCast_ne_top _
    have hne2 : ((k : ℕ∞ω) + 1 + 1) ≠ ∞ := by
      have : ((k + 2 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 + 1 := by push_cast; ring
      rw [← this]
      intro hh
      have h2 : (((k + 2 : ℕ) : ℕ∞) : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) := hh
      exact ENat.natCast_ne_top (k + 2) (WithTop.coe_injective h2)
    -- the prolonged field and its flow box
    have hW : ContDiffAt ℝ ((k : ℕ∞ω) + 1) (prolong V) (x₀, ContinuousLinearMap.id ℝ E) := by
      have h1 : ContDiffAt ℝ ((k : ℕ∞ω) + 1) (fun p : E × (E →L[ℝ] E) => V p.1)
          (x₀, ContinuousLinearMap.id ℝ E) :=
        (hV.of_le le_self_add).comp _ contDiffAt_fst
      have h2 : ContDiffAt ℝ ((k : ℕ∞ω) + 1) (fun p : E × (E →L[ℝ] E) => fderiv ℝ V p.1)
          (x₀, ContinuousLinearMap.id ℝ E) :=
        (hV.fderiv_right (m := (k : ℕ∞ω) + 1) le_rfl).comp _ contDiffAt_fst
      exact h1.prodMk (h2.clm_comp contDiffAt_snd)
    obtain ⟨a', r', T', K', Ψ, hΨ, -, hΨc⟩ := ih hW
    -- a flow box of `V` inside it
    have hV1 : ContDiffAt ℝ 1 V x₀ := hV.of_le (by
      have : (1 : ℕ∞ω) ≤ (k : ℕ∞ω) + 1 := le_add_self
      exact this.trans le_self_add)
    obtain ⟨A, hA, H⟩ := exists_isFlowBox hV1
    obtain ⟨a₂, ha₂, hVon⟩ := Metric.eventually_nhds_iff_ball.1 (hV.eventually hne2)
    have ha' : 0 < a' := lt_of_le_of_lt dist_nonneg
      (mem_ball.1 (hΨ.initial_mem (mem_ball_self hΨ.r_pos)))
    set a : ℝ := min A (min a' a₂) with ha
    have ha0 : 0 < a := lt_min hA (lt_min ha' ha₂)
    obtain ⟨r₁, T₁, K, Φ, h₁⟩ := H a ha0 (min_le_left _ _)
    set r : ℝ := min r₁ r' with hr
    have hr0 : 0 < r := lt_min h₁.r_pos hΨ.r_pos
    have hK1 : (0 : ℝ) < 4 * (K + 1) := by positivity
    set T : ℝ := min (min T₁ T') (a' / (4 * (K + 1))) with hT
    have hT0 : 0 < T := lt_min (lt_min h₁.T_pos hΨ.T_pos) (div_pos ha' hK1)
    have h : IsFlowBox V x₀ a r T K Φ :=
      h₁.mono hr0 (min_le_left _ _) hT0 ((min_le_left _ _).trans (min_le_left _ _))
    have hΨ' : IsFlowBox (prolong V) (x₀, ContinuousLinearMap.id ℝ E) a' r' T K' Ψ :=
      hΨ.mono hΨ.r_pos le_rfl hT0 ((min_le_left _ _).trans (min_le_right _ _))
    have hKT : (K : ℝ) * Real.exp (K * T) * T < a' := by
      have hK0 : (0 : ℝ) ≤ K := K.2
      have he : Real.exp (K * T) ≤ 2 := by
        have h3 : Real.exp (K * T) ≤ Real.exp 1 :=
          Real.exp_le_exp.2 (h.mul_le.trans (by norm_num))
        have h4 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        have h5 : Real.exp (K * T) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 h.mul_le
        have h6 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        have h7 : 0 < Real.exp (1 / 2) := Real.exp_pos _
        nlinarith
      have hTle : T ≤ a' / (4 * (K + 1)) := min_le_right _ _
      have h8 : (K : ℝ) * T ≤ a' / 4 := by
        have h9 : (K : ℝ) * T ≤ K * (a' / (4 * (K + 1))) := mul_le_mul_of_nonneg_left hTle hK0
        have h10 : (K : ℝ) * (a' / (4 * (K + 1))) ≤ a' / 4 := by
          rw [← mul_div_assoc, div_le_iff₀ hK1]
          nlinarith
        linarith
      have h11 : (K : ℝ) * Real.exp (K * T) * T = (K * T) * Real.exp (K * T) := by ring
      have h12 : (K : ℝ) * T * Real.exp (K * T) ≤ a' / 4 * 2 :=
        mul_le_mul h8 he (Real.exp_pos _).le (by linarith)
      rw [h11]
      linarith
    -- the pair `(Φ, D_x Φ)` is the flow of the prolonged field
    have hpair : ∀ x ∈ ball x₀ r, ∀ t ∈ Icc (-T) T,
        Ψ t (x, ContinuousLinearMap.id ℝ E) = (Φ t x, fderiv ℝ (Φ t) x) := by
      intro x hx t ht
      have hx' : (x, ContinuousLinearMap.id ℝ E) ∈
          ball (x₀, ContinuousLinearMap.id ℝ E) r' := by
        rw [mem_ball, Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
        exact lt_of_lt_of_le (mem_ball.1 hx) (min_le_right _ _)
      have hc : ∀ u ∈ Icc (-T) T, HasDerivWithinAt (fun u => (Φ u x, fderiv ℝ (Φ u) x))
          (prolong V (Φ u x, fderiv ℝ (Φ u) x)) (Icc (-T) T) u := fun u hu =>
        (h.hasDerivWithinAt hx u hu).prodMk (h.hasDerivWithinAt_fderiv_flow hx hu)
      have hcs : ∀ u ∈ Icc (-T) T, (Φ u x, fderiv ℝ (Φ u) x) ∈
          ball (x₀, ContinuousLinearMap.id ℝ E) a' := by
        intro u hu
        rw [mem_ball, Prod.dist_eq]
        refine max_lt ?_ ?_
        · exact lt_of_lt_of_le (mem_ball.1 (h.flow_mem x hx u hu))
            ((min_le_right _ _).trans (min_le_left _ _))
        · rw [dist_eq_norm]
          refine lt_of_le_of_lt (h.norm_fderiv_flow_sub_id_le hx hu) (lt_of_le_of_lt ?_ hKT)
          exact mul_le_mul_of_nonneg_left (abs_le.2 hu)
            (mul_nonneg K.2 (Real.exp_pos _).le)
      have h0 : (fun u => Ψ u (x, ContinuousLinearMap.id ℝ E)) 0 =
          (fun u => (Φ u x, fderiv ℝ (Φ u) x)) 0 := by
        simp only [hΨ'.flow_zero _ hx', h.flow_zero x hx, h.fderiv_flow_zero hx]
      exact eqOn_of_trajectories hΨ'.lipschitzOnWith (hΨ'.hasDerivWithinAt hx')
        (hΨ'.flow_mem _ hx') hc hcs h0 ht
    -- smoothness of `Φ` and `D_x Φ` from that of `Ψ`
    have hι : ContDiff ℝ ((k : ℕ∞ω) + 1)
        (fun p : ℝ × E => (p.1, (p.2, ContinuousLinearMap.id ℝ E))) :=
      contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
    have hιm : MapsTo (fun p : ℝ × E => (p.1, (p.2, ContinuousLinearMap.id ℝ E)))
        (Ioo (-T) T ×ˢ ball x₀ r)
        (Ioo (-T') T' ×ˢ ball (x₀, ContinuousLinearMap.id ℝ E) r') := by
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have : T ≤ T' := (min_le_left _ _).trans (min_le_right _ _)
        have := ht.1
        simp only at *
        linarith
      · have : T ≤ T' := (min_le_left _ _).trans (min_le_right _ _)
        have := ht.2
        simp only at *
        linarith
      · rw [mem_ball, Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
        exact lt_of_lt_of_le (mem_ball.1 hx) (min_le_right _ _)
    have hΨι : ContDiffOn ℝ ((k : ℕ∞ω) + 1)
        (fun p : ℝ × E => Ψ p.1 (p.2, ContinuousLinearMap.id ℝ E))
        (Ioo (-T) T ×ˢ ball x₀ r) :=
      hΨc.comp hι.contDiffOn hιm
    have hΦc : ContDiffOn ℝ ((k : ℕ∞ω) + 1) (fun p : ℝ × E => Φ p.1 p.2)
        (Ioo (-T) T ×ˢ ball x₀ r) :=
      (contDiff_fst.comp_contDiffOn hΨι).congr fun p hp => by
        show Φ p.1 p.2 = (Ψ p.1 (p.2, ContinuousLinearMap.id ℝ E)).1
        rw [hpair p.2 hp.2 p.1 (Ioo_subset_Icc_self hp.1)]
    have hDc : ContDiffOn ℝ ((k : ℕ∞ω) + 1) (fun p : ℝ × E => fderiv ℝ (Φ p.1) p.2)
        (Ioo (-T) T ×ˢ ball x₀ r) :=
      (contDiff_snd.comp_contDiffOn hΨι).congr fun p hp => by
        show fderiv ℝ (Φ p.1) p.2 = (Ψ p.1 (p.2, ContinuousLinearMap.id ℝ E)).2
        rw [hpair p.2 hp.2 p.1 (Ioo_subset_Icc_self hp.1)]
    have hVc' : ContDiffOn ℝ ((k : ℕ∞ω) + 1 + 1) V (ball x₀ a) := fun y hy =>
      (hVon y (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
        hy)).contDiffWithinAt
    exact ⟨a, r, T, K, Φ, h, hVc',
      h.contDiffOn_succ_uncurry hne (hVc'.of_le le_self_add) hΦc hDc⟩

/-- **Teschl's Theorem 2.10: the solution of a time-dependent equation is `C^k` in the time, the
initial time and the initial point.**

Let `f : ℝ × E → E` be `C^{k+1}` at `(t₀, x₀)` (`k` a natural number; `E` a real Banach space).
Then there are `δ > 0` and a map `φ` such that, with `I = (t₀ - δ, t₀ + δ)` and `B` the ball of
radius `δ` about `x₀`: for `s ∈ I` and `x ∈ B`, `φ s s x = x` and `t ↦ φ t s x` solves
`ẋ = f (t, x)` on `I`; and both `(t, s, x) ↦ φ t s x` and its time derivative
`(t, s, x) ↦ f (t, φ t s x)` are `C^{k+1}` on `I × I × B`.

The proof adds the time to the dependent variables, as in the source: `φ t s x` is the second
component of the flow of `(τ, x) ↦ (1, f (τ, x))` for the time `t - s` from `(s, x)`. -/
theorem exists_solution_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (k : ℕ) {f : ℝ × E → E} {t₀ : ℝ} {x₀ : E}
    (hf : ContDiffAt ℝ ((k : ℕ∞ω) + 1) f (t₀, x₀)) :
    ∃ (δ : ℝ) (φ : ℝ → ℝ → E → E), 0 < δ ∧
      (∀ s ∈ Ioo (t₀ - δ) (t₀ + δ), ∀ x ∈ ball x₀ δ, φ s s x = x ∧
        ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), HasDerivAt (fun t => φ t s x) (f (t, φ t s x)) t) ∧
      ContDiffOn ℝ ((k : ℕ∞ω) + 1) (fun q : ℝ × ℝ × E => φ q.1 q.2.1 q.2.2)
        (Ioo (t₀ - δ) (t₀ + δ) ×ˢ Ioo (t₀ - δ) (t₀ + δ) ×ˢ ball x₀ δ) ∧
      ContDiffOn ℝ ((k : ℕ∞ω) + 1) (fun q : ℝ × ℝ × E => f (q.1, φ q.1 q.2.1 q.2.2))
        (Ioo (t₀ - δ) (t₀ + δ) ×ˢ Ioo (t₀ - δ) (t₀ + δ) ×ˢ ball x₀ δ) := by
  set W : ℝ × E → ℝ × E := fun p => ((1 : ℝ), f p) with hWdef
  have hW : ContDiffAt ℝ ((k : ℕ∞ω) + 1) W (t₀, x₀) := contDiffAt_const.prodMk hf
  obtain ⟨a, r, T, K, Ψ, h, hWc, hΨc⟩ := exists_isFlowBox_contDiffOn k hW
  -- the first component of the flow is the time
  have hfst : ∀ p ∈ ball (t₀, x₀) r, ∀ u ∈ Icc (-T) T, (Ψ u p).1 = p.1 + u := by
    intro p hp u hu
    have hg : ∀ v ∈ Icc (-T) T, HasDerivWithinAt (fun v => (Ψ v p).1 - v) (0 : ℝ)
        (Icc (-T) T) v := by
      intro v hv
      have h1 : HasDerivWithinAt (Prod.fst ∘ fun v => Ψ v p) (W (Ψ v p)).1 (Icc (-T) T) v :=
        (hasFDerivAt_fst (𝕜 := ℝ) (p := Ψ v p)).comp_hasDerivWithinAt v
          (h.hasDerivWithinAt hp v hv)
      have h2 : HasDerivWithinAt (fun v => (Ψ v p).1 - v) ((W (Ψ v p)).1 - 1) (Icc (-T) T) v :=
        h1.sub (hasDerivWithinAt_id v (Icc (-T) T))
      have h3 : (W (Ψ v p)).1 - 1 = 0 := by simp [hWdef]
      rw [h3] at h2
      exact h2
    have h3 := (convex_Icc (-T) T).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun v => (Ψ v p).1 - v) (f' := fun _ => (0 : ℝ)) hg (C := 0)
      (fun v _ => by simp) h.zero_mem hu
    simp only [h.flow_zero p hp, sub_zero, zero_mul, norm_le_zero_iff] at h3
    linarith
  set δ : ℝ := min (T / 2) r with hδ
  have hδ0 : 0 < δ := lt_min (half_pos h.T_pos) h.r_pos
  have hδT : δ ≤ T / 2 := min_le_left _ _
  -- the points and times that occur
  have hdom : ∀ {t s : ℝ} {x : E}, t ∈ Ioo (t₀ - δ) (t₀ + δ) → s ∈ Ioo (t₀ - δ) (t₀ + δ) →
      x ∈ ball x₀ δ → t - s ∈ Ioo (-T) T ∧ ((s, x) : ℝ × E) ∈ ball (t₀, x₀) r := by
    intro t s x ht hs hx
    refine ⟨⟨by linarith [ht.1, hs.2], by linarith [ht.2, hs.1]⟩, ?_⟩
    rw [mem_ball, Prod.dist_eq]
    refine max_lt ?_ (lt_of_lt_of_le (mem_ball.1 hx) (min_le_right _ _))
    rw [Real.dist_eq, abs_lt]
    have hr : δ ≤ r := min_le_right _ _
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hι : ContDiff ℝ ((k : ℕ∞ω) + 1)
      (fun q : ℝ × ℝ × E => (q.1 - q.2.1, ((q.2.1, q.2.2) : ℝ × E))) :=
    (contDiff_fst.sub (contDiff_fst.comp contDiff_snd)).prodMk
      ((contDiff_fst.comp contDiff_snd).prodMk (contDiff_snd.comp contDiff_snd))
  have hιm : MapsTo (fun q : ℝ × ℝ × E => (q.1 - q.2.1, ((q.2.1, q.2.2) : ℝ × E)))
      (Ioo (t₀ - δ) (t₀ + δ) ×ˢ Ioo (t₀ - δ) (t₀ + δ) ×ˢ ball x₀ δ)
      (Ioo (-T) T ×ˢ ball (t₀, x₀) r) := by
    rintro ⟨t, s, x⟩ ⟨ht, hs, hx⟩
    exact ⟨(hdom ht hs hx).1, (hdom ht hs hx).2⟩
  have hΨι : ContDiffOn ℝ ((k : ℕ∞ω) + 1)
      (fun q : ℝ × ℝ × E => Ψ (q.1 - q.2.1) (q.2.1, q.2.2))
      (Ioo (t₀ - δ) (t₀ + δ) ×ˢ Ioo (t₀ - δ) (t₀ + δ) ×ˢ ball x₀ δ) :=
    hΨc.comp hι.contDiffOn hιm
  refine ⟨δ, fun t s x => (Ψ (t - s) (s, x)).2, hδ0, fun s hs x hx => ⟨?_, fun t ht => ?_⟩,
    contDiff_snd.comp_contDiffOn hΨι, ?_⟩
  · have hp := (hdom hs hs hx).2
    simp only [sub_self, h.flow_zero _ hp]
  · obtain ⟨hu, hp⟩ := hdom ht hs hx
    have hu' : t - s ∈ Icc (-T) T := Ioo_subset_Icc_self hu
    have h1 : HasDerivAt (fun t => Ψ (t - s) (s, x)) (W (Ψ (t - s) (s, x))) t := by
      have h2 := (h.hasDerivAt _ hp (t - s) hu').scomp t
        ((hasDerivAt_id t).sub_const s)
      simpa [Function.comp_def] using h2
    have h3 : HasDerivAt (Prod.snd ∘ fun t => Ψ (t - s) (s, x)) (W (Ψ (t - s) (s, x))).2 t :=
      (hasFDerivAt_snd (𝕜 := ℝ) (p := Ψ (t - s) (s, x))).comp_hasDerivAt t h1
    have h4 : Ψ (t - s) (s, x) = (t, (Ψ (t - s) (s, x)).2) :=
      Prod.ext (by rw [hfst _ hp _ hu']; simp) rfl
    have h5 : (W (Ψ (t - s) (s, x))).2 = f (t, (Ψ (t - s) (s, x)).2) := by
      conv_lhs => rw [h4]
    rw [h5] at h3
    exact h3
  · -- the time derivative `f (t, φ)` is the second component of `W` along the flow
    have hmaps : MapsTo (fun q : ℝ × ℝ × E => Ψ (q.1 - q.2.1) (q.2.1, q.2.2))
        (Ioo (t₀ - δ) (t₀ + δ) ×ˢ Ioo (t₀ - δ) (t₀ + δ) ×ˢ ball x₀ δ) (ball (t₀, x₀) a) := by
      rintro ⟨t, s, x⟩ ⟨ht, hs, hx⟩
      obtain ⟨hu, hp⟩ := hdom ht hs hx
      exact h.flow_mem _ hp _ (Ioo_subset_Icc_self hu)
    have h6 : ContDiffOn ℝ ((k : ℕ∞ω) + 1)
        (fun q : ℝ × ℝ × E => (W (Ψ (q.1 - q.2.1) (q.2.1, q.2.2))).2)
        (Ioo (t₀ - δ) (t₀ + δ) ×ˢ Ioo (t₀ - δ) (t₀ + δ) ×ˢ ball x₀ δ) :=
      contDiff_snd.comp_contDiffOn (hWc.comp hΨι hmaps)
    refine h6.congr fun q hq => ?_
    obtain ⟨t, s, x⟩ := q
    obtain ⟨ht, hs, hx⟩ := hq
    obtain ⟨hu, hp⟩ := hdom ht hs hx
    have h4 : Ψ (t - s) (s, x) = (t, (Ψ (t - s) (s, x)).2) :=
      Prod.ext (by rw [hfst _ hp _ (Ioo_subset_Icc_self hu)]; simp) rfl
    show f (t, (Ψ (t - s) (s, x)).2) = (W (Ψ (t - s) (s, x))).2
    conv_rhs => rw [h4]

end Lightlike.ODE
