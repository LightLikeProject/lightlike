import Lightlike.ODE.FlowDeriv
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Joint differentiability of a flow, and fields carried along by a flow

In a flow box (`Lightlike.ODE.IsFlowBox`) of a `C¹` field `V`:

* the flow `(t, x) ↦ Φ t x` is differentiable in both variables at once, with derivative
  `(τ, ξ) ↦ τ • V (Φ t x) + D_x Φ_t ξ` (`IsFlowBox.hasFDerivAt_uncurry`);
* a differentiable field `W` with `[V, W] = 0` is carried into itself by the flow:
  `D_x Φ_t (W x) = W (Φ t x)` (`IsFlowBox.fderiv_flow_apply_eq_of_lieBracket_eq_zero`). This is
  the step (1) ⇒ (2) of Michor's Corollary 3.15, proved here by uniqueness for the linear equation
  `u̇ = DV(Φ t x) u`, which both sides solve.

## References

* `teschl-2012`: G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, Theorem 2.10,
  pages 46–47 of the author's version (joint regularity of the flow; here for an autonomous `C¹`
  field and without the initial time).
* `michor-2008`: P. W. Michor, *Topics in Differential Geometry*, Corollary 3.15, page 28 of the
  author's version.
-/

open Set Metric Filter Topology
open scoped NNReal

noncomputable section

namespace Lightlike.ODE

namespace IsFlowBox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V : E → E} {x₀ : E} {a r T : ℝ} {K : ℝ≥0} {Φ : ℝ → E → E}

/-- In a flow box the field is bounded by `‖V x₀‖ + K a` on the large ball. -/
lemma norm_field_le (h : IsFlowBox V x₀ a r T K Φ) {y : E} (hy : y ∈ ball x₀ a) :
    ‖V y‖ ≤ ‖V x₀‖ + K * a := by
  have ha : 0 < a := lt_of_le_of_lt dist_nonneg (mem_ball.1 hy)
  have h1 : ‖V y - V x₀‖ ≤ K * ‖y - x₀‖ := h.lipschitzOnWith.norm_sub_le hy (mem_ball_self ha)
  have h2 : ‖y - x₀‖ ≤ a := (mem_ball_iff_norm.1 hy).le
  calc ‖V y‖ = ‖V x₀ + (V y - V x₀)‖ := by simp
    _ ≤ ‖V x₀‖ + ‖V y - V x₀‖ := norm_add_le _ _
    _ ≤ ‖V x₀‖ + K * a := by
      have : (K : ℝ) * ‖y - x₀‖ ≤ K * a := mul_le_mul_of_nonneg_left h2 K.2
      linarith

/-- In a flow box a trajectory moves with speed at most `‖V x₀‖ + K a`. -/
theorem norm_flow_sub_time_le (h : IsFlowBox V x₀ a r T K Φ) {x : E} (hx : x ∈ ball x₀ r)
    {s t : ℝ} (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) :
    ‖Φ t x - Φ s x‖ ≤ (‖V x₀‖ + K * a) * |t - s| := by
  have := (convex_Icc (-T) T).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => Φ t x) (f' := fun t => V (Φ t x)) (h.hasDerivWithinAt hx)
    (fun u hu => h.norm_field_le (h.flow_mem x hx u hu)) hs ht
  simpa [Real.norm_eq_abs] using this

/-- In a flow box a point of the trajectory of `x` is within `(‖V x₀‖ + K a) |t|` of `x`. -/
theorem norm_flow_sub_self_le (h : IsFlowBox V x₀ a r T K Φ) {x : E} (hx : x ∈ ball x₀ r)
    {t : ℝ} (ht : t ∈ Icc (-T) T) : ‖Φ t x - x‖ ≤ (‖V x₀‖ + K * a) * |t| := by
  have := h.norm_flow_sub_time_le hx h.zero_mem ht
  simpa [h.flow_zero x hx] using this

/-- **A field that commutes with `V` is carried into itself by the flow of `V`.** In a flow box
of `V`, if `W` is differentiable on the large ball and `[V, W] = 0` along the trajectory of `x`,
then `D_x Φ_t (W x) = W (Φ t x)`: Michor, Corollary 3.15, (1) ⇒ (2). (The bracket is only needed
along the trajectory, which matters when the fields commute on an invariant subset only.) -/
theorem fderiv_flow_apply_eq_of_lieBracket_eq_zero [CompleteSpace E]
    (h : IsFlowBox V x₀ a r T K Φ) {W : E → E}
    (hW : ∀ y ∈ ball x₀ a, DifferentiableAt ℝ W y)
    {x : E} (hx : x ∈ ball x₀ r)
    (hVW : ∀ t ∈ Icc (-T) T, VectorField.lieBracket ℝ V W (Φ t x) = 0)
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    fderiv ℝ (Φ t) x (W x) = W (Φ t x) := by
  have hu : ∀ t ∈ Icc (-T) T, HasDerivWithinAt (fun t => fderiv ℝ (Φ t) x (W x))
      (fderiv ℝ V (Φ t x) (fderiv ℝ (Φ t) x (W x))) (Icc (-T) T) t := by
    intro t ht
    have h1 := (h.hasDerivWithinAt_fderiv_flow hx ht).clm_apply
      (hasDerivWithinAt_const t (Icc (-T) T) (W x))
    simpa using h1
  have hw : ∀ t ∈ Icc (-T) T, HasDerivWithinAt (fun t => W (Φ t x))
      (fderiv ℝ V (Φ t x) (W (Φ t x))) (Icc (-T) T) t := by
    intro t ht
    have hmem := h.flow_mem x hx t ht
    have h1 : HasDerivWithinAt (W ∘ fun t => Φ t x) (fderiv ℝ W (Φ t x) (V (Φ t x)))
        (Icc (-T) T) t :=
      (hW _ hmem).hasFDerivAt.comp_hasDerivWithinAt t (h.hasDerivWithinAt hx t ht)
    have h2 : fderiv ℝ W (Φ t x) (V (Φ t x)) = fderiv ℝ V (Φ t x) (W (Φ t x)) := by
      have := hVW t ht
      rw [VectorField.lieBracket] at this
      exact sub_eq_zero.1 this
    rw [h2] at h1
    exact h1
  have h0 : (fun t => fderiv ℝ (Φ t) x (W x)) 0 = (fun t => W (Φ t x)) 0 := by
    simp [h.fderiv_flow_zero hx, h.flow_zero x hx]
  exact eqOn_of_linear (A := fun t => fderiv ℝ V (Φ t x)) (K := K)
    (fun t ht => h.norm_fderiv_le _ (h.flow_mem x hx t ht)) hu hw h0 ht

/-- **In a flow box the flow is differentiable in `(t, x)`**, with derivative
`(τ, ξ) ↦ τ • V (Φ t x) + D_x Φ_t ξ`. -/
theorem hasFDerivAt_uncurry [CompleteSpace E] (h : IsFlowBox V x₀ a r T K Φ) {x : E}
    (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo (-T) T) :
    HasFDerivAt (fun p : ℝ × E => Φ p.1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (V (Φ t x)) +
        (fderiv ℝ (Φ t) x).comp (ContinuousLinearMap.snd ℝ ℝ E)) (t, x) := by
  have ht' : t ∈ Icc (-T) T := Ioo_subset_Icc_self ht
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set M : ℝ := ‖V x₀‖ + K * a with hM
  have hM0 : 0 ≤ M :=
    (norm_nonneg _).trans (h.norm_field_le (h.initial_mem hx))
  set e : ℝ := Real.exp (K * T) with he
  have he0 : 0 < e := Real.exp_pos _
  -- the derivative in the initial point, as an estimate
  have hD := (h.differentiableAt_flow hx ht').hasFDerivAt
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff] at hD
  have hD' : ∀ᶠ p : ℝ × E in 𝓝 0,
      ‖Φ t (x + p.2) - Φ t x - fderiv ℝ (Φ t) x p.2‖ ≤ c / 2 * ‖p.2‖ :=
    (continuous_snd.tendsto (0 : ℝ × E)).eventually (hD (half_pos hc))
  have hr : 0 < r - dist x x₀ := sub_pos.2 (mem_ball.1 hx)
  have hτ1 : 0 < min (T - t) (t + T) := lt_min (by linarith [ht.2]) (by linarith [ht.1])
  set q : ℝ := c / (2 * (K * M + K * e + 1)) with hq
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hKM : 0 ≤ K * M := mul_nonneg hK0 hM0
  have hKe : 0 ≤ K * e := mul_nonneg hK0 he0.le
  have hden : 0 < 2 * (K * M + K * e + 1) := by linarith
  have hq0 : 0 < q := div_pos hc hden
  have hball : ∀ᶠ p : ℝ × E in 𝓝 0, p ∈ ball (0 : ℝ × E) (min (min (T - t) (t + T)) (min q (r - dist x x₀))) :=
    Metric.ball_mem_nhds _ (lt_min hτ1 (lt_min hq0 hr))
  filter_upwards [hD', hball] with p hp1 hp2
  obtain ⟨τ, ξ⟩ := p
  rw [mem_ball_zero_iff] at hp2
  have hτn : |τ| ≤ ‖((τ, ξ) : ℝ × E)‖ := by
    rw [← Real.norm_eq_abs]; exact norm_fst_le (τ, ξ)
  have hξn : ‖ξ‖ ≤ ‖((τ, ξ) : ℝ × E)‖ := norm_snd_le (τ, ξ)
  have hτT : |τ| < min (T - t) (t + T) :=
    lt_of_le_of_lt hτn (lt_of_lt_of_le hp2 (min_le_left _ _))
  have hτq : |τ| < q :=
    lt_of_le_of_lt hτn (lt_of_lt_of_le hp2 ((min_le_right _ _).trans (min_le_left _ _)))
  have hξr : ‖ξ‖ < r - dist x x₀ :=
    lt_of_le_of_lt hξn (lt_of_lt_of_le hp2 ((min_le_right _ _).trans (min_le_right _ _)))
  have hxξ : x + ξ ∈ ball x₀ r := by
    rw [mem_ball]
    calc dist (x + ξ) x₀ ≤ dist (x + ξ) x + dist x x₀ := dist_triangle _ _ _
      _ = ‖ξ‖ + dist x x₀ := by simp [dist_eq_norm]
      _ < r := by linarith
  have habs := abs_lt.1 hτT
  have htτ : t + τ ∈ Icc (-T) T := by
    constructor
    · have := lt_of_lt_of_le habs.1 (le_refl _)
      have h3 : min (T - t) (t + T) ≤ t + T := min_le_right _ _
      linarith
    · have h3 : min (T - t) (t + T) ≤ T - t := min_le_left _ _
      linarith [habs.2]
  -- first term: the trajectory of `x + ξ` between the times `t` and `t + τ`
  have hfirst : ‖Φ (t + τ) (x + ξ) - Φ t (x + ξ) - τ • V (Φ t (x + ξ))‖ ≤ K * M * |τ| * |τ| := by
    have hS : uIcc t (t + τ) ⊆ Icc (-T) T := uIcc_subset_Icc ht' htτ
    have hg : ∀ s ∈ uIcc t (t + τ), HasDerivWithinAt
        (fun s => Φ s (x + ξ) - s • V (Φ t (x + ξ)))
        (V (Φ s (x + ξ)) - V (Φ t (x + ξ))) (uIcc t (t + τ)) s := by
      intro s hs
      have h1 := ((h.hasDerivWithinAt hxξ s (hS hs)).mono hS)
      have h2 := (hasDerivWithinAt_id s (uIcc t (t + τ))).smul_const (V (Φ t (x + ξ)))
      simp only [one_smul] at h2
      exact h1.sub h2
    have hbound : ∀ s ∈ uIcc t (t + τ), ‖V (Φ s (x + ξ)) - V (Φ t (x + ξ))‖ ≤ K * M * |τ| := by
      intro s hs
      have h1 : ‖V (Φ s (x + ξ)) - V (Φ t (x + ξ))‖ ≤ K * ‖Φ s (x + ξ) - Φ t (x + ξ)‖ :=
        h.lipschitzOnWith.norm_sub_le (h.flow_mem _ hxξ s (hS hs)) (h.flow_mem _ hxξ t ht')
      have h2 : ‖Φ s (x + ξ) - Φ t (x + ξ)‖ ≤ M * |s - t| :=
        h.norm_flow_sub_time_le hxξ ht' (hS hs)
      have h3 : |s - t| ≤ |τ| := by
        have := abs_sub_left_of_mem_uIcc hs
        simpa using this
      calc ‖V (Φ s (x + ξ)) - V (Φ t (x + ξ))‖ ≤ K * (M * |s - t|) :=
            h1.trans (mul_le_mul_of_nonneg_left h2 hK0)
        _ ≤ K * (M * |τ|) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hM0) hK0
        _ = K * M * |τ| := by ring
    have := (convex_uIcc t (t + τ)).norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound
      left_mem_uIcc right_mem_uIcc
    have hrew : Φ (t + τ) (x + ξ) - (t + τ) • V (Φ t (x + ξ)) -
        (Φ t (x + ξ) - t • V (Φ t (x + ξ))) =
        Φ (t + τ) (x + ξ) - Φ t (x + ξ) - τ • V (Φ t (x + ξ)) := by
      rw [add_smul]; abel
    simp only [hrew, add_sub_cancel_left, Real.norm_eq_abs] at this
    exact this
  -- second term: the field at time `t` along the two trajectories
  have hsecond : ‖τ • (V (Φ t (x + ξ)) - V (Φ t x))‖ ≤ |τ| * (K * (‖ξ‖ * e)) := by
    rw [norm_smul, Real.norm_eq_abs]
    have h1 : ‖V (Φ t (x + ξ)) - V (Φ t x)‖ ≤ K * ‖Φ t (x + ξ) - Φ t x‖ :=
      h.lipschitzOnWith.norm_sub_le (h.flow_mem _ hxξ t ht') (h.flow_mem _ hx t ht')
    have h2 : ‖Φ t (x + ξ) - Φ t x‖ ≤ ‖ξ‖ * e := by
      have := h.norm_flow_sub_le hxξ hx ht'
      simpa using this
    exact mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hK0)) (abs_nonneg _)
  have hsplit : Φ (t + τ) (x + ξ) - Φ t x - (τ • V (Φ t x) + fderiv ℝ (Φ t) x ξ) =
      (Φ (t + τ) (x + ξ) - Φ t (x + ξ) - τ • V (Φ t (x + ξ))) +
        τ • (V (Φ t (x + ξ)) - V (Φ t x)) + (Φ t (x + ξ) - Φ t x - fderiv ℝ (Φ t) x ξ) := by
    rw [smul_sub]; abel
  have hgoal : ‖Φ (t + τ) (x + ξ) - Φ t x - (τ • V (Φ t x) + fderiv ℝ (Φ t) x ξ)‖ ≤
      c * ‖((τ, ξ) : ℝ × E)‖ := by
    rw [hsplit]
    set n : ℝ := ‖((τ, ξ) : ℝ × E)‖ with hn
    have hn0 : 0 ≤ n := norm_nonneg _
    have hτ0 : 0 ≤ |τ| := abs_nonneg τ
    have h1 : K * M * |τ| * |τ| ≤ K * M * |τ| * n :=
      mul_le_mul_of_nonneg_left hτn (mul_nonneg hKM hτ0)
    have h2 : |τ| * (K * (‖ξ‖ * e)) ≤ K * e * |τ| * n := by
      have : |τ| * (K * (‖ξ‖ * e)) = K * e * |τ| * ‖ξ‖ := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hξn (mul_nonneg hKe hτ0)
    have h3 : c / 2 * ‖ξ‖ ≤ c / 2 * n := mul_le_mul_of_nonneg_left hξn (half_pos hc).le
    have h4 : (K * M + K * e) * |τ| ≤ c / 2 := by
      have h5 : (K * M + K * e) * |τ| ≤ (K * M + K * e) * q :=
        mul_le_mul_of_nonneg_left hτq.le (add_nonneg hKM hKe)
      have h6 : (K * M + K * e) * q ≤ c / 2 := by
        rw [hq, ← mul_div_assoc, div_le_iff₀ hden]
        nlinarith
      linarith
    have h9 : (K * M + K * e) * |τ| * n ≤ c / 2 * n := mul_le_mul_of_nonneg_right h4 hn0
    calc ‖(Φ (t + τ) (x + ξ) - Φ t (x + ξ) - τ • V (Φ t (x + ξ))) +
          τ • (V (Φ t (x + ξ)) - V (Φ t x)) + (Φ t (x + ξ) - Φ t x - fderiv ℝ (Φ t) x ξ)‖
        ≤ ‖Φ (t + τ) (x + ξ) - Φ t (x + ξ) - τ • V (Φ t (x + ξ))‖ +
          ‖τ • (V (Φ t (x + ξ)) - V (Φ t x))‖ + ‖Φ t (x + ξ) - Φ t x - fderiv ℝ (Φ t) x ξ‖ :=
          norm_add₃_le
      _ ≤ K * M * |τ| * |τ| + |τ| * (K * (‖ξ‖ * e)) + c / 2 * ‖ξ‖ :=
          add_le_add (add_le_add hfirst hsecond) hp1
      _ ≤ c * n := by linarith
  simpa using hgoal

end IsFlowBox

end Lightlike.ODE
