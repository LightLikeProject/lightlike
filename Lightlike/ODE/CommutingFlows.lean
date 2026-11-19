import Lightlike.ODE.FlowJoint
import Lightlike.ODE.LocalFlow

/-!
# Flows of vector fields with vanishing Lie bracket commute

For `C¹` vector fields `V`, `W` on a real Banach space with `[V, W] = 0` near a point `x₀`, the
local flows commute near `x₀`: `Φ t (Ψ s x) = Ψ s (Φ t x)` for small `t`, `s` and `x` near `x₀`.

The proof follows Michor's Corollary 3.15: the flow `Φ t` of `V` carries `W` into itself
(`IsFlowBox.fderiv_flow_apply_eq_of_lieBracket_eq_zero`), so `s ↦ Φ t (Ψ s x)` is an integral
curve of `W` through `Φ t x`, like `s ↦ Ψ s (Φ t x)`; integral curves are unique.

## Main results

* `Lightlike.ODE.IsFlowBox.flow_comm`: commutation in two flow boxes with the same large ball.
* `Lightlike.ODE.exists_flows_commute`: the local statement for two fields that are `C¹` at `x₀`.

## References

* `michor-2008`: P. W. Michor, *Topics in Differential Geometry*, Corollary 3.15, page 28 of the
  author's version: `[X, Y] = 0` if and only if the flows commute wherever one side is defined
  along the whole rectangle of times. Differences: this file proves the direction from the
  bracket to the flows only, locally (small times, initial points near `x₀`), for `C¹` fields on
  an open subset of a Banach space (the source has smooth fields on a manifold).
-/

open Set Metric Filter Topology
open scoped NNReal

noncomputable section

namespace Lightlike.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace IsFlowBox

variable {V W : E → E} {x₀ : E} {a r r' T T' : ℝ} {K K' : ℝ≥0} {Φ Ψ : ℝ → E → E}

/-- In a flow box, a trajectory that starts in the ball of radius `ρ ≤ r` about `x₀` stays in the
ball of radius `ρ + (‖V x₀‖ + K a) T`. -/
theorem flow_mem_ball_add (h : IsFlowBox V x₀ a r T K Φ) {ρ : ℝ} (hρ : ρ ≤ r) {x : E}
    (hx : x ∈ ball x₀ ρ) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    Φ t x ∈ ball x₀ (ρ + (‖V x₀‖ + K * a) * T) := by
  have hx' : x ∈ ball x₀ r := ball_subset_ball hρ hx
  have h1 := h.norm_flow_sub_self_le hx' ht
  have hM : 0 ≤ ‖V x₀‖ + K * a := (norm_nonneg _).trans (h.norm_field_le (h.initial_mem hx'))
  have h2 : (‖V x₀‖ + K * a) * |t| ≤ (‖V x₀‖ + K * a) * T :=
    mul_le_mul_of_nonneg_left (abs_le.2 ht) hM
  rw [mem_ball]
  calc dist (Φ t x) x₀ ≤ dist (Φ t x) x + dist x x₀ := dist_triangle _ _ _
    _ < (‖V x₀‖ + K * a) * T + ρ := by
      rw [dist_eq_norm]
      exact add_lt_add_of_le_of_lt (h1.trans h2) (mem_ball.1 hx)
    _ = ρ + (‖V x₀‖ + K * a) * T := add_comm _ _

/-- **Commuting flows.** Let `Φ` and `Ψ` be flow boxes of `V` and `W` about `x₀` with the same
large ball, on which `[V, W] = 0`. If `x` and `Φ t x` are initial points of the `W`-box and the
whole `W`-trajectory of `x` consists of initial points of the `V`-box, then
`Φ t (Ψ s x) = Ψ s (Φ t x)` for all `s` in the time interval of the `W`-box. -/
theorem flow_comm [CompleteSpace E] (hV : IsFlowBox V x₀ a r T K Φ)
    (hW : IsFlowBox W x₀ a r' T' K' Ψ)
    (hVW : ∀ y ∈ ball x₀ a, VectorField.lieBracket ℝ V W y = 0)
    {x : E} (hx : x ∈ ball x₀ r') {t : ℝ} (ht : t ∈ Icc (-T) T) (hΦ : Φ t x ∈ ball x₀ r')
    (hΨ : ∀ s ∈ Icc (-T') T', Ψ s x ∈ ball x₀ r) {s : ℝ} (hs : s ∈ Icc (-T') T') :
    Φ t (Ψ s x) = Ψ s (Φ t x) := by
  have hc : ∀ s ∈ Icc (-T') T', HasDerivWithinAt (fun s => Φ t (Ψ s x)) (W (Φ t (Ψ s x)))
      (Icc (-T') T') s := by
    intro s hs
    have hd := (hV.differentiableAt_flow (hΨ s hs) ht).hasFDerivAt
    have h1 : HasDerivWithinAt (Φ t ∘ fun s => Ψ s x)
        (fderiv ℝ (Φ t) (Ψ s x) (W (Ψ s x))) (Icc (-T') T') s :=
      hd.comp_hasDerivWithinAt s (hW.hasDerivWithinAt hx s hs)
    rw [hV.fderiv_flow_apply_eq_of_lieBracket_eq_zero hW.differentiableAt (hΨ s hs)
      (fun u hu => hVW _ (hV.flow_mem _ (hΨ s hs) u hu)) ht] at h1
    exact h1
  have h0 : (fun s => Φ t (Ψ s x)) 0 = (fun s => Ψ s (Φ t x)) 0 := by
    simp only [hW.flow_zero x hx, hW.flow_zero _ hΦ]
  exact eqOn_of_trajectories hW.lipschitzOnWith hc
    (fun s hs => hV.flow_mem _ (hΨ s hs) t ht) (hW.hasDerivWithinAt hΦ)
    (hW.flow_mem _ hΦ) h0 hs

end IsFlowBox

/-- **The flows of two `C¹` vector fields with vanishing Lie bracket commute locally** (Michor,
Corollary 3.15, (1) ⇒ (3), local form).

If `V` and `W` are `C¹` at `x₀` and `[V, W] = 0` near `x₀`, there are flow boxes `Φ` of `V` and
`Ψ` of `W` about `x₀`, with the same balls and the same time `τ`, and a radius `ρ > 0`, such that
for `x` within `ρ` of `x₀` and `t, s ∈ [-τ, τ]` the points `Φ t x` and `Ψ s x` are again initial
points of the boxes and `Φ t (Ψ s x) = Ψ s (Φ t x)`. -/
theorem exists_flows_commute [CompleteSpace E] {V W : E → E} {x₀ : E}
    (hV : ContDiffAt ℝ 1 V x₀) (hW : ContDiffAt ℝ 1 W x₀)
    (hVW : ∀ᶠ y in 𝓝 x₀, VectorField.lieBracket ℝ V W y = 0) :
    ∃ (a r τ ρ : ℝ) (K K' : ℝ≥0) (Φ Ψ : ℝ → E → E),
      IsFlowBox V x₀ a r τ K Φ ∧ IsFlowBox W x₀ a r τ K' Ψ ∧ 0 < ρ ∧ ρ ≤ r ∧
      ∀ x ∈ ball x₀ ρ, ∀ t ∈ Icc (-τ) τ, ∀ s ∈ Icc (-τ) τ,
        Φ t x ∈ ball x₀ r ∧ Ψ s x ∈ ball x₀ r ∧ Φ t (Ψ s x) = Ψ s (Φ t x) := by
  obtain ⟨A₁, hA₁, H₁⟩ := exists_isFlowBox hV
  obtain ⟨A₂, hA₂, H₂⟩ := exists_isFlowBox hW
  obtain ⟨A₃, hA₃, H₃⟩ := Metric.eventually_nhds_iff_ball.1 hVW
  set a : ℝ := min A₁ (min A₂ A₃) with ha
  have ha0 : 0 < a := lt_min hA₁ (lt_min hA₂ hA₃)
  obtain ⟨r₁, T₁, K, Φ, h₁⟩ := H₁ a ha0 (min_le_left _ _)
  obtain ⟨r₂, T₂, K', Ψ, h₂⟩ := H₂ a ha0 ((min_le_right _ _).trans (min_le_left _ _))
  have hbr : ∀ y ∈ ball x₀ a, VectorField.lieBracket ℝ V W y = 0 := fun y hy =>
    H₃ y (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hy)
  set r : ℝ := min r₁ r₂ with hr
  have hr0 : 0 < r := lt_min h₁.r_pos h₂.r_pos
  set M : ℝ := max (‖V x₀‖ + K * a) (‖W x₀‖ + K' * a) with hM
  have hM0 : 0 ≤ M :=
    ((norm_nonneg _).trans (h₁.norm_field_le (mem_ball_self ha0))).trans (le_max_left _ _)
  set τ : ℝ := min (min T₁ T₂) (r / (2 * (M + 1))) with hτ
  have hM1 : 0 < 2 * (M + 1) := by linarith
  have hτ0 : 0 < τ := lt_min (lt_min h₁.T_pos h₂.T_pos) (div_pos hr0 hM1)
  have hMτ : M * τ ≤ r / 2 := by
    have h1 : M * τ ≤ M * (r / (2 * (M + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hM0
    have h2 : M * (r / (2 * (M + 1))) ≤ r / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ hM1]
      nlinarith
    linarith
  have hV' : IsFlowBox V x₀ a r τ K Φ :=
    h₁.mono hr0 (min_le_left _ _) hτ0 ((min_le_left _ _).trans (min_le_left _ _))
  have hW' : IsFlowBox W x₀ a r τ K' Ψ :=
    h₂.mono hr0 (min_le_right _ _) hτ0 ((min_le_left _ _).trans (min_le_right _ _))
  have hsub₁ : ball x₀ (r / 2 + (‖V x₀‖ + K * a) * τ) ⊆ ball x₀ r := by
    refine ball_subset_ball ?_
    have : (‖V x₀‖ + K * a) * τ ≤ M * τ := mul_le_mul_of_nonneg_right (le_max_left _ _) hτ0.le
    linarith
  have hsub₂ : ball x₀ (r / 2 + (‖W x₀‖ + K' * a) * τ) ⊆ ball x₀ r := by
    refine ball_subset_ball ?_
    have : (‖W x₀‖ + K' * a) * τ ≤ M * τ := mul_le_mul_of_nonneg_right (le_max_right _ _) hτ0.le
    linarith
  refine ⟨a, r, τ, r / 2, K, K', Φ, Ψ, hV', hW', half_pos hr0, by linarith, ?_⟩
  intro x hx t ht s hs
  have hxr : x ∈ ball x₀ r := ball_subset_ball (by linarith) hx
  have hΦ : Φ t x ∈ ball x₀ r := hsub₁ (hV'.flow_mem_ball_add (by linarith) hx ht)
  have hΨ : ∀ s ∈ Icc (-τ) τ, Ψ s x ∈ ball x₀ r := fun s hs =>
    hsub₂ (hW'.flow_mem_ball_add (by linarith) hx hs)
  exact ⟨hΦ, hΨ s hs, hV'.flow_comm hW' hbr hxr ht hΦ hΨ hs⟩

end Lightlike.ODE
