import Lightlike.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Differentiability of a flow in the initial point

For a `C¹` vector field `V` on a real Banach space `E`, the local flow `Φ t x` (the solution of
`ẋ = V x` that starts at `x`) is differentiable in `x`, and its derivative `D_x Φ_t` solves the
first variational equation `d/dt D_x Φ_t = DV(Φ_t x) ∘ D_x Φ_t`, `D_x Φ_0 = id`.

The proof is the one in Teschl's book: with `ψ` the solution of the variational equation along
`t ↦ Φ t x`, the difference `Φ t (x + h) - Φ t x - ψ t h` has derivative
`DV(Φ t x) (…) + R`, where `‖R‖ ≤ η ‖Φ t (x + h) - Φ t x‖` for small `h` by uniform continuity of
`DV` near the compact trajectory, and Grönwall's inequality bounds it by a multiple of `η ‖h‖`.

## Main definitions

* `Lightlike.ODE.IsFlowBox V x₀ a r T K Φ`: `Φ` is a flow of `V` for initial points in the ball of
  radius `r` about `x₀` and times in `[-T, T]`, with values in the ball of radius `a`, where `V`
  is differentiable with a continuous derivative of norm at most `K`, and `K T ≤ 1/2`.

## Main results

* `Lightlike.ODE.IsFlowBox.hasFDerivAt_of_variational`: a solution of the variational equation
  along a trajectory is the derivative of the flow in the initial point.
* `Lightlike.ODE.IsFlowBox.differentiableAt_flow`, `IsFlowBox.hasDerivWithinAt_fderiv_flow`,
  `IsFlowBox.fderiv_flow_zero`: the flow is differentiable in the initial point and its derivative
  solves the variational equation.
* `Lightlike.ODE.IsFlowBox.continuousOn_fderiv_flow`: the derivative is continuous in `(t, x)`.

## References

* `teschl-2012`: G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, Theorem 2.10
  and equation (2.49), pages 46–47 of the author's version. The source states the result for a
  time-dependent field of class `C^k` on an open subset of `ℝⁿ⁺¹`, jointly in the time, the initial
  time and the initial point; this file proves the case of an autonomous `C¹` field (on a Banach
  space), with the derivative in the initial point only.
-/

open Set Metric Filter Topology
open scoped NNReal

noncomputable section

namespace Lightlike.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **First-order expansion of a trajectory in its initial point.** Let `γ` and `γ'` be solutions
of `ẋ = V x` on `[-T, T]` in a convex set `s` on which `V` has the derivative `V'` with
`‖V'‖ ≤ K`, and let `U` solve the variational equation `U̇ = V'(γ t) ∘ U`, `U 0 = id`. If `V'`
moves by at most `η` within distance `δ` of the trajectory `γ`, and the initial points are closer
than `δ e^{-K T}`, then
`‖γ' t - γ t - U t (γ' 0 - γ 0)‖ ≤ η ‖γ' 0 - γ 0‖ e^{K T} T e^{K T}`. -/
theorem norm_sub_sub_le_of_trajectories {V : E → E} {V' : E → E →L[ℝ] E} {s : Set E} {K : ℝ≥0}
    {T η δ : ℝ} {γ γ' : ℝ → E} {U : ℝ → E →L[ℝ] E}
    (hs : Convex ℝ s) (hV : ∀ y ∈ s, HasFDerivAt V (V' y) y) (hK : ∀ y ∈ s, ‖V' y‖ ≤ K)
    (hη : 0 ≤ η)
    (hγ : ∀ t ∈ Icc (-T) T, HasDerivWithinAt γ (V (γ t)) (Icc (-T) T) t)
    (hγs : ∀ t ∈ Icc (-T) T, γ t ∈ s)
    (hγ' : ∀ t ∈ Icc (-T) T, HasDerivWithinAt γ' (V (γ' t)) (Icc (-T) T) t)
    (hγ's : ∀ t ∈ Icc (-T) T, γ' t ∈ s)
    (hU : ∀ t ∈ Icc (-T) T, HasDerivWithinAt U ((V' (γ t)).comp (U t)) (Icc (-T) T) t)
    (hU0 : U 0 = ContinuousLinearMap.id ℝ E)
    (hunif : ∀ t ∈ Icc (-T) T, ∀ w ∈ s, ‖w - γ t‖ < δ → ‖V' w - V' (γ t)‖ ≤ η)
    (hsmall : ‖γ' 0 - γ 0‖ * Real.exp (K * T) < δ) :
    ∀ t ∈ Icc (-T) T, ‖γ' t - γ t - U t (γ' 0 - γ 0)‖ ≤
      η * (‖γ' 0 - γ 0‖ * Real.exp (K * T)) * T * Real.exp (K * T) := by
  set h : E := γ' 0 - γ 0 with hh
  have hLip : LipschitzOnWith K V s :=
    hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun y hy => (hV y hy).hasFDerivWithinAt)
      (fun y hy => by exact_mod_cast hK y hy)
  have hdist : ∀ t ∈ Icc (-T) T, ‖γ' t - γ t‖ ≤ ‖h‖ * Real.exp (K * T) := by
    intro t ht
    refine (norm_sub_le_of_trajectories hLip hγ' hγ's hγ hγs t ht).trans ?_
    have : Real.exp (K * |t|) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_le.2 ht) K.2)
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  have hδ : 0 < δ := lt_of_le_of_lt (by positivity) hsmall
  refine norm_le_of_deriv_le (f := fun t => γ' t - γ t - U t h)
    (f' := fun t => V (γ' t) - V (γ t) - ((V' (γ t)).comp (U t)) h) (K := K)
    (ε := η * (‖h‖ * Real.exp (K * T))) K.2
    (mul_nonneg hη (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)) (fun t ht => ?_) ?_
    (fun t ht => ?_)
  · have h1 := (hU t ht).clm_apply (hasDerivWithinAt_const t (Icc (-T) T) h)
    simp only [map_zero, add_zero] at h1
    exact ((hγ' t ht).sub (hγ t ht)).sub h1
  · simp [hU0, hh]
  · -- the derivative is `V'(γ t) z + R` with `‖R‖ ≤ η ‖γ' t - γ t‖`
    have hR : ‖V (γ' t) - V (γ t) - V' (γ t) (γ' t - γ t)‖ ≤ η * ‖γ' t - γ t‖ := by
      have hconv : Convex ℝ (s ∩ ball (γ t) δ) := hs.inter (convex_ball _ _)
      refine hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := V) (f' := V')
        (fun y hy => (hV y hy.1).hasFDerivWithinAt) (fun y hy => ?_) ⟨hγs t ht, mem_ball_self hδ⟩
        ⟨hγ's t ht, ?_⟩
      · exact hunif t ht y hy.1 (mem_ball_iff_norm.1 hy.2)
      · exact mem_ball_iff_norm.2 (lt_of_le_of_lt (hdist t ht) hsmall)
    have hsplit : V (γ' t) - V (γ t) - ((V' (γ t)).comp (U t)) h =
        V' (γ t) (γ' t - γ t - U t h) + (V (γ' t) - V (γ t) - V' (γ t) (γ' t - γ t)) := by
      simp only [ContinuousLinearMap.comp_apply, map_sub]
      abel
    rw [hsplit]
    calc ‖V' (γ t) (γ' t - γ t - U t h) + (V (γ' t) - V (γ t) - V' (γ t) (γ' t - γ t))‖
        ≤ ‖V' (γ t)‖ * ‖γ' t - γ t - U t h‖ + η * ‖γ' t - γ t‖ :=
          (norm_add_le _ _).trans (add_le_add ((V' (γ t)).le_opNorm _) hR)
      _ ≤ K * ‖γ' t - γ t - U t h‖ + η * (‖h‖ * Real.exp (K * T)) :=
          add_le_add (mul_le_mul_of_nonneg_right (hK _ (hγs t ht)) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (hdist t ht) hη)

/-- `Φ` is a flow box of the vector field `V` about `x₀`: for every initial point `x` in the open
ball of radius `r` about `x₀`, the curve `t ↦ Φ t x` solves `ẋ = V x` on `[-T, T]` with
`Φ 0 x = x` and stays in the open ball of radius `a` about `x₀`; on that ball `V` is differentiable
with a continuous derivative of norm at most `K`; and `K T ≤ 1/2` (a short-time condition, used
to solve the variational equation with Mathlib's Picard–Lindelöf theorem). -/
structure IsFlowBox (V : E → E) (x₀ : E) (a r T : ℝ) (K : ℝ≥0) (Φ : ℝ → E → E) : Prop where
  /-- The radius of the ball of initial points is positive. -/
  r_pos : 0 < r
  /-- The time is positive. -/
  T_pos : 0 < T
  /-- The short-time condition. -/
  mul_le : K * T ≤ 1 / 2
  /-- The field is differentiable on the large ball. -/
  differentiableAt : ∀ y ∈ ball x₀ a, DifferentiableAt ℝ V y
  /-- The derivative of the field is continuous on the large ball. -/
  continuousOn_fderiv : ContinuousOn (fderiv ℝ V) (ball x₀ a)
  /-- The derivative of the field is bounded by `K` on the large ball. -/
  norm_fderiv_le : ∀ y ∈ ball x₀ a, ‖fderiv ℝ V y‖ ≤ K
  /-- The flow at time `0` is the identity. -/
  flow_zero : ∀ x ∈ ball x₀ r, Φ 0 x = x
  /-- Trajectories stay in the large ball. -/
  flow_mem : ∀ x ∈ ball x₀ r, ∀ t ∈ Icc (-T) T, Φ t x ∈ ball x₀ a
  /-- Trajectories solve the equation. -/
  hasDerivAt : ∀ x ∈ ball x₀ r, ∀ t ∈ Icc (-T) T, HasDerivAt (fun t => Φ t x) (V (Φ t x)) t

namespace IsFlowBox

variable {V : E → E} {x₀ : E} {a r T : ℝ} {K : ℝ≥0} {Φ : ℝ → E → E}

lemma zero_mem (h : IsFlowBox V x₀ a r T K Φ) : (0 : ℝ) ∈ Icc (-T) T :=
  ⟨by linarith [h.T_pos], h.T_pos.le⟩

lemma hasDerivWithinAt (h : IsFlowBox V x₀ a r T K Φ) {x : E} (hx : x ∈ ball x₀ r) :
    ∀ t ∈ Icc (-T) T, HasDerivWithinAt (fun t => Φ t x) (V (Φ t x)) (Icc (-T) T) t :=
  fun t ht => (h.hasDerivAt x hx t ht).hasDerivWithinAt

lemma lipschitzOnWith (h : IsFlowBox V x₀ a r T K Φ) : LipschitzOnWith K V (ball x₀ a) :=
  (convex_ball x₀ a).lipschitzOnWith_of_nnnorm_fderiv_le h.differentiableAt
    (fun y hy => by exact_mod_cast h.norm_fderiv_le y hy)

/-- The initial points lie in the large ball. -/
lemma initial_mem (h : IsFlowBox V x₀ a r T K Φ) {x : E} (hx : x ∈ ball x₀ r) : x ∈ ball x₀ a := by
  simpa [h.flow_zero x hx] using h.flow_mem x hx 0 h.zero_mem

/-- The flow of a flow box is Lipschitz in the initial point, with constant `e^{K T}`. -/
theorem norm_flow_sub_le (h : IsFlowBox V x₀ a r T K Φ) {x y : E} (hx : x ∈ ball x₀ r)
    (hy : y ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    ‖Φ t x - Φ t y‖ ≤ ‖x - y‖ * Real.exp (K * T) := by
  have h1 := norm_sub_le_of_trajectories h.lipschitzOnWith (h.hasDerivWithinAt hx) (h.flow_mem x hx)
    (h.hasDerivWithinAt hy) (h.flow_mem y hy) t ht
  rw [h.flow_zero x hx, h.flow_zero y hy] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_le.2 ht) K.2)

/-- Uniform continuity of `DV` near a trajectory: for `η > 0` there is `δ > 0` such that `DV`
moves by at most `η` within distance `δ` of any point of the trajectory of `x`. -/
lemma exists_delta (h : IsFlowBox V x₀ a r T K Φ) {x : E} (hx : x ∈ ball x₀ r) {η : ℝ}
    (hη : 0 < η) :
    ∃ δ > 0, ∀ t ∈ Icc (-T) T, ∀ w : E, ‖w - Φ t x‖ < δ →
      ‖fderiv ℝ V w - fderiv ℝ V (Φ t x)‖ ≤ η := by
  have hcont : ContinuousOn (fun t => Φ t x) (Icc (-T) T) := fun t ht =>
    (h.hasDerivAt x hx t ht).continuousAt.continuousWithinAt
  have hcomp : IsCompact ((fun t => Φ t x) '' Icc (-T) T) :=
    isCompact_Icc.image_of_continuousOn hcont
  have hat : ∀ y ∈ (fun t => Φ t x) '' Icc (-T) T, ContinuousAt (fderiv ℝ V) y := by
    rintro y ⟨t, ht, rfl⟩
    exact h.continuousOn_fderiv.continuousAt (isOpen_ball.mem_nhds (h.flow_mem x hx t ht))
  obtain ⟨δ, hδ, H⟩ := Metric.mem_uniformity_dist.1
    (hcomp.uniformContinuousAt_of_continuousAt (fderiv ℝ V) hat (dist_mem_uniformity hη))
  refine ⟨δ, hδ, fun t ht w hw => ?_⟩
  have h1 : dist (Φ t x) w < δ := by rw [dist_comm, dist_eq_norm]; exact hw
  have h2 := H h1 ⟨t, ht, rfl⟩
  simp only [Set.mem_ofPred_eq] at h2
  rw [dist_comm, dist_eq_norm] at h2
  exact h2.le

/-- **The derivative of a flow in the initial point.** In a flow box, a solution `U` of the
variational equation `U̇ = DV(Φ t x) ∘ U`, `U 0 = id`, along the trajectory of `x` is the
derivative of `x ↦ Φ t x`: Teschl, Theorem 2.10, case `k = 1`. -/
theorem hasFDerivAt_of_variational (h : IsFlowBox V x₀ a r T K Φ) {x : E} (hx : x ∈ ball x₀ r)
    {U : ℝ → E →L[ℝ] E} (hU0 : U 0 = ContinuousLinearMap.id ℝ E)
    (hU : ∀ t ∈ Icc (-T) T,
      HasDerivWithinAt U ((fderiv ℝ V (Φ t x)).comp (U t)) (Icc (-T) T) t)
    {t : ℝ} (ht : t ∈ Icc (-T) T) : HasFDerivAt (Φ t) (U t) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hT := h.T_pos
  set e : ℝ := Real.exp (K * T) with he
  have he0 : 0 < e := Real.exp_pos _
  have hne : e * T * e ≠ 0 := (mul_pos (mul_pos he0 hT) he0).ne'
  set η : ℝ := c / (e * T * e) with hη
  have hη0 : 0 < η := div_pos hc (mul_pos (mul_pos he0 hT) he0)
  obtain ⟨δ, hδ, H⟩ := h.exists_delta hx hη0
  have hr : 0 < r - dist x x₀ := sub_pos.2 (mem_ball.1 hx)
  have hδe : 0 < δ / e := div_pos hδ he0
  filter_upwards [Metric.ball_mem_nhds (0 : E) hr, Metric.ball_mem_nhds (0 : E) hδe] with k hk1 hk2
  rw [mem_ball_zero_iff] at hk1 hk2
  have hxk : x + k ∈ ball x₀ r := by
    rw [mem_ball]
    calc dist (x + k) x₀ ≤ dist (x + k) x + dist x x₀ := dist_triangle _ _ _
      _ = ‖k‖ + dist x x₀ := by simp [dist_eq_norm]
      _ < r := by linarith
  have e0 : Φ 0 (x + k) - Φ 0 x = k := by
    rw [h.flow_zero _ hxk, h.flow_zero _ hx]; abel
  have hsmall : ‖Φ 0 (x + k) - Φ 0 x‖ * Real.exp (K * T) < δ := by
    rw [e0]
    calc ‖k‖ * e < δ / e * e := mul_lt_mul_of_pos_right hk2 he0
      _ = δ := div_mul_cancel₀ δ he0.ne'
  have key := norm_sub_sub_le_of_trajectories (V := V) (V' := fderiv ℝ V) (γ := fun t => Φ t x)
    (γ' := fun t => Φ t (x + k)) (U := U) (η := η) (δ := δ) (convex_ball x₀ a)
    (fun y hy => (h.differentiableAt y hy).hasFDerivAt) h.norm_fderiv_le hη0.le
    (h.hasDerivWithinAt hx) (h.flow_mem x hx) (h.hasDerivWithinAt hxk) (h.flow_mem _ hxk) hU hU0
    (fun t ht w _ hw => H t ht w hw) hsmall t ht
  simp only [e0] at key
  calc ‖Φ t (x + k) - Φ t x - U t k‖ ≤ η * (‖k‖ * e) * T * e := key
    _ = η * (e * T * e) * ‖k‖ := by ring
    _ = c * ‖k‖ := by rw [hη, div_mul_cancel₀ _ hne]

variable [CompleteSpace E]

/-- In a flow box the variational equation along each trajectory has a solution. -/
theorem exists_variational (h : IsFlowBox V x₀ a r T K Φ) {x : E} (hx : x ∈ ball x₀ r) :
    ∃ U : ℝ → E →L[ℝ] E, U 0 = ContinuousLinearMap.id ℝ E ∧ ∀ t ∈ Icc (-T) T,
      HasDerivWithinAt U ((fderiv ℝ V (Φ t x)).comp (U t)) (Icc (-T) T) t := by
  have hcont : ContinuousOn (fun t => Φ t x) (Icc (-T) T) := fun t ht =>
    (h.hasDerivAt x hx t ht).continuousAt.continuousWithinAt
  have hA : ContinuousOn
      (fun t => ContinuousLinearMap.compL ℝ E E E (fderiv ℝ V (Φ t x))) (Icc (-T) T) :=
    (ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn
      (h.continuousOn_fderiv.comp hcont (fun t ht => h.flow_mem x hx t ht))
  have hKb : ∀ t ∈ Icc (-T) T, ‖ContinuousLinearMap.compL ℝ E E E (fderiv ℝ V (Φ t x))‖ ≤ K := by
    intro t ht
    calc ‖ContinuousLinearMap.compL ℝ E E E (fderiv ℝ V (Φ t x))‖
        ≤ ‖ContinuousLinearMap.compL ℝ E E E‖ * ‖fderiv ℝ V (Φ t x)‖ :=
          (ContinuousLinearMap.compL ℝ E E E).le_opNorm _
      _ ≤ 1 * K := mul_le_mul (ContinuousLinearMap.norm_compL_le ℝ E E E)
          (h.norm_fderiv_le _ (h.flow_mem x hx t ht)) (norm_nonneg _) zero_le_one
      _ = K := one_mul _
  obtain ⟨U, hU0, hU⟩ := exists_linear_solution h.T_pos.le h.mul_le hA hKb
    (ContinuousLinearMap.id ℝ E)
  exact ⟨U, hU0, fun t ht => hU t ht⟩

/-- **In a flow box the flow is differentiable in the initial point.** -/
theorem differentiableAt_flow (h : IsFlowBox V x₀ a r T K Φ) {x : E} (hx : x ∈ ball x₀ r)
    {t : ℝ} (ht : t ∈ Icc (-T) T) : DifferentiableAt ℝ (Φ t) x := by
  obtain ⟨U, hU0, hU⟩ := h.exists_variational hx
  exact (h.hasFDerivAt_of_variational hx hU0 hU ht).differentiableAt

/-- **The first variational equation.** In a flow box the derivative `D_x Φ_t` of the flow in the
initial point solves `d/dt D_x Φ_t = DV(Φ_t x) ∘ D_x Φ_t` on `[-T, T]`: Teschl, equation (2.49). -/
theorem hasDerivWithinAt_fderiv_flow (h : IsFlowBox V x₀ a r T K Φ) {x : E} (hx : x ∈ ball x₀ r)
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    HasDerivWithinAt (fun t => fderiv ℝ (Φ t) x)
      ((fderiv ℝ V (Φ t x)).comp (fderiv ℝ (Φ t) x)) (Icc (-T) T) t := by
  obtain ⟨U, hU0, hU⟩ := h.exists_variational hx
  have heq : ∀ s ∈ Icc (-T) T, fderiv ℝ (Φ s) x = U s := fun s hs =>
    (h.hasFDerivAt_of_variational hx hU0 hU hs).fderiv
  rw [heq t ht]
  exact (hU t ht).congr heq (heq t ht)

/-- The variational equation at interior times, with a two-sided derivative. -/
theorem hasDerivAt_fderiv_flow (h : IsFlowBox V x₀ a r T K Φ) {x : E} (hx : x ∈ ball x₀ r)
    {t : ℝ} (ht : t ∈ Ioo (-T) T) :
    HasDerivAt (fun t => fderiv ℝ (Φ t) x)
      ((fderiv ℝ V (Φ t x)).comp (fderiv ℝ (Φ t) x)) t :=
  (h.hasDerivWithinAt_fderiv_flow hx (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- The derivative of the flow at time `0` is the identity. -/
theorem fderiv_flow_zero (h : IsFlowBox V x₀ a r T K Φ) {x : E} (hx : x ∈ ball x₀ r) :
    fderiv ℝ (Φ 0) x = ContinuousLinearMap.id ℝ E := by
  obtain ⟨U, hU0, hU⟩ := h.exists_variational hx
  rw [(h.hasFDerivAt_of_variational hx hU0 hU h.zero_mem).fderiv, hU0]

/-- The operator form of the variational equation, as a linear equation in `E →L[ℝ] E`. -/
lemma hasDerivWithinAt_fderiv_flow' (h : IsFlowBox V x₀ a r T K Φ) {x : E} (hx : x ∈ ball x₀ r)
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    HasDerivWithinAt (fun t => fderiv ℝ (Φ t) x)
      (ContinuousLinearMap.compL ℝ E E E (fderiv ℝ V (Φ t x)) (fderiv ℝ (Φ t) x))
      (Icc (-T) T) t :=
  h.hasDerivWithinAt_fderiv_flow hx ht

omit [CompleteSpace E] in
/-- The coefficient of the operator form of the variational equation is bounded by `K`. -/
lemma norm_compL_fderiv_le (h : IsFlowBox V x₀ a r T K Φ) {x : E} (hx : x ∈ ball x₀ r)
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    ‖ContinuousLinearMap.compL ℝ E E E (fderiv ℝ V (Φ t x))‖ ≤ K :=
  calc ‖ContinuousLinearMap.compL ℝ E E E (fderiv ℝ V (Φ t x))‖
      ≤ ‖ContinuousLinearMap.compL ℝ E E E‖ * ‖fderiv ℝ V (Φ t x)‖ :=
        (ContinuousLinearMap.compL ℝ E E E).le_opNorm _
    _ ≤ 1 * K := mul_le_mul (ContinuousLinearMap.norm_compL_le ℝ E E E)
        (h.norm_fderiv_le _ (h.flow_mem x hx t ht)) (norm_nonneg _) zero_le_one
    _ = K := one_mul _

/-- The derivative of the flow is bounded by `e^{K T}`. -/
theorem norm_fderiv_flow_le (h : IsFlowBox V x₀ a r T K Φ) {x : E} (hx : x ∈ ball x₀ r)
    {t : ℝ} (ht : t ∈ Icc (-T) T) : ‖fderiv ℝ (Φ t) x‖ ≤ Real.exp (K * T) := by
  have h1 := norm_le_of_linear (A := fun t => ContinuousLinearMap.compL ℝ E E E (fderiv ℝ V (Φ t x)))
    (u := fun t => fderiv ℝ (Φ t) x) (K := K) (fun t ht => h.norm_compL_fderiv_le hx ht)
    (fun t ht => h.hasDerivWithinAt_fderiv_flow' hx ht) t ht
  simp only [h.fderiv_flow_zero hx] at h1
  calc ‖fderiv ℝ (Φ t) x‖ ≤ ‖ContinuousLinearMap.id ℝ E‖ * Real.exp (K * |t|) := h1
    _ ≤ 1 * Real.exp (K * T) := mul_le_mul ContinuousLinearMap.norm_id_le
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_le.2 ht) K.2)) (Real.exp_pos _).le
        zero_le_one
    _ = Real.exp (K * T) := one_mul _

/-- The derivative of the flow is continuous in the initial point, uniformly in the time: for
`ε > 0` there is `δ > 0` with `‖D_x Φ_t (y) - D_x Φ_t (x)‖ ≤ ε` for all `t ∈ [-T, T]` and all `y`
in the ball of initial points with `‖y - x‖ < δ`. -/
theorem exists_delta_fderiv_flow (h : IsFlowBox V x₀ a r T K Φ) {x : E} (hx : x ∈ ball x₀ r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ ball x₀ r, ‖y - x‖ < δ → ∀ t ∈ Icc (-T) T,
      ‖fderiv ℝ (Φ t) y - fderiv ℝ (Φ t) x‖ ≤ ε := by
  have hT := h.T_pos
  set e : ℝ := Real.exp (K * T) with he
  have he0 : 0 < e := Real.exp_pos _
  have hne : e * T * e ≠ 0 := (mul_pos (mul_pos he0 hT) he0).ne'
  set η : ℝ := ε / (e * T * e) with hη
  have hη0 : 0 < η := div_pos hε (mul_pos (mul_pos he0 hT) he0)
  obtain ⟨δ, hδ, H⟩ := h.exists_delta hx hη0
  refine ⟨δ / e, div_pos hδ he0, fun y hy hyx t ht => ?_⟩
  have hAB : ∀ t ∈ Icc (-T) T,
      ‖ContinuousLinearMap.compL ℝ E E E (fderiv ℝ V (Φ t y)) -
        ContinuousLinearMap.compL ℝ E E E (fderiv ℝ V (Φ t x))‖ ≤ η := by
    intro t ht
    have h1 : ‖Φ t y - Φ t x‖ < δ := by
      calc ‖Φ t y - Φ t x‖ ≤ ‖y - x‖ * e := h.norm_flow_sub_le hy hx ht
        _ < δ / e * e := mul_lt_mul_of_pos_right hyx he0
        _ = δ := div_mul_cancel₀ δ he0.ne'
    rw [← map_sub]
    calc ‖ContinuousLinearMap.compL ℝ E E E (fderiv ℝ V (Φ t y) - fderiv ℝ V (Φ t x))‖
        ≤ ‖ContinuousLinearMap.compL ℝ E E E‖ * ‖fderiv ℝ V (Φ t y) - fderiv ℝ V (Φ t x)‖ :=
          (ContinuousLinearMap.compL ℝ E E E).le_opNorm _
      _ ≤ 1 * η := mul_le_mul (ContinuousLinearMap.norm_compL_le ℝ E E E) (H t ht _ h1) (norm_nonneg _)
          zero_le_one
      _ = η := one_mul _
  have key := norm_sub_le_of_linear
    (A := fun t => ContinuousLinearMap.compL ℝ E E E (fderiv ℝ V (Φ t y)))
    (B := fun t => ContinuousLinearMap.compL ℝ E E E (fderiv ℝ V (Φ t x)))
    (u := fun t => fderiv ℝ (Φ t) y) (v := fun t => fderiv ℝ (Φ t) x) (K := K) (η := η) (M := e)
    K.2 hη0.le he0.le (fun t ht => h.norm_compL_fderiv_le hx ht) hAB
    (fun t ht => h.hasDerivWithinAt_fderiv_flow' hy ht) (fun t ht => h.norm_fderiv_flow_le hy ht)
    (fun t ht => h.hasDerivWithinAt_fderiv_flow' hx ht)
    (by rw [h.fderiv_flow_zero hy, h.fderiv_flow_zero hx]) t ht
  calc ‖fderiv ℝ (Φ t) y - fderiv ℝ (Φ t) x‖ ≤ η * e * T * e := key
    _ = η * (e * T * e) := by ring
    _ = ε := by rw [hη, div_mul_cancel₀ _ hne]

/-- **The derivative of the flow in the initial point is continuous in `(t, x)`.** -/
theorem continuousOn_fderiv_flow (h : IsFlowBox V x₀ a r T K Φ) :
    ContinuousOn (fun p : ℝ × E => fderiv ℝ (Φ p.1) p.2) (Icc (-T) T ×ˢ ball x₀ r) := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, H₁⟩ := h.exists_delta_fderiv_flow hx (half_pos hε)
  have hct : ContinuousWithinAt (fun t => fderiv ℝ (Φ t) x) (Icc (-T) T) t :=
    (h.hasDerivWithinAt_fderiv_flow hx ht).continuousWithinAt
  obtain ⟨δ₂, hδ₂, H₂⟩ := Metric.continuousWithinAt_iff.1 hct (ε / 2) (half_pos hε)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  rintro ⟨s, y⟩ ⟨hs, hy⟩ hd
  rw [Prod.dist_eq, max_lt_iff] at hd
  have h1 : ‖fderiv ℝ (Φ s) y - fderiv ℝ (Φ s) x‖ ≤ ε / 2 :=
    H₁ y hy (by rw [← dist_eq_norm]; exact lt_of_lt_of_le hd.2 (min_le_left _ _)) s hs
  have h2 : dist (fderiv ℝ (Φ s) x) (fderiv ℝ (Φ t) x) < ε / 2 :=
    H₂ hs (lt_of_lt_of_le hd.1 (min_le_right _ _))
  calc dist (fderiv ℝ (Φ s) y) (fderiv ℝ (Φ t) x)
      ≤ dist (fderiv ℝ (Φ s) y) (fderiv ℝ (Φ s) x) + dist (fderiv ℝ (Φ s) x) (fderiv ℝ (Φ t) x) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        rw [dist_eq_norm]
        exact add_lt_add_of_le_of_lt h1 h2
    _ = ε := add_halves ε

end IsFlowBox

end Lightlike.ODE
