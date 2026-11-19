import Lightlike.ODE.FlowDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Existence of flow boxes, and the local flow of a `C¹` field is `C¹` in the initial point

A vector field that is `C¹` at a point `x₀` of a real Banach space has a flow box about `x₀`
(`Lightlike.ODE.exists_isFlowBox`), built from Mathlib's Picard–Lindelöf theorem. With the results
of `Lightlike.ODE.FlowDeriv` this gives the differentiable dependence of the local flow on the
initial point (`Lightlike.ODE.exists_flow_differentiable`).

## Main results

* `Lightlike.ODE.exists_isFlowBox`: flow boxes exist, with any sufficiently small large ball.
* `Lightlike.ODE.exists_flow_differentiable`: a `C¹` field has a local flow `Φ` about each point
  such that `x ↦ Φ t x` is differentiable, its derivative solves the first variational equation
  `d/dt D_x Φ_t = DV(Φ_t x) ∘ D_x Φ_t` with `D_x Φ_0 = id`, and is continuous in `(t, x)`.

## References

* `teschl-2012`: G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, Theorem 2.10
  and equation (2.49), pages 46–47 of the author's version. Differences from the source, all in
  the weaker direction: the field is autonomous (the source's is time-dependent), of class `C¹`
  (the source treats `C^k`), and the regularity proved is differentiability in the initial point
  with a derivative continuous in `(t, x)` (the source has `C^k` jointly in the time, the initial
  time and the initial point). The space is a real Banach space instead of `ℝⁿ`.
-/

open Set Metric Filter Topology Function
open scoped NNReal

noncomputable section

namespace Lightlike.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A flow box can be shrunk in the radius of initial points and in the time. -/
theorem IsFlowBox.mono {V : E → E} {x₀ : E} {a r T : ℝ} {K : ℝ≥0} {Φ : ℝ → E → E}
    (h : IsFlowBox V x₀ a r T K Φ) {r' T' : ℝ} (hr' : 0 < r') (hrr : r' ≤ r) (hT' : 0 < T')
    (hTT : T' ≤ T) : IsFlowBox V x₀ a r' T' K Φ := by
  have hb : ball x₀ r' ⊆ ball x₀ r := ball_subset_ball hrr
  have hI : Icc (-T') T' ⊆ Icc (-T) T := Icc_subset_Icc (by linarith) hTT
  exact
    { r_pos := hr'
      T_pos := hT'
      mul_le := (mul_le_mul_of_nonneg_left hTT K.2).trans h.mul_le
      differentiableAt := h.differentiableAt
      continuousOn_fderiv := h.continuousOn_fderiv
      norm_fderiv_le := h.norm_fderiv_le
      flow_zero := fun x hx => h.flow_zero x (hb hx)
      flow_mem := fun x hx t ht => h.flow_mem x (hb hx) t (hI ht)
      hasDerivAt := fun x hx t ht => h.hasDerivAt x (hb hx) t (hI ht) }

/-- **Existence of flow boxes.** A vector field that is `C¹` at `x₀` has a flow box about `x₀`
with large ball of any sufficiently small radius `a`. -/
theorem exists_isFlowBox {V : E → E} {x₀ : E} (hV : ContDiffAt ℝ 1 V x₀) :
    ∃ A > 0, ∀ a, 0 < a → a ≤ A →
      ∃ (r T : ℝ) (K : ℝ≥0) (Φ : ℝ → E → E), IsFlowBox V x₀ a r T K Φ := by
  classical
  have h1 : ∀ᶠ y in 𝓝 x₀, ContDiffAt ℝ 1 V y := hV.eventually (by simp)
  have hc : ContinuousAt (fderiv ℝ V) x₀ :=
    (hV.fderiv_right (m := 0) (by simp)).continuousAt
  have h2 : ∀ᶠ y in 𝓝 x₀, ‖fderiv ℝ V y‖ < ‖fderiv ℝ V x₀‖ + 1 :=
    hc.norm.tendsto.eventually (eventually_lt_nhds (lt_add_one _))
  obtain ⟨a₁, ha₁, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  refine ⟨a₁, ha₁, fun a ha0 haA => ?_⟩
  have hsub : ball x₀ a ⊆ ball x₀ a₁ := ball_subset_ball haA
  set K : ℝ≥0 := ‖fderiv ℝ V x₀‖₊ + 1 with hK
  have hdiff : ∀ y ∈ ball x₀ a, DifferentiableAt ℝ V y := fun y hy =>
    (hball y (hsub hy)).1.differentiableAt (by simp)
  have hcont : ContinuousOn (fderiv ℝ V) (ball x₀ a) := fun y hy =>
    (((hball y (hsub hy)).1.fderiv_right (m := 0) (by simp)).continuousAt).continuousWithinAt
  have hbound : ∀ y ∈ ball x₀ a, ‖fderiv ℝ V y‖ ≤ K := fun y hy => by
    have := (hball y (hsub hy)).2.le
    simpa [hK] using this
  have hLip : LipschitzOnWith K V (ball x₀ a) :=
    (convex_ball x₀ a).lipschitzOnWith_of_nnnorm_fderiv_le hdiff
      (fun y hy => by exact_mod_cast hbound y hy)
  -- the Picard–Lindelöf data
  set aP : ℝ≥0 := ⟨a / 2, (half_pos ha0).le⟩ with haP
  set rP : ℝ≥0 := ⟨a / 4, by linarith⟩ with hrP
  have haPc : (aP : ℝ) = a / 2 := rfl
  have hrPc : (rP : ℝ) = a / 4 := rfl
  set L : ℝ≥0 := ‖V x₀‖₊ + K * aP with hL
  have hcb : closedBall x₀ (aP : ℝ) ⊆ ball x₀ a :=
    closedBall_subset_ball (by rw [haPc]; linarith)
  have hb : ∀ x ∈ closedBall x₀ (aP : ℝ), ‖V x‖ ≤ L := by
    intro x hx
    have hx0 : x₀ ∈ ball x₀ a := mem_ball_self ha0
    have h3 : ‖V x - V x₀‖ ≤ K * ‖x - x₀‖ := hLip.norm_sub_le (hcb hx) hx0
    have h4 : ‖x - x₀‖ ≤ aP := mem_closedBall_iff_norm.1 hx
    calc ‖V x‖ = ‖V x₀ + (V x - V x₀)‖ := by simp
      _ ≤ ‖V x₀‖ + ‖V x - V x₀‖ := norm_add_le _ _
      _ ≤ ‖V x₀‖ + K * aP := by
        have : (K : ℝ) * ‖x - x₀‖ ≤ K * aP := mul_le_mul_of_nonneg_left h4 K.2
        linarith
      _ = L := by simp [hL]
  set T₂ : ℝ := min (a / (4 * (L + 1))) (1 / (2 * (K + 1))) with hT₂
  have hL1 : (0 : ℝ) < 4 * (L + 1) := by positivity
  have hK1 : (0 : ℝ) < 2 * (K + 1) := by positivity
  have hT₂0 : 0 < T₂ := lt_min (div_pos ha0 hL1) (div_pos one_pos hK1)
  have hLT : (L : ℝ) * T₂ ≤ a / 4 := by
    have h5 : (L : ℝ) * T₂ ≤ L * (a / (4 * (L + 1))) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) L.2
    have h6 : (L : ℝ) * (a / (4 * (L + 1))) ≤ a / 4 := by
      have hL0 : (0 : ℝ) ≤ L := L.2
      rw [← mul_div_assoc, div_le_iff₀ hL1]
      nlinarith
    linarith
  have hKT : (K : ℝ) * T₂ ≤ 1 / 2 := by
    have h5 : (K : ℝ) * T₂ ≤ K * (1 / (2 * (K + 1))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) K.2
    have h6 : (K : ℝ) * (1 / (2 * (K + 1))) ≤ 1 / 2 := by
      have hK0 : (0 : ℝ) ≤ K := K.2
      rw [← mul_div_assoc, div_le_iff₀ hK1]
      nlinarith
    linarith
  have h0mem : (0 : ℝ) ∈ Icc (-T₂) T₂ := ⟨by linarith, hT₂0.le⟩
  have hPL : IsPicardLindelof (fun _ => V) (tmin := -T₂) (tmax := T₂) ⟨0, h0mem⟩ x₀ aP rP L K := by
    refine IsPicardLindelof.of_time_independent hb (hLip.mono hcb) ?_
    have hmax : max (T₂ - (0 : ℝ)) ((0 : ℝ) - -T₂) = T₂ := by simp
    show (L : ℝ) * max (T₂ - (0 : ℝ)) ((0 : ℝ) - -T₂) ≤ (aP : ℝ) - (rP : ℝ)
    rw [hmax]
    have : (aP : ℝ) - (rP : ℝ) = a / 4 := by rw [haPc, hrPc]; ring
    linarith
  -- the flow, from the fixed points of the Picard map
  have H : ∀ x (hx : x ∈ closedBall x₀ (rP : ℝ)),
      ∃ α : _root_.ODE.FunSpace (⟨0, h0mem⟩ : Icc (-T₂) T₂) x₀ rP L,
        IsFixedPt (_root_.ODE.FunSpace.next hPL hx) α :=
    fun x hx => _root_.ODE.FunSpace.exists_isFixedPt_next hPL hx
  choose α hα using H
  set Φ : ℝ → E → E := fun t x =>
    if hx : x ∈ closedBall x₀ (rP : ℝ) then (α x hx).compProj t else x₀ with hΦ
  have hbr : ball x₀ (a / 4) ⊆ closedBall x₀ (rP : ℝ) := by
    intro x hx
    have : dist x x₀ < a / 4 := hx
    exact mem_closedBall.2 (by rw [hrPc]; exact this.le)
  refine ⟨a / 4, T₂ / 2, K, Φ, ?_⟩
  have hI : Icc (-(T₂ / 2)) (T₂ / 2) ⊆ Ioo (-T₂) T₂ := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine
    { r_pos := by linarith
      T_pos := half_pos hT₂0
      mul_le := by
        have hK0 : (0 : ℝ) ≤ K := K.2
        nlinarith
      differentiableAt := hdiff
      continuousOn_fderiv := hcont
      norm_fderiv_le := hbound
      flow_zero := fun x hx => ?_
      flow_mem := fun x hx t _ => ?_
      hasDerivAt := fun x hx t ht => ?_ }
  · have hx' := hbr hx
    simp only [hΦ, dite_eq_left hx']
    have h7 : (α x hx').compProj ((⟨0, h0mem⟩ : Icc (-T₂) T₂) : ℝ) = (α x hx') ⟨0, h0mem⟩ :=
      _root_.ODE.FunSpace.compProj_val
    have h8 : (α x hx') ⟨0, h0mem⟩ = x := by
      rw [← hα x hx']
      exact _root_.ODE.FunSpace.next_apply₀ hPL hx' _
    exact h7.trans h8
  · have hx' := hbr hx
    simp only [hΦ, dite_eq_left hx']
    exact hcb ((α x hx').compProj_mem_closedBall hPL.mul_max_le)
  · have hx' := hbr hx
    have ht' : t ∈ Icc (-T₂) T₂ := Ioo_subset_Icc_self (hI ht)
    have hder : HasDerivWithinAt (α x hx').compProj (V ((α x hx').compProj t)) (Icc (-T₂) T₂) t := by
      refine (_root_.ODE.hasDerivWithinAt_picard_Icc (f := fun _ => V) (t₀ := 0) h0mem
        hPL.continuousOn_uncurry (α x hx').continuous_compProj.continuousOn
        (fun _ _ => (α x hx').compProj_mem_closedBall hPL.mul_max_le) x ht').congr_of_mem ?_ ht'
      intro t' ht'
      nth_rw 1 [← hα x hx']
      rw [_root_.ODE.FunSpace.compProj_of_mem ht', _root_.ODE.FunSpace.next_apply]
    have hder' : HasDerivAt (α x hx').compProj (V ((α x hx').compProj t)) t :=
      hder.hasDerivAt (Icc_mem_nhds (hI ht).1 (hI ht).2)
    have hfun : (fun t => Φ t x) = (α x hx').compProj := by
      funext s
      simp only [hΦ, dite_eq_left hx']
    rw [hfun]
    simpa only [hΦ, dite_eq_left hx'] using hder'

/-- **The local flow of a `C¹` vector field is differentiable in the initial point, and its
derivative solves the first variational equation** (Teschl, Theorem 2.10 with `k = 1` and
equation (2.49), for an autonomous field).

If `V` is `C¹` at `x₀`, there are `T > 0`, `r > 0` and a map `Φ` such that for every `x` in the
ball of radius `r` about `x₀`: `Φ 0 x = x`; `t ↦ Φ t x` solves `ẋ = V x` on `(-T, T)`; each
`Φ t` is differentiable at `x`; the derivative `D_x Φ_t` is the identity at `t = 0` and solves
`d/dt D_x Φ_t = DV(Φ_t x) ∘ D_x Φ_t` on `(-T, T)`; and `(t, x) ↦ D_x Φ_t` is continuous on
`(-T, T) × B(x₀, r)`.

Weaker than the source in three ways: autonomous instead of time-dependent, `C¹` instead of
`C^k`, and regularity in the initial point only (the source has joint `C^k` regularity in the
time, the initial time and the initial point). -/
theorem exists_flow_differentiable {V : E → E} {x₀ : E} (hV : ContDiffAt ℝ 1 V x₀) :
    ∃ (Φ : ℝ → E → E) (T r : ℝ), 0 < T ∧ 0 < r ∧
      (∀ x ∈ ball x₀ r, Φ 0 x = x ∧ fderiv ℝ (Φ 0) x = ContinuousLinearMap.id ℝ E ∧
        ∀ t ∈ Ioo (-T) T, HasDerivAt (fun t => Φ t x) (V (Φ t x)) t ∧
          DifferentiableAt ℝ (Φ t) x ∧
          HasDerivAt (fun t => fderiv ℝ (Φ t) x)
            ((fderiv ℝ V (Φ t x)).comp (fderiv ℝ (Φ t) x)) t) ∧
      ContinuousOn (fun p : ℝ × E => fderiv ℝ (Φ p.1) p.2) (Ioo (-T) T ×ˢ ball x₀ r) := by
  obtain ⟨A, hA, H⟩ := exists_isFlowBox hV
  obtain ⟨r, T, K, Φ, h⟩ := H A hA le_rfl
  refine ⟨Φ, T, r, h.T_pos, h.r_pos, fun x hx => ⟨h.flow_zero x hx, h.fderiv_flow_zero hx,
    fun t ht => ⟨h.hasDerivAt x hx t (Ioo_subset_Icc_self ht),
      h.differentiableAt_flow hx (Ioo_subset_Icc_self ht), h.hasDerivAt_fderiv_flow hx ht⟩⟩, ?_⟩
  exact h.continuousOn_fderiv_flow.mono (prod_mono Ioo_subset_Icc_self subset_rfl)

end Lightlike.ODE
