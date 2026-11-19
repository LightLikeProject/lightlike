import Lightlike.ODE.FlowDeriv
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# The local flow of a Killing field is an isometry

For a `C¹` vector field `V` on a real Banach space `E` with a local flow `Φ` (a flow box,
`Lightlike.ODE.IsFlowBox`) and a differentiable field of bilinear forms `G : E → E →L E →L ℝ`
(a metric in coordinates) for which `V` is Killing in coordinates,

`DG(y)(V y)(u, w) + G(y)(DV(y) u, w) + G(y)(u, DV(y) w) = 0`,

the flow preserves `G`: `G(Φ_t x)(D_xΦ_t u, D_xΦ_t w) = G(x)(u, w)` (`Lightlike.killing_flow_isometry`).
The proof differentiates the left side in `t` with the first variational equation
`d/dt D_xΦ_t = DV(Φ_t x) ∘ D_xΦ_t` (`IsFlowBox.hasDerivWithinAt_fderiv_flow`): the derivative is
the Killing expression at `Φ_t x` evaluated on `D_xΦ_t u, D_xΦ_t w`, hence zero.

This is the step from a Killing field to its local isometries, the converse of the statement that the
generator of a one-parameter family of isometries is Killing (Carroll, gr-qc/9712019, around
equation (5.44)); it is the first step of route (A) to the abstract form of G1-024.
-/

open Set Metric
open scoped NNReal

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The local flow of a Killing field preserves the metric.** -/
theorem killing_flow_isometry {V : E → E} {x₀ : E} {a r T : ℝ} {K : ℝ≥0} {Φ : ℝ → E → E}
    (h : ODE.IsFlowBox V x₀ a r T K Φ) (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hG : ∀ y ∈ ball x₀ a, DifferentiableAt ℝ G y)
    (hK : ∀ y ∈ ball x₀ a, ∀ u w : E,
      fderiv ℝ G y (V y) u w + G y (fderiv ℝ V y u) w + G y u (fderiv ℝ V y w) = 0)
    {x : E} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Icc (-T) T) (u w : E) :
    G (Φ t x) (fderiv ℝ (Φ t) x u) (fderiv ℝ (Φ t) x w) = G x u w := by
  set f : ℝ → ℝ := fun s => G (Φ s x) (fderiv ℝ (Φ s) x u) (fderiv ℝ (Φ s) x w) with hf
  have hd : ∀ s ∈ Icc (-T) T, HasDerivWithinAt f 0 (Icc (-T) T) s := by
    intro s hs
    have hy := h.flow_mem x hx s hs
    have hG' : HasFDerivAt G (fderiv ℝ G (Φ s x)) (Φ s x) := (hG _ hy).hasFDerivAt
    have h1 := (HasFDerivAt.comp_hasDerivAt (l := G) (f := fun s => Φ s x) s hG' (h.hasDerivAt x hx s hs)).hasDerivWithinAt (s := Icc (-T) T)
    have hD := h.hasDerivWithinAt_fderiv_flow hx hs
    have hu := hD.clm_apply (hasDerivWithinAt_const s (Icc (-T) T) u)
    have hw := hD.clm_apply (hasDerivWithinAt_const s (Icc (-T) T) w)
    have := (h1.clm_apply hu).clm_apply hw
    convert this using 1
    all_goals try rfl
    simp only [Function.comp_apply, map_zero, add_zero, add_apply, ContinuousLinearMap.comp_apply]
    linarith [hK _ hy (fderiv ℝ (Φ s) x u) (fderiv ℝ (Φ s) x w)]
  have hc : ContinuousOn f (Icc (-T) T) := fun s hs => (hd s hs).continuousWithinAt
  have hT := h.T_pos
  have hconst := constant_of_has_deriv_right_zero hc fun s hs =>
    (hd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)
  have h0 : f 0 = G x u w := by
    simp only [hf, h.flow_zero x hx, h.fderiv_flow_zero hx, ContinuousLinearMap.id_apply]
  show f t = G x u w
  rw [hconst t ht, ← hconst 0 h.zero_mem, h0]

/-- **Transport of a field along a flow whose brackets close.** If the brackets of the flow field `V` with finitely
many fields `X e` are constant combinations `[V, X c] = ∑ₑ C c e • X e` on the flow box, and `c(t)` solves
`ċₑ = -∑_d c_d C d e`, then `D_xΦ_t (∑_b c_b(0) X_b(x)) = ∑ₑ cₑ(t) Xₑ(Φ_t x)`: both sides solve the first
variational equation `u̇ = DV(Φ_t x) u` with the same value at `0`. -/
theorem flow_transport {V : E → E} {x₀ : E} {a r T : ℝ} {K : ℝ≥0} {Φ : ℝ → E → E}
    (h : ODE.IsFlowBox V x₀ a r T K Φ) {ι : Type*} [Fintype ι] (X : ι → E → E)
    (hX : ∀ c, ∀ y ∈ ball x₀ a, DifferentiableAt ℝ (X c) y) (C : ι → ι → ℝ)
    (hVX : ∀ c, ∀ y ∈ ball x₀ a, VectorField.lieBracket ℝ V (X c) y = ∑ e, C c e • X e y)
    {x : E} (hx : x ∈ ball x₀ r) (c : ℝ → ι → ℝ)
    (hc : ∀ t ∈ Icc (-T) T, HasDerivWithinAt c (fun e => -∑ d, c t d * C d e) (Icc (-T) T) t)
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    fderiv ℝ (Φ t) x (∑ b, c 0 b • X b x) = ∑ e, c t e • X e (Φ t x) := by
  set v : E := ∑ b, c 0 b • X b x
  have hl : ∀ s ∈ Icc (-T) T, HasDerivWithinAt (fun s => fderiv ℝ (Φ s) x v)
      (fderiv ℝ V (Φ s x) (fderiv ℝ (Φ s) x v)) (Icc (-T) T) s := by
    intro s hs
    have := (h.hasDerivWithinAt_fderiv_flow hx hs).clm_apply (hasDerivWithinAt_const s (Icc (-T) T) v)
    simpa using this
  have hu : ∀ s ∈ Icc (-T) T, HasDerivWithinAt (fun s => ∑ e, c s e • X e (Φ s x))
      (fderiv ℝ V (Φ s x) (∑ e, c s e • X e (Φ s x))) (Icc (-T) T) s := by
    intro s hs
    have hy := h.flow_mem x hx s hs
    have hce : ∀ e, HasDerivWithinAt (fun s => c s e) (-∑ d, c s d * C d e) (Icc (-T) T) s := fun e =>
      (hasDerivWithinAt_pi.1 (hc s hs)) e
    have hXe : ∀ e, HasDerivWithinAt (fun s => X e (Φ s x)) (fderiv ℝ (X e) (Φ s x) (V (Φ s x))) (Icc (-T) T) s :=
      fun e => (HasFDerivAt.comp_hasDerivAt (l := X e) (f := fun s => Φ s x) s (hX e _ hy).hasFDerivAt
        (h.hasDerivAt x hx s hs)).hasDerivWithinAt
    have hsum := HasDerivWithinAt.sum (u := Finset.univ) fun e _ => (hce e).smul (hXe e)
    convert hsum using 1
    · funext s; simp
    · -- `DXₑ V = DV Xₑ + [V, Xₑ]`
      have hbr : ∀ e, fderiv ℝ (X e) (Φ s x) (V (Φ s x)) =
          fderiv ℝ V (Φ s x) (X e (Φ s x)) + ∑ f, C e f • X f (Φ s x) := by
        intro e
        rw [← hVX e _ hy, VectorField.lieBracket]
        abel
      simp only [hbr, smul_add, Finset.sum_add_distrib, map_sum, map_smul, neg_smul, Finset.sum_smul,
        Finset.smul_sum, smul_smul]
      rw [Finset.sum_neg_distrib, Finset.sum_comm (f := fun x_1 y => (c s y * C y x_1) • X x_1 (Φ s x))]
      simp only [mul_comm]
      abel
  have hA : ∀ s ∈ Icc (-T) T, ‖fderiv ℝ V (Φ s x)‖ ≤ K := fun s hs => h.norm_fderiv_le _ (h.flow_mem x hx s hs)
  have := ODE.eqOn_of_linear (A := fun s => fderiv ℝ V (Φ s x)) hA hl hu (by
    simp only [h.fderiv_flow_zero hx, ContinuousLinearMap.id_apply, h.flow_zero x hx, v]) ht
  exact this

end Lightlike
