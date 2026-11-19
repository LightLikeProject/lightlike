import Lightlike.ODE.CommutingFlows

/-!
# Commuting flows: the converses

Michor's Corollary 3.15 states the equivalence of (1) `[X, Y] = 0`, (2) the flow of `X` carries
`Y` into itself, and (3) the flows commute. `Lightlike.ODE.CommutingFlows` has (1) ⇒ (2) ⇒ (3)
in flow boxes. This file has the converses, also in flow boxes:

* `Lightlike.ODE.IsFlowBox.fderiv_flow_apply_eq_of_flow_comm`: (3) ⇒ (2);
* `Lightlike.ODE.IsFlowBox.lieBracket_eq_zero_of_fderiv_flow_apply_eq`: (2) ⇒ (1);
* `Lightlike.ODE.IsFlowBox.lieBracket_eq_zero_of_flow_comm`: (3) ⇒ (1).

## References

* `michor-2008`: P. W. Michor, *Topics in Differential Geometry*, Corollary 3.15, page 28 of the
  author's version.
-/

open Set Metric Filter Topology
open scoped NNReal

noncomputable section

namespace Lightlike.ODE

namespace IsFlowBox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {V W : E → E} {x₀ : E} {a a' r r' T T' : ℝ} {K K' : ℝ≥0} {Φ Ψ : ℝ → E → E}

/-- **If the flow of `V` carries `W` into itself along a trajectory, then `[V, W] = 0` at its
starting point** (Michor, Corollary 3.15, (2) ⇒ (1)): differentiate
`D_x Φ_t (W x) = W (Φ t x)` at `t = 0`. -/
theorem lieBracket_eq_zero_of_fderiv_flow_apply_eq (h : IsFlowBox V x₀ a r T K Φ) {x : E}
    (hx : x ∈ ball x₀ r) (hW : DifferentiableAt ℝ W x)
    (hinv : ∀ t ∈ Icc (-T) T, fderiv ℝ (Φ t) x (W x) = W (Φ t x)) :
    VectorField.lieBracket ℝ V W x = 0 := by
  have h0 : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith [h.T_pos], h.T_pos⟩
  have hu : HasDerivAt (fun t => fderiv ℝ (Φ t) x (W x))
      (fderiv ℝ V (Φ 0 x) (fderiv ℝ (Φ 0) x (W x))) 0 := by
    have h1 := (h.hasDerivAt_fderiv_flow hx h0).clm_apply (hasDerivAt_const (0 : ℝ) (W x))
    simpa using h1
  have hw : HasDerivAt (fun t => W (Φ t x)) (fderiv ℝ W (Φ 0 x) (V (Φ 0 x))) 0 := by
    have hW' : HasFDerivAt W (fderiv ℝ W (Φ 0 x)) (Φ 0 x) := by
      rw [h.flow_zero x hx]; exact hW.hasFDerivAt
    exact hW'.comp_hasDerivAt (0 : ℝ) (h.hasDerivAt x hx 0 h.zero_mem)
  have heq : (fun t => fderiv ℝ (Φ t) x (W x)) =ᶠ[𝓝 0] fun t => W (Φ t x) := by
    filter_upwards [Icc_mem_nhds h0.1 h0.2] with t ht using hinv t ht
  have h2 := (hw.congr_of_eventuallyEq heq).unique hu
  simp only [h.flow_zero x hx, h.fderiv_flow_zero hx, ContinuousLinearMap.id_apply] at h2
  rw [VectorField.lieBracket, h2, sub_self]

/-- **If the flows of `V` and `W` commute, the flow of `V` carries `W` into itself** (Michor,
Corollary 3.15, (3) ⇒ (2)): differentiate `Φ t (Ψ s x) = Ψ s (Φ t x)` in `s` at `s = 0`. -/
theorem fderiv_flow_apply_eq_of_flow_comm (hV : IsFlowBox V x₀ a r T K Φ)
    (hW : IsFlowBox W x₀ a' r' T' K' Ψ) {x : E} (hx : x ∈ ball x₀ r) (hx' : x ∈ ball x₀ r')
    {t : ℝ} (ht : t ∈ Icc (-T) T) (hΦ : Φ t x ∈ ball x₀ r')
    (hcomm : ∀ s ∈ Icc (-T') T', Φ t (Ψ s x) = Ψ s (Φ t x)) :
    fderiv ℝ (Φ t) x (W x) = W (Φ t x) := by
  have h0 : (0 : ℝ) ∈ Ioo (-T') T' := ⟨by linarith [hW.T_pos], hW.T_pos⟩
  have hd : HasFDerivAt (Φ t) (fderiv ℝ (Φ t) x) (Ψ 0 x) := by
    rw [hW.flow_zero x hx']; exact (hV.differentiableAt_flow hx ht).hasFDerivAt
  have h1 : HasDerivAt (Φ t ∘ fun s => Ψ s x) (fderiv ℝ (Φ t) x (W (Ψ 0 x))) 0 :=
    hd.comp_hasDerivAt (0 : ℝ) (hW.hasDerivAt x hx' 0 hW.zero_mem)
  have h2 : HasDerivAt (fun s => Ψ s (Φ t x)) (W (Ψ 0 (Φ t x))) 0 :=
    hW.hasDerivAt _ hΦ 0 hW.zero_mem
  have heq : (Φ t ∘ fun s => Ψ s x) =ᶠ[𝓝 0] fun s => Ψ s (Φ t x) := by
    filter_upwards [Icc_mem_nhds h0.1 h0.2] with s hs using hcomm s hs
  have h3 := (h2.congr_of_eventuallyEq heq).unique h1
  simp only [hW.flow_zero x hx', hW.flow_zero _ hΦ] at h3
  exact h3.symm

/-- **If the flows of `V` and `W` commute near `x`, then `[V, W] = 0` at `x`** (Michor,
Corollary 3.15, (3) ⇒ (1)). -/
theorem lieBracket_eq_zero_of_flow_comm (hV : IsFlowBox V x₀ a r T K Φ)
    (hW : IsFlowBox W x₀ a' r' T' K' Ψ) {x : E} (hx : x ∈ ball x₀ r) (hx' : x ∈ ball x₀ r')
    (hΦ : ∀ t ∈ Icc (-T) T, Φ t x ∈ ball x₀ r')
    (hcomm : ∀ t ∈ Icc (-T) T, ∀ s ∈ Icc (-T') T', Φ t (Ψ s x) = Ψ s (Φ t x)) :
    VectorField.lieBracket ℝ V W x = 0 :=
  hV.lieBracket_eq_zero_of_fderiv_flow_apply_eq hx
    (hW.differentiableAt x (hW.initial_mem hx'))
    (fun t ht => hV.fderiv_flow_apply_eq_of_flow_comm hW hx hx' ht (hΦ t ht) (hcomm t ht))

end IsFlowBox

end Lightlike.ODE
