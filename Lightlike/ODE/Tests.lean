import Lightlike.ODE.Frobenius
import Lightlike.ODE.FlowContDiff
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Checks for the flow, commuting-flow and Frobenius results

* The linear field `V x = x` on `ℝ` with its flow `Φ t x = e^t x` is a flow box
  (`isFlowBox_id`), so the hypotheses of the flow-box theorems can be met.
* Known value: the theorem on the derivative of a flow returns `D_x Φ_t = e^t`
  (`hasFDerivAt_exp_flow`), and a wrong candidate, the identity, is excluded
  (`fderiv_exp_flow_ne_id`).
* Constant fields satisfy the hypotheses of the commuting-flows theorem and of the Frobenius
  theorem (`exists_flows_commute_const`, `exists_integral_manifold_const`).
* The time-dependent field `f (t, x) = t` satisfies the hypothesis of the `C^k` theorem
  (`exists_solution_contDiffOn_fst`).
-/

open Set Metric Filter Topology VectorField
open scoped NNReal

noncomputable section

namespace Lightlike.ODE.Tests

/-- **Non-vacuity of `IsFlowBox`**: the field `V x = x` on `ℝ` with the flow `e^t x`. -/
theorem isFlowBox_id :
    IsFlowBox (fun x : ℝ => x) 0 3 1 (1 / 2) 1 (fun t x => Real.exp t * x) where
  r_pos := one_pos
  T_pos := by norm_num
  mul_le := by norm_num
  differentiableAt := fun _ _ => differentiableAt_id
  continuousOn_fderiv := by
    have : fderiv ℝ (fun x : ℝ => x) = fun _ => ContinuousLinearMap.id ℝ ℝ := by
      funext y; exact fderiv_fun_id
    rw [this]
    exact continuousOn_const
  norm_fderiv_le := fun y _ => by
    have : fderiv ℝ (fun x : ℝ => x) y = ContinuousLinearMap.id ℝ ℝ := fderiv_fun_id
    rw [this]
    simp
  flow_zero := fun x _ => by simp
  flow_mem := fun x hx t ht => by
    rw [mem_ball_zero_iff, Real.norm_eq_abs] at hx ⊢
    have h1 : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith [ht.2])
    have h2 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h3 : 0 < Real.exp t := Real.exp_pos t
    rw [abs_mul, abs_of_pos h3]
    nlinarith [abs_nonneg x]
  hasDerivAt := fun x _ t _ => (Real.hasDerivAt_exp t).mul_const x

/-- **Known value**: the derivative in the initial point of the flow `e^t x` of `V x = x`, computed
with `IsFlowBox.hasFDerivAt_of_variational` from the solution `e^t` of the variational equation
`u̇ = u`, is multiplication by `e^t`. -/
theorem hasFDerivAt_exp_flow {x t : ℝ} (hx : x ∈ ball (0 : ℝ) 1)
    (ht : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    HasFDerivAt (fun x : ℝ => Real.exp t * x) (Real.exp t • ContinuousLinearMap.id ℝ ℝ) x := by
  refine isFlowBox_id.hasFDerivAt_of_variational (U := fun t => Real.exp t •
    ContinuousLinearMap.id ℝ ℝ) hx (by simp) (fun s _ => ?_) ht
  simp only [fderiv_fun_id, ContinuousLinearMap.id_comp]
  exact ((Real.hasDerivAt_exp s).smul_const (ContinuousLinearMap.id ℝ ℝ)).hasDerivWithinAt

/-- **A wrong candidate is excluded**: at `t = 1/2` the derivative of the flow `e^t x` in the
initial point is not the identity. -/
theorem fderiv_exp_flow_ne_id :
    fderiv ℝ (fun x : ℝ => Real.exp (1 / 2) * x) 0 ≠ ContinuousLinearMap.id ℝ ℝ := by
  have h := (hasFDerivAt_exp_flow (x := 0) (t := 1 / 2) (mem_ball_self one_pos)
    ⟨by norm_num, le_rfl⟩).fderiv
  rw [h]
  intro hcontra
  have h1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hcontra
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    mul_one] at h1
  have h2 : (1 : ℝ) < Real.exp (1 / 2) := Real.one_lt_exp_iff.2 (by norm_num)
  linarith

/-- **Non-vacuity of `exists_flows_commute`**: two constant fields on a Banach space. -/
theorem exists_flows_commute_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (v w x₀ : E) :
    ∃ (a r τ ρ : ℝ) (K K' : ℝ≥0) (Φ Ψ : ℝ → E → E),
      IsFlowBox (fun _ : E => v) x₀ a r τ K Φ ∧ IsFlowBox (fun _ : E => w) x₀ a r τ K' Ψ ∧
      0 < ρ ∧ ρ ≤ r ∧ ∀ x ∈ ball x₀ ρ, ∀ t ∈ Icc (-τ) τ, ∀ s ∈ Icc (-τ) τ,
        Φ t x ∈ ball x₀ r ∧ Ψ s x ∈ ball x₀ r ∧ Φ t (Ψ s x) = Ψ s (Φ t x) :=
  exists_flows_commute contDiffAt_const contDiffAt_const
    (Eventually.of_forall fun y => by simp [lieBracket])

/-- **Non-vacuity of `exists_integral_manifold_of_involutive`**: one constant nonzero field on
`ℝ × ℝ`. -/
theorem exists_integral_manifold_const :
    ∃ (ε : ℝ) (f : (Fin 1 → ℝ) × (ℝ × ℝ) → ℝ × ℝ)
      (f' : (Fin 1 → ℝ) × (ℝ × ℝ) → ((Fin 1 → ℝ) × (ℝ × ℝ) →L[ℝ] ℝ × ℝ)), 0 < ε ∧
      (∀ x ∈ ball (0 : ℝ × ℝ) ε, f (0, x) = x ∧ ∀ ξ : ℝ × ℝ, f' (0, x) (0, ξ) = ξ) ∧
      ∀ t ∈ ball (0 : Fin 1 → ℝ) ε, ∀ x ∈ ball (0 : ℝ × ℝ) ε,
        HasFDerivAt f (f' (t, x)) (t, x) ∧
        Function.Injective (fun τ : Fin 1 → ℝ => f' (t, x) (τ, 0)) ∧
        range (fun τ : Fin 1 → ℝ => f' (t, x) (τ, 0)) =
          (Submodule.span ℝ (range fun _ : Fin 1 => ((1, 0) : ℝ × ℝ)) : Set (ℝ × ℝ)) :=
  exists_integral_manifold_of_involutive (X := fun _ : Fin 1 => fun _ : ℝ × ℝ => ((1, 0) : ℝ × ℝ))
    (x₀ := 0) (fun _ => contDiffAt_const)
    (linearIndependent_unique_iff.2 (by simp))
    (Eventually.of_forall fun y i j => by simp [lieBracket])

/-- **Non-vacuity of `exists_solution_contDiffOn`**: the time-dependent field `f (t, x) = t` on
`ℝ`, which is `C^{k+1}` for every `k`. -/
theorem exists_solution_contDiffOn_fst (k : ℕ) (t₀ x₀ : ℝ) :
    ∃ (δ : ℝ) (φ : ℝ → ℝ → ℝ → ℝ), 0 < δ ∧
      (∀ s ∈ Ioo (t₀ - δ) (t₀ + δ), ∀ x ∈ ball x₀ δ, φ s s x = x ∧
        ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), HasDerivAt (fun t => φ t s x) t t) ∧
      ContDiffOn ℝ ((k : WithTop ℕ∞) + 1) (fun q : ℝ × ℝ × ℝ => φ q.1 q.2.1 q.2.2)
        (Ioo (t₀ - δ) (t₀ + δ) ×ˢ Ioo (t₀ - δ) (t₀ + δ) ×ˢ ball x₀ δ) := by
  obtain ⟨δ, φ, hδ, h1, h2, -⟩ := exists_solution_contDiffOn k
    (f := fun p : ℝ × ℝ => p.1) (t₀ := t₀) (x₀ := x₀) contDiffAt_fst
  exact ⟨δ, φ, hδ, h1, h2⟩

end Lightlike.ODE.Tests
