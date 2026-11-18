import Mathlib
import Lightlike.Canonical.ADM
import Lightlike.Canonical.MomentumBracket

/-!
# Trust checks of the ADM constraints

* **Flat data.** The Euclidean metric `h = 1` with `π = 0` satisfies both constraints at every point
  (in every dimension), and its smeared constraints vanish for every test field.
* **Wrong data.** In dimension one, `π(x) = x` on `h = 1` violates the momentum constraint
  (`∇_k π^{ik} = 1`), and in dimension `d ≥ 2` the constant `π = 1` violates the Hamiltonian constraint (`ℋ = −d/(d − 1)`) while
  satisfying the momentum constraint. So neither constraint is implied by the other, and neither
  definition is vacuous.
-/

open Matrix

namespace Lightlike.Canonical

variable {d : ℕ}

/-- The flat spatial metric `h = 1` and `π = 0` satisfy the Hamiltonian constraint. -/
theorem flat_hamiltonian (x : Fin d → ℝ) :
    hamiltonianDensity (fun _ => (1 : Matrix (Fin d) (Fin d) ℝ)) (fun _ => 0) x = 0 := by
  have hR : Lightlike.scalarCurvature (fun _ => (1 : Matrix (Fin d) (Fin d) ℝ)) x = 0 :=
    Lightlike.scalarCurvature_eq_zero_of_riemann_eq_zero fun ρ σ μ ν =>
      Lightlike.riemann_const 1 ρ σ μ ν x
  simp [hamiltonianDensity, kineticDensity, hR]

/-- The flat data satisfy the momentum constraint. -/
theorem flat_momentum (x : Fin d → ℝ) :
    MomentumConstraintAt (fun _ => (1 : Matrix (Fin d) (Fin d) ℝ)) (fun _ => 0) x := by
  intro i
  simp [momentumDivergence, Lightlike.pd]

/-- The smeared constraints of the flat data vanish for every test field. -/
theorem flat_smeared (N : (Fin d → ℝ) → ℝ) (ξ : VectorField d) :
    hamiltonianConstraint N (fun _ => (1 : Matrix (Fin d) (Fin d) ℝ)) (fun _ => 0) = 0 ∧
      momentumConstraint ξ (fun _ => (1 : Matrix (Fin d) (Fin d) ℝ)) (fun _ => 0) = 0 := by
  refine ⟨?_, ?_⟩
  · simp [hamiltonianConstraint, flat_hamiltonian]
  · simp [momentumConstraint, momentumDensity]

/-- **Wrong momentum**: in dimension one, `π(x) = x` on the flat metric violates the momentum constraint. -/
theorem wrong_momentum_violates (x : Fin 1 → ℝ) :
    ¬ MomentumConstraintAt (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) (fun y => Matrix.of fun _ _ => y 0) x := by
  intro h
  have := h 0
  have hp : Lightlike.pd (0 : Fin 1) (fun y : Fin 1 → ℝ => y 0) x = 1 := by
    simp only [Lightlike.pd]
    rw [(hasFDerivAt_apply (0 : Fin 1) x).fderiv]
    simp
  have hc : ∀ k l : Fin 1, Lightlike.christoffel (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 k l x = 0 := by
    intro k l; simp [Lightlike.christoffel_const]
  simp [momentumDivergence, hc, hp] at this

/-- **Wrong Hamiltonian**: in dimension `d ≥ 2`, the constant `π = 1` on `h = 1` satisfies the momentum
constraint but violates the Hamiltonian constraint (`ℋ = −d/(d − 1)`). -/
theorem wrong_hamiltonian_violates (hd : 2 ≤ d) (x : Fin d → ℝ) :
    MomentumConstraintAt (fun _ => (1 : Matrix (Fin d) (Fin d) ℝ)) (fun _ => 1) x ∧
      ¬ HamiltonianConstraintAt (fun _ => (1 : Matrix (Fin d) (Fin d) ℝ)) (fun _ => 1) x := by
  have hR : Lightlike.scalarCurvature (fun _ => (1 : Matrix (Fin d) (Fin d) ℝ)) x = 0 :=
    Lightlike.scalarCurvature_eq_zero_of_riemann_eq_zero fun ρ σ μ ν =>
      Lightlike.riemann_const 1 ρ σ μ ν x
  refine ⟨fun i => ?_, fun h => ?_⟩
  · simp [momentumDivergence, Lightlike.pd, Lightlike.christoffel_const]
  · have h1 : ((d : ℝ) - 1) ≠ 0 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    simp only [HamiltonianConstraintAt, hamiltonianDensity, kineticDensity, hR, mul_zero, sub_zero] at h
    simp [Matrix.trace_one] at h
    field_simp at h
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith

/-- **Non-vacuity of `bracket_momentum_momentum`**: in dimension one there are nonzero, smooth, compactly supported
shifts, a smooth positive metric and a continuous momentum, so the bracket of two smeared momentum constraints
is `D` of the Lie bracket of two bump-function shifts on the flat metric. -/
theorem bracket_momentum_momentum_nonvacuous :
    ∃ (ξ η : VectorField 1) (h π : TensorField 1), SmoothVec ξ ∧ SmoothVec η ∧ SmoothTensor h ∧
      (∀ x, (h x).PosDef) ∧ (∀ k, HasCompactSupport (fun y => ξ y k)) ∧ (∀ k, HasCompactSupport (fun y => η y k)) ∧
      (∃ x, ξ x 0 ≠ 0) ∧ (∃ x, η x 0 ≠ 0) ∧
      admBracket (momentumConstraint ξ) (momentumConstraint η) (fun h _ => lieTensor ξ h)
        (fun h _ => lieTensor η h) h π = momentumConstraint (fun y k => lieBracket ξ η y k) h π := by
  let b1 : ContDiffBump (0 : Fin 1 → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let b2 : ContDiffBump (0 : Fin 1 → ℝ) := ⟨2, 3, two_pos, by norm_num⟩
  let ξ : VectorField 1 := fun y _ => b1 y
  let η : VectorField 1 := fun y _ => b2 y
  let h : TensorField 1 := fun _ => 1
  let π : TensorField 1 := fun y => Matrix.of fun _ _ => y 0
  have hξ : SmoothVec ξ := fun _ => b1.contDiff
  have hη : SmoothVec η := fun _ => b2.contDiff
  have hh : SmoothTensor h := fun i j => contDiff_const
  have hξc : ∀ k, HasCompactSupport (fun y => ξ y k) := fun _ => b1.hasCompactSupport
  have hηc : ∀ k, HasCompactSupport (fun y => η y k) := fun _ => b2.hasCompactSupport
  have hπ : ∀ i j, Continuous (fun x => π x i j) := fun i j => by
    show Continuous (fun x : Fin 1 → ℝ => x 0)
    exact continuous_apply 0
  refine ⟨ξ, η, h, π, hξ, hη, hh, fun x => ?_, hξc, hηc, ⟨0, ?_⟩, ⟨0, ?_⟩,
    bracket_momentum_momentum hξ hη hξc hηc hh hπ⟩
  · simpa [h] using Matrix.PosDef.one
  · show b1 0 ≠ 0
    rw [b1.one_of_mem_closedBall (x := 0) (by simp [b1])]
    exact one_ne_zero
  · show b2 0 ≠ 0
    rw [b2.one_of_mem_closedBall (x := 0) (by simp [b2])]
    exact one_ne_zero

end Lightlike.Canonical
