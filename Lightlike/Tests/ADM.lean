import Mathlib
import Lightlike.Canonical.ADM

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

end Lightlike.Canonical
