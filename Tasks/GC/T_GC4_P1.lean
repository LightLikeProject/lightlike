import Lightlike.Gauge.Constraints

/-!
# Task T-GC4-P1

The Dirac bracket with a second-class constraint vanishes.

The statement is `Lightlike.Gauge.diracBracket_constraint`, at the end of this file. Replace its `sorry` by
a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Where the bracket matrix is nonsingular, `{f, φ_c}_D = 0` for every observable `f` and every constraint `φ_c`.

Hint. `{φ_b, φ_c}` is the entry `C b c`, so the double sum collapses with `C⁻¹ * C = 1` (`Matrix.nonsing_inv_mul`); no differentiability is needed.

## What the statement uses

Everything the statement depends on, in one block:

    scripts/context-pack Lightlike.Gauge.diracBracket_constraint

## References

Milestone GC4 (constrained Hamiltonian systems), ROADMAP section "Gauge theory and constrained systems".
Source: Dirac (1964), Lectures on Quantum Mechanics, Lecture 2; Henneaux–Teitelboim, Section 1.3 (`henneaux-teitelboim-1992` in docs/tasks/sources.yaml).
-/

open ClassicalMechanics InnerProductSpace

namespace Lightlike.Gauge

theorem diracBracket_constraint {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {m : ℕ} (φ : Fin m → X → X → ℝ) (f : X → X → ℝ) (c : Fin m) (p q : X)
    (hC : (bracketMatrix φ p q).det ≠ 0) :
    diracBracket φ f (φ c) p q = 0 := by
  sorry

end Lightlike.Gauge
