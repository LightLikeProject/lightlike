import Lightlike.Gauge.Constraints

/-!
# Task T-GC4-P3

Second-class constraints come in an even number.

The statement is `Lightlike.Gauge.even_of_isSecondClass`, at the end of this file. Replace its `sorry` by
a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

If the constraints are second class and the constraint surface is non-empty, `m` is even.

Hint. The bracket matrix is antisymmetric, and an antisymmetric real matrix of odd size has determinant `0` (`Matrix.det_neg`, `Matrix.det_transpose`).

## What the statement uses

Everything the statement depends on, in one block:

    scripts/context-pack Lightlike.Gauge.even_of_isSecondClass

## References

Milestone GC4 (constrained Hamiltonian systems), ROADMAP section "Gauge theory and constrained systems".
Source: Henneaux–Teitelboim, Chapter 1 (`henneaux-teitelboim-1992` in docs/tasks/sources.yaml).
-/

open ClassicalMechanics InnerProductSpace

namespace Lightlike.Gauge

theorem even_of_isSecondClass {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {m : ℕ} (φ : Fin m → X → X → ℝ) (h : IsSecondClass φ) (hne : (constraintSet φ).Nonempty) :
    Even m := by
  sorry

end Lightlike.Gauge
