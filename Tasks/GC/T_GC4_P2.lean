import Lightlike.Gauge.Constraints

/-!
# Task T-GC4-P2

The Dirac bracket is antisymmetric.

The statement is `Lightlike.Gauge.diracBracket_antisymm`, at the end of this file. Replace its `sorry` by
a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

`{f, g}_D = -{g, f}_D` at every point.

Hint. The bracket matrix is antisymmetric (`poissonBracket_antisymm`), hence so is its inverse (`Matrix.transpose_nonsing_inv`); swap the two summation indices.

## What the statement uses

Everything the statement depends on, in one block:

    scripts/context-pack Lightlike.Gauge.diracBracket_antisymm

## References

Milestone GC4 (constrained Hamiltonian systems), ROADMAP section "Gauge theory and constrained systems".
Source: Henneaux–Teitelboim, Chapter 1 (`henneaux-teitelboim-1992` in docs/tasks/sources.yaml).
-/

open ClassicalMechanics InnerProductSpace

namespace Lightlike.Gauge

theorem diracBracket_antisymm {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {m : ℕ} (φ : Fin m → X → X → ℝ) (f g : X → X → ℝ) (p q : X) :
    diracBracket φ f g p q = -diracBracket φ g f p q := by
  sorry

end Lightlike.Gauge
