import Lightlike.Gauge.ConstraintsAPI

/-!
# Task T-GC4-P1

The Jacobi identity for the Poisson bracket of smooth phase-space functions.

The statement is `Lightlike.Gauge.poissonBracket_jacobi`, at the end of this file. Replace its `sorry` by
a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

For `C²` observables `f, g, h`, `{f, {g, h}} + {g, {h, f}} + {h, {f, g}} = 0` at every point of phase space.

Hint. Write the bracket as `Ω (∇f, ∇g)` (`poissonBracket_eq_gradForm`) and use the symmetry of second derivatives.

## What the statement uses

Everything the statement depends on, in one block:

    scripts/context-pack Lightlike.Gauge.poissonBracket_jacobi

## References

Milestone GC4 (constrained Hamiltonian systems), ROADMAP section "Gauge theory and constrained systems".
Source: Physlib's Poisson bracket module lists this identity as a TODO (`henneaux-teitelboim-1992` in docs/tasks/sources.yaml).
-/

open ClassicalMechanics InnerProductSpace
open scoped ContDiff

namespace Lightlike.Gauge

theorem poissonBracket_jacobi {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g h : X → X → ℝ) (hf : ContDiff ℝ 2 (fun x : X × X => f x.1 x.2))
    (hg : ContDiff ℝ 2 (fun x : X × X => g x.1 x.2)) (hh : ContDiff ℝ 2 (fun x : X × X => h x.1 x.2))
    (p q : X) :
    poissonBracket f (fun p q => poissonBracket g h p q) p q +
      poissonBracket g (fun p q => poissonBracket h f p q) p q +
      poissonBracket h (fun p q => poissonBracket f g p q) p q = 0 := by
  sorry

end Lightlike.Gauge
