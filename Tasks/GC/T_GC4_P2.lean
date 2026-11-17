import Lightlike.Gauge.ConstraintsAPI

/-!
# Task T-GC4-P2

The Jacobi identity for the Dirac bracket of smooth functions.

The statement is `Lightlike.Gauge.diracBracket_jacobi`, at the end of this file. Replace its `sorry` by
a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

For `C²` constraints with nonsingular bracket matrix everywhere and `C²` observables `f, g, h`, the Dirac bracket satisfies the Jacobi identity.

Hint. Differentiate the inverse of the bracket matrix and use `poissonBracket_jacobi`.

## What the statement uses

Everything the statement depends on, in one block:

    scripts/context-pack Lightlike.Gauge.diracBracket_jacobi

## References

Milestone GC4 (constrained Hamiltonian systems), ROADMAP section "Gauge theory and constrained systems".
Source: Henneaux–Teitelboim, Chapter 1 (`henneaux-teitelboim-1992` in docs/tasks/sources.yaml).
-/

open ClassicalMechanics InnerProductSpace
open scoped ContDiff

namespace Lightlike.Gauge

theorem diracBracket_jacobi {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {m : ℕ} (φ : Fin m → X → X → ℝ) (hφ : ∀ a, ContDiff ℝ 3 (fun x : X × X => φ a x.1 x.2))
    (hC : ∀ p q, (bracketMatrix φ p q).det ≠ 0)
    (f g h : X → X → ℝ) (hf : ContDiff ℝ 3 (fun x : X × X => f x.1 x.2))
    (hg : ContDiff ℝ 3 (fun x : X × X => g x.1 x.2)) (hh : ContDiff ℝ 3 (fun x : X × X => h x.1 x.2))
    (p q : X) :
    diracBracket φ f (fun p q => diracBracket φ g h p q) p q +
      diracBracket φ g (fun p q => diracBracket φ h f p q) p q +
      diracBracket φ h (fun p q => diracBracket φ f g p q) p q = 0 := by
  sorry

end Lightlike.Gauge
