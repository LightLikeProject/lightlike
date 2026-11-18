import Lightlike.Spacetime.Causal.BasicRelations

/-!
# Task T-GE2-P9

Strong causality implies causality.

The statement is `Lightlike.Causal.isCausal_of_isStronglyCausal`, at the end of this file. Replace
its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. If `y ∈ J⁺(x)` and `x ∈ J⁺(y)` with `x ≠ y`, a causally convex neighbourhood of `x` missing
`y` contains the whole loop, contradiction.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Causal/TimeOrientation.lean`: `Causal.TimeOrientation`
* `Lightlike/Spacetime/Causal/Ladder.lean`: `Causal.IsStronglyCausal`, `Causal.IsCausal`

Lemmas about them, which a proof may use:

* `Causal.causal_of_stronglyCausal` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.chronological_of_causal` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.isStronglyCausal_of_isStablyCausal_aux` (`Lightlike/Spacetime/CausalLadder/StrongCausality.lean`)
* `Causal.chron_trans` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.causal_trans` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.fieldAt_self` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.fieldAt_coord` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.exit_or_diamond` (`Lightlike/Spacetime/CausalLadder/ExitDiamond.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Causal.isCausal_of_isStronglyCausal

## References

Milestone GE2 (Causal structure), ROADMAP section "Lorentzian and Riemannian geometry".
Source: S. W. Hawking and G. F. R. Ellis, The Large Scale Structure of Space-Time, Cambridge
University Press (1973), Chapter: Causal structure (`hawking-ellis-1973` in
docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Strong causality implies causality.** -/
theorem isCausal_of_isStronglyCausal [T2Space M] (h : IsStronglyCausal T) : IsCausal T := by
  exact causal_of_stronglyCausal T h

end Lightlike.Causal
