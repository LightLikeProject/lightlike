import Lightlike.Spacetime.Causal.MinkowskiCausal

/-!
# Task T-GE2-P11

Causal simplicity implies stable causality.

The statement is `Lightlike.Causal.isStablyCausal_of_isCausallySimple`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. Construct a time function by Hawking's averaging of volumes of futures, using closedness of
`J±`.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Causal/TimeOrientation.lean`: `Causal.TimeOrientation`
* `Lightlike/Spacetime/Causal/Ladder.lean`: `Causal.IsCausallySimple`, `Causal.IsStablyCausal`

Lemmas about them, which a proof may use:

* `Causal.isStronglyCausal_of_isStablyCausal_aux` (`Lightlike/Spacetime/CausalLadder/StrongCausality.lean`)
* `Causal.chron_trans` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.causal_trans` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.fieldAt_self` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.fieldAt_coord` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.isOpen_coverSet` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.exit_or_diamond` (`Lightlike/Spacetime/CausalLadder/ExitDiamond.lean`)
* `Causal.ReachIn.left_mem` (`Lightlike/Spacetime/CausalLadder/StrongCausality.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Causal.isStablyCausal_of_isCausallySimple

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

/-- **Causal simplicity implies stable causality.** -/
theorem isStablyCausal_of_isCausallySimple [T2Space M] [SecondCountableTopology M]
    (h : IsCausallySimple T) : IsStablyCausal T := by
  sorry

end Lightlike.Causal
