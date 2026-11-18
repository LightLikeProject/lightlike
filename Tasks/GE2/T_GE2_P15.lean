import Lightlike.Spacetime.Causal.MinkowskiGH

/-!
# Task T-GE2-P15

Minkowski space is globally hyperbolic.

The statement is `Lightlike.Causal.minkowski_isGloballyHyperbolic`, at the end of this file. Replace
its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. From `minkowski_causalFuture`: the diamonds are closed and bounded subsets of `ℝ^{d+1}`.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Causal/Ladder.lean`: `Causal.IsGloballyHyperbolic`
* `Lightlike/Spacetime/Minkowski.lean`: `minkowskiMetric`
* `Lightlike/Spacetime/Causal/MinkowskiCausal.lean`: `Causal.minkowskiOrientation`

Lemmas about them, which a proof may use:

* `Causal.minkowski_globallyHyperbolic` (`Lightlike/Spacetime/Causal/MinkowskiGH.lean`)
* `Causal.coord_sub_le` (`Lightlike/Spacetime/Causal/MinkowskiCauchy.lean`)
* `Causal.timeMinus_mono` (`Lightlike/Spacetime/Causal/MinkowskiFuture.lean`)
* `Causal.dist_le_time_sub` (`Lightlike/Spacetime/Causal/MinkowskiCauchy.lean`)
* `Causal.time_lt_of_timelike` (`Lightlike/Spacetime/Causal/MinkowskiCauchy.lean`)
* `Causal.line_mem_chronFuture` (`Lightlike/Spacetime/Causal/MinkowskiCausal.lean`)
* `Causal.mem_causalFuture_iff` (`Lightlike/Spacetime/Causal/MinkowskiGH.lean`)
* `Causal.minkowski_isStablyCausal` (`Lightlike/Spacetime/CausalLadder/TestsStrong.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Causal.minkowski_isGloballyHyperbolic

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

variable {d : ℕ}

/-- **Minkowski space is globally hyperbolic.** -/
theorem minkowski_isGloballyHyperbolic : IsGloballyHyperbolic (minkowskiOrientation d) := by
  exact minkowski_globallyHyperbolic

end Lightlike.Causal
