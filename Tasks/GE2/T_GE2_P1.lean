import Lightlike.Spacetime.Causal.BasicRelations

/-!
# Task T-GE2-P1

Timelike futures are causal futures: I⁺(x) ⊆ J⁺(x).

The statement is `Lightlike.Causal.chronFuture_subset_causalFuture`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. Unfold both definitions; `IsFutureTimelike v` gives `IsFutureCausal v` (the vector is nonzero
because `g(v, X) < 0`).

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Causal/TimeOrientation.lean`: `Causal.TimeOrientation`
* `Lightlike/Spacetime/Causal/Relations.lean`: `Causal.chronFuture`, `Causal.causalFuture`

Lemmas about them, which a proof may use:

* `Causal.chron_subset_causal` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.chron_trans` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.causal_trans` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.exit_or_diamond` (`Lightlike/Spacetime/CausalLadder/ExitDiamond.lean`)
* `Causal.self_mem_causalFuture` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.causalFuture_of_subarc` (`Lightlike/Spacetime/CausalLadder/ExitDiamond.lean`)
* `Causal.exists_limit_curve_const` (`Lightlike/Spacetime/CausalLadder/LimitCurve.lean`)
* `Causal.exists_limit_mem_causalFuture` (`Lightlike/Spacetime/CausalLadder/LimitCurve.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Causal.chronFuture_subset_causalFuture

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

/-- **Timelike futures are causal futures: I⁺(x) ⊆ J⁺(x).** -/
theorem chronFuture_subset_causalFuture (x : M) : chronFuture T x ⊆ causalFuture T x := by
  exact chron_subset_causal T x

end Lightlike.Causal
