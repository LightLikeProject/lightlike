import Lightlike.Spacetime.Causal.MinkowskiCausal

/-!
# Task T-GE2-P7

The chronological future is open.

The statement is `Lightlike.Causal.isOpen_chronFuture`, at the end of this file. Replace its `sorry`
by a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. Perturb the end of a timelike curve inside a chart; the open future cone at the end point
supplies the room.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Causal/TimeOrientation.lean`: `Causal.TimeOrientation`
* `Lightlike/Spacetime/Causal/Relations.lean`: `Causal.chronFuture`

Lemmas about them, which a proof may use:

* `Causal.TimeOrientation.mk.inj` (`Lightlike/Spacetime/Causal/TimeOrientation.lean`)
* `Causal.TimeOrientation.mk.injEq` (`Lightlike/Spacetime/Causal/TimeOrientation.lean`)
* `Causal.TimeOrientation.timelike` (`Lightlike/Spacetime/Causal/TimeOrientation.lean`)
* `Causal.TimeOrientation.contMDiff` (`Lightlike/Spacetime/Causal/TimeOrientation.lean`)
* `Causal.TimeOrientation.mk.sizeOf_spec` (`Lightlike/Spacetime/Causal/TimeOrientation.lean`)
* `LorentzianMetric.symm` (`Lightlike/Spacetime/Lorentzian.lean`)
* `LorentzianMetric.mk.inj` (`Lightlike/Spacetime/Lorentzian.lean`)
* `LorentzianMetric.mk.injEq` (`Lightlike/Spacetime/Lorentzian.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Causal.isOpen_chronFuture

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

/-- **The chronological future is open.** -/
theorem isOpen_chronFuture (x : M) : IsOpen (chronFuture T x) := by
  sorry

end Lightlike.Causal
