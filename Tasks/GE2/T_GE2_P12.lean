import Lightlike.Spacetime.CausalLadder.GlobHypSimple

/-!
# Task T-GE2-P12

Global hyperbolicity implies causal simplicity.

The statement is `Lightlike.Causal.isCausallySimple_of_isGloballyHyperbolic`, at the end of this
file. Replace its `sorry` by a proof and change nothing else in the file: the proof-task check
rejects any other change (CONTRIBUTING.md).

Hint. The limit curve theorem for causal curves with endpoints converging, using compactness of the
diamonds.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Causal/TimeOrientation.lean`: `Causal.TimeOrientation`
* `Lightlike/Spacetime/Causal/Ladder.lean`: `Causal.IsGloballyHyperbolic`, `Causal.IsCausallySimple`

Lemmas about them, which a proof may use:

* `Causal.TimeOrientation.mk.inj` (`Lightlike/Spacetime/Causal/TimeOrientation.lean`)
* `Causal.TimeOrientation.timelike` (`Lightlike/Spacetime/Causal/TimeOrientation.lean`)
* `Causal.TimeOrientation.mk.injEq` (`Lightlike/Spacetime/Causal/TimeOrientation.lean`)
* `Causal.TimeOrientation.contMDiff` (`Lightlike/Spacetime/Causal/TimeOrientation.lean`)
* `Causal.TimeOrientation.mk.sizeOf_spec` (`Lightlike/Spacetime/Causal/TimeOrientation.lean`)
* `LorentzianMetric.symm` (`Lightlike/Spacetime/Lorentzian.lean`)
* `LorentzianMetric.mk.inj` (`Lightlike/Spacetime/Lorentzian.lean`)
* `LorentzianMetric.mk.injEq` (`Lightlike/Spacetime/Lorentzian.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Causal.isCausallySimple_of_isGloballyHyperbolic

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

/-- **Global hyperbolicity implies causal simplicity.** The hypothesis `[BoundarylessManifold I M]`
matches the source (Hawking–Ellis: space-time has no boundary); approved by the maintainers,
18 November 2026. -/
theorem isCausallySimple_of_isGloballyHyperbolic [T2Space M] [SecondCountableTopology M]
    [BoundarylessManifold I M] (h : IsGloballyHyperbolic T) : IsCausallySimple T := by
  exact isCausallySimple_of_isGloballyHyperbolic_boundaryless T h

end Lightlike.Causal
