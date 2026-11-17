import Lightlike.Spacetime.Causal.MinkowskiCausal

/-!
# Task T-GE2-P16

The slice t = 0 is a Cauchy surface of Minkowski space.

The statement is `Lightlike.Causal.minkowski_isCauchySurface`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. The time coordinate is strictly increasing along a timelike curve and unbounded on an
inextendible one (the cone is bounded by lines).

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Causal/Ladder.lean`: `Causal.IsCauchySurface`
* `Lightlike/Spacetime/Minkowski.lean`: `minkowskiMetric`
* `Lightlike/Spacetime/Causal/MinkowskiCausal.lean`: `Causal.minkowskiOrientation`

Lemmas about them, which a proof may use:

* `Causal.line_mem_chronFuture` (`Lightlike/Spacetime/Causal/MinkowskiCausal.lean`)
* `Causal.isFutureTimelikeCurve_line` (`Lightlike/Spacetime/Causal/MinkowskiCausal.lean`)
* `minkowski_flat` (`Lightlike/Spacetime/Curvature.lean`)
* `minkowski_coordMetric` (`Lightlike/Spacetime/Curvature.lean`)
* `minkowski_isCoordMetric` (`Lightlike/Spacetime/Curvature.lean`)
* `minkowski_isVacuumSolution` (`Lightlike/GR/Einstein.lean`)
* `minkowski_not_vacuumSolution_of_ne_zero` (`Lightlike/GR/Einstein.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Causal.minkowski_isCauchySurface

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

/-- **The slice t = 0 is a Cauchy surface of Minkowski space.** -/
theorem minkowski_isCauchySurface :
    IsCauchySurface (minkowskiOrientation d) {y : Fin (d + 1) → ℝ | y 0 = 0} := by
  sorry

end Lightlike.Causal
