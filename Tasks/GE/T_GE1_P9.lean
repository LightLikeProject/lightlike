import Lightlike.Spacetime.Connection
import Lightlike.Spacetime.Minkowski

/-!
# Task T-GE1-P9

Minkowski space solves the Einstein equations on the manifold.

The statement is `Lightlike.minkowski_satisfiesEinstein`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. {'The connection is the trivial one, `∇_v Y = Dy(v)`': 'it is torsion free, compatible with
the constant metric, and its curvature vanishes.'}

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Connection.lean`: `Connection`, `LorentzianMetric.SatisfiesEinstein`
* `Lightlike/Spacetime/Minkowski.lean`: `minkowskiMetric`

Lemmas about them, which a proof may use:

* `minkowski_flat` (`Lightlike/Spacetime/Curvature.lean`)
* `minkowski_coordMetric` (`Lightlike/Spacetime/Curvature.lean`)
* `minkowski_isCoordMetric` (`Lightlike/Spacetime/Curvature.lean`)
* `minkowski_isVacuumSolution` (`Lightlike/GR/Einstein.lean`)
* `minkowski_not_vacuumSolution_of_ne_zero` (`Lightlike/GR/Einstein.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.minkowski_satisfiesEinstein

## References

Milestone GE1 (Smooth curvature from connections), ROADMAP section "Lorentzian and Riemannian
geometry".
Source: S. M. Carroll, Lecture Notes on General Relativity (1997), Chapter 3 (`carroll-1997` in
docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle
open scoped Manifold ContDiff

namespace Lightlike

/-- **Minkowski space is a vacuum solution.** The Minkowski metric of `ℝⁿ` has a connection for which
it satisfies the Einstein equations with `Λ = 0` (non-vacuity of `SatisfiesEinstein`). -/
theorem minkowski_satisfiesEinstein (n : ℕ) :
    ∃ cov : Connection 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ),
      (minkowskiMetric n).SatisfiesEinstein cov 0 := by
  sorry

end Lightlike
