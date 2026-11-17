import Lightlike.Spacetime.Connection
import Lightlike.Spacetime.Minkowski

/-!
# Task T-GE1-P7

The second Bianchi identity of a Levi-Civita connection.

The statement is `Lightlike.bianchi_second`, at the end of this file. Replace its `sorry` by a proof
and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. {'Torsion-freeness and the Jacobi identity': 'evaluate the cyclic sum on extensions of the
vectors with vanishing brackets at the point (coordinate fields of a chart), where it reduces to the
Jacobi identity for the covariant derivatives.'}

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Connection.lean`: `Connection`, `Connection.IsLeviCivita`,
  `Connection.covDerivCurvatureAt`

Lemmas about them, which a proof may use:

* `leviCivita_unique` (`Lightlike/Spacetime/LeviCivita.lean`)
* `koszul_of_isLeviCivita` (`Lightlike/Spacetime/LeviCivita.lean`)
* `leviCivita_exists_unique_proved` (`Lightlike/Spacetime/LeviCivita.lean`)
* `compat_mv` (`Lightlike/Spacetime/CurvatureSymmetries.lean`)
* `compat_mv'` (`Lightlike/Spacetime/CurvatureSymmetries.lean`)
* `ricciAt_eq_sum` (`Lightlike/Spacetime/CurvatureSymmetries.lean`)
* `ricciAt_symm_proved` (`Lightlike/Spacetime/CurvatureSymmetries.lean`)
* `riemann_antisymm_aux` (`Lightlike/Spacetime/CurvatureSymmetries.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.bianchi_second

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I 2 M] [CompleteSpace E] {n : ℕ}

/-- **Second Bianchi identity.** `(∇_X R)(Y, Z) W + (∇_Y R)(Z, X) W + (∇_Z R)(X, Y) W = 0` for the
Levi-Civita connection of a Lorentzian metric. -/
theorem bianchi_second (g : LorentzianMetric I M n) (cov : Connection I M)
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (h : cov.IsLeviCivita g) (x : M)
    (X Y Z W : TangentSpace I x) :
    cov.covDerivCurvatureAt x X Y Z W + cov.covDerivCurvatureAt x Y Z X W
      + cov.covDerivCurvatureAt x Z X Y W = 0 := by
  sorry

end Lightlike
