import Lightlike.Spacetime.Connection
import Lightlike.GR.Einstein

/-!
# Task T-GE1-P4

The first Bianchi identity and the pair symmetry of the lowered curvature.

The statement is `Lightlike.bianchi_first_and_pair_symm`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. Torsion-freeness gives the first identity (Jacobi identity of the Lie bracket); metric
compatibility gives antisymmetry in the last pair; the pair symmetry follows by the usual four-term
argument.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Connection.lean`: `Connection`, `Connection.IsLeviCivita`,
  `Connection.curvatureAt`, `Connection.riemannLowerAt`

Lemmas about them, which a proof may use:

* `leviCivita_unique` (`Lightlike/Spacetime/LeviCivita.lean`)
* `koszul_of_isLeviCivita` (`Lightlike/Spacetime/LeviCivita.lean`)
* `leviCivita_exists_unique_proved` (`Lightlike/Spacetime/LeviCivita.lean`)
* `g_sharp` (`Lightlike/Spacetime/LeviCivita.lean`)
* `g_leviOf` (`Lightlike/Spacetime/LeviCivita.lean`)
* `sharp_add` (`Lightlike/Spacetime/LeviCivita.lean`)
* `g_leviAux` (`Lightlike/Spacetime/LeviCivita.lean`)
* `gpair_comm` (`Lightlike/Spacetime/LeviCivita.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.bianchi_first_and_pair_symm

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

/-- **Symmetries of the curvature of a Levi-Civita connection.** `R(X, Y) Z + R(Y, Z) X + R(Z, X) Y = 0`
and `g(R(X, Y) Z, W) = g(R(Z, W) X, Y)`. -/
theorem bianchi_first_and_pair_symm (g : LorentzianMetric I M n) (cov : Connection I M)
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (h : cov.IsLeviCivita g) (x : M)
    (X Y Z W : TangentSpace I x) :
    cov.curvatureAt x X Y Z + cov.curvatureAt x Y Z X + cov.curvatureAt x Z X Y = 0 ∧
      cov.riemannLowerAt g x X Y Z W = cov.riemannLowerAt g x Z W X Y := by
  sorry

end Lightlike
