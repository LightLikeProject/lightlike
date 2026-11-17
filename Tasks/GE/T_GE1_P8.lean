import Lightlike.Spacetime.Connection
import Lightlike.Spacetime.Minkowski

/-!
# Task T-GE1-P8

The Einstein tensor of a Levi-Civita connection is divergence free.

The statement is `Lightlike.einstein_divergence_free`, at the end of this file. Replace its `sorry`
by a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. Contract the second Bianchi identity (T-GE1-P7) twice, using the symmetries of the curvature
(T-GE1-P4) and metric compatibility.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Connection.lean`: `Connection`, `Connection.IsLeviCivita`,
  `Connection.divBilinAt`, `Connection.einsteinField`

Lemmas about them, which a proof may use:

* `gamHat_coord` (`Lightlike/Spacetime/ChartAgreement.lean`)
* `ricciAt_coord` (`Lightlike/Spacetime/ChartAgreement.lean`)
* `leviCivita_unique` (`Lightlike/Spacetime/LeviCivita.lean`)
* `riemann_coord_comp` (`Lightlike/Spacetime/ChartAgreement.lean`)
* `mvfderiv_gamHat_coord` (`Lightlike/Spacetime/ChartAgreement.lean`)
* `koszul_of_isLeviCivita` (`Lightlike/Spacetime/LeviCivita.lean`)
* `scalarCurvatureAt_coord` (`Lightlike/Spacetime/ChartAgreement.lean`)
* `leviCivita_exists_unique_proved` (`Lightlike/Spacetime/LeviCivita.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.einstein_divergence_free

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

/-- **The contracted Bianchi identity.** `∇^μ G_{μν} = 0` for `G = Ric - (S/2) g` of the Levi-Civita
connection of a Lorentzian metric. -/
theorem einstein_divergence_free (g : LorentzianMetric I M n) (cov : Connection I M)
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (h : cov.IsLeviCivita g) (x : M)
    (w : TangentSpace I x) :
    cov.divBilinAt g (cov.einsteinField g) x w = 0 := by
  sorry

end Lightlike
