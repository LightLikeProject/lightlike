import Lightlike.Spacetime.Connection
import Lightlike.GR.Einstein

/-!
# Task T-GE1-P3

The Ricci tensor of a Levi-Civita connection is symmetric.

The statement is `Lightlike.ricciAt_symm`, at the end of this file. Replace its `sorry` by a proof
and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. First Bianchi identity and the pair symmetry of the lowered curvature (T-GE1-P4), then trace.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Connection.lean`: `Connection`, `Connection.IsLeviCivita`,
  `Connection.ricciAt`

Lemmas about them, which a proof may use:

* `leviCivita_unique` (`Lightlike/Spacetime/LeviCivita.lean`)
* `koszul_of_isLeviCivita` (`Lightlike/Spacetime/LeviCivita.lean`)
* `leviCivita_exists_unique_proved` (`Lightlike/Spacetime/LeviCivita.lean`)
* `g_sharp` (`Lightlike/Spacetime/LeviCivita.lean`)
* `hat_cov` (`Lightlike/Spacetime/ChartCurvature.lean`)
* `g_leviOf` (`Lightlike/Spacetime/LeviCivita.lean`)
* `g_leviAux` (`Lightlike/Spacetime/LeviCivita.lean`)
* `gam_apply` (`Lightlike/Spacetime/ChartCurvature.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.ricciAt_symm

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

/-- **Symmetry of Ricci.** For the Levi-Civita connection of a Lorentzian metric, `Ric(v, w) = Ric(w, v)`. -/
theorem ricciAt_symm (g : LorentzianMetric I M n) (cov : Connection I M) [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (h : cov.IsLeviCivita g) (x : M) (v w : TangentSpace I x) :
    cov.ricciAt x v w = cov.ricciAt x w v := by
  sorry

end Lightlike
