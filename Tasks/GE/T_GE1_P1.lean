import Lightlike.Spacetime.Connection
import Lightlike.GR.Einstein

/-!
# Task T-GE1-P1

Existence and uniqueness of the Levi-Civita connection of a Lorentzian metric.

The statement is `Lightlike.leviCivita_exists_unique`, at the end of this file. Replace its `sorry`
by a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. {"Koszul formula as in Mathlib's `CovariantDerivative.leviCivitaConnection` (Riemannian
case)": 'it needs only non-degeneracy of `g`; use the musical isomorphism
`LinearMap.BilinForm.toDual` (nondegenerate by `IsLorentzianForm.bilinForm_nondegenerate`).
Uniqueness is on differentiable fields, as in Mathlib.'}

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Connection.lean`: `Connection`, `Connection.IsLeviCivita`

Lemmas about them, which a proof may use:

* `LorentzianMetric.symm` (`Lightlike/Spacetime/Lorentzian.lean`)
* `LorentzianMetric.mk.inj` (`Lightlike/Spacetime/Lorentzian.lean`)
* `LorentzianMetric.mk.injEq` (`Lightlike/Spacetime/Lorentzian.lean`)
* `LorentzianMetric.contMDiff` (`Lightlike/Spacetime/Lorentzian.lean`)
* `LorentzianMetric.lorentzian` (`Lightlike/Spacetime/Lorentzian.lean`)
* `LorentzianMetric.nondegenerate` (`Lightlike/Spacetime/Lorentzian.lean`)
* `LorentzianMetric.mk.sizeOf_spec` (`Lightlike/Spacetime/Lorentzian.lean`)
* `LorentzianMetric.coordMetric_eq` (`Lightlike/Spacetime/Coordinates.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.leviCivita_exists_unique

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

/-- **The fundamental theorem of Lorentzian geometry.** A Lorentzian metric has a Levi-Civita
connection (torsion-free and compatible with `g`), and two of them agree on every vector field
differentiable at a point. -/
theorem leviCivita_exists_unique (g : LorentzianMetric I M n) :
    (∃ cov : Connection I M, cov.IsLeviCivita g) ∧
      ∀ cov cov' : Connection I M, cov.IsLeviCivita g → cov'.IsLeviCivita g →
        ∀ (Y : Π x : M, TangentSpace I x) (x : M), MDiffAt (T% Y) x → cov Y x = cov' Y x := by
  sorry

end Lightlike
