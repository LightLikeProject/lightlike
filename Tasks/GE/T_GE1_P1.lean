import Lightlike.Spacetime.Connection
import Lightlike.GR.Einstein

/-!
# Task T-GE1-P1

Existence and uniqueness of the Levi-Civita connection of a Lorentzian metric.

The statement is `Lightlike.leviCivita_exists_unique`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. Koszul formula as in Mathlib's `CovariantDerivative.leviCivitaConnection` (Riemannian case, `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`): the formula needs only non-degeneracy of `g`, not positivity; use the musical isomorphism of `LinearMap.BilinForm.toDual` (nondegenerate by `IsLorentzianForm.bilinForm_nondegenerate`). Uniqueness is on differentiable fields, as in Mathlib.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* Lightlike/Spacetime/Connection.lean: `Connection`, `Connection.IsLeviCivita`

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.leviCivita_exists_unique

## References

Milestone GE1 (smooth curvature from connections), ROADMAP section "Lorentzian and Riemannian geometry".
Structural: statement of the manifold-level theory of `Lightlike/Spacetime/Connection.lean`; the
conventions are those of Mathlib pull request 45069 for the curvature sign and signature `(-,+,…,+)`.
Reference for the content: O'Neill, Semi-Riemannian Geometry (1983), Theorem 3.11 (the fundamental theorem); not yet a verified location in docs/tasks/sources.yaml.
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
