import Lightlike.Spacetime.Connection
import Lightlike.GR.Einstein

/-!
# Task T-GE1-P2

The curvature tensor is computed by any smooth extensions.

The statement is `Lightlike.curvatureAt_apply`, at the end of this file. Replace its `sorry` by a
proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. Tensoriality of `(X, Y, Z) ↦ ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` in each slot, as
`CovariantDerivative.torsion_apply` (Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Torsion.lean), with `TensorialAt.mkHom`.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Connection.lean`: `Connection`, `Connection.curvatureAt`

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.curvatureAt_apply

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

/-- **The curvature does not depend on the extension.** For smooth vector fields `X, Y, Z` and a smooth
connection, `curvatureAt` at `x` of their values is `∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` at `x`. -/
theorem curvatureAt_apply (cov : Connection I M) [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (X Y Z : Π x : M, TangentSpace I x)
    (hX : ContMDiff I I.tangent ∞ (T% X)) (hY : ContMDiff I I.tangent ∞ (T% Y))
    (hZ : ContMDiff I I.tangent ∞ (T% Z)) (x : M) :
    cov.curvatureAt x (X x) (Y x) (Z x) =
      cov (fun y => cov Z y (Y y)) x (X x) - cov (fun y => cov Z y (X y)) x (Y x)
        - cov Z x (mlieBracket I X Y x) := by
  sorry

end Lightlike
