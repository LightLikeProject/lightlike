import Lightlike.Spacetime.Connection
import Lightlike.GR.Einstein

/-!
# Task T-GE1-P2

The curvature tensor is computed by any smooth extensions.

The statement is `Lightlike.curvatureAt_apply`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. Tensoriality of `(X, Y, Z) ↦ ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` in each slot, as `torsion_apply` in Mathlib's `CovariantDerivative/Torsion.lean`, with `TensorialAt.mkHom`.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* Lightlike/Spacetime/Connection.lean: `Connection.curvatureAt`

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.curvatureAt_apply

## References

Milestone GE1 (smooth curvature from connections), ROADMAP section "Lorentzian and Riemannian geometry".
Structural: statement of the manifold-level theory of `Lightlike/Spacetime/Connection.lean`; the
conventions are those of Mathlib pull request 45069 for the curvature sign and signature `(-,+,…,+)`.
Reference for the content: Wald, General Relativity (1984), eq. (3.2.11); not yet a verified location in docs/tasks/sources.yaml.
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
