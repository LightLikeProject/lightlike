import Lightlike.Spacetime.Connection
import Lightlike.GR.Einstein

/-!
# Task T-GE1-P3

The Ricci tensor of a Levi-Civita connection is symmetric.

The statement is `Lightlike.ricciAt_symm`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. First Bianchi identity and the pair symmetry of the lowered curvature (T-GE1-P4), then trace.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* Lightlike/Spacetime/Connection.lean: `Connection.ricciAt`, `Connection.IsLeviCivita`

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.ricciAt_symm

## References

Milestone GE1 (smooth curvature from connections), ROADMAP section "Lorentzian and Riemannian geometry".
Structural: statement of the manifold-level theory of `Lightlike/Spacetime/Connection.lean`; the
conventions are those of Mathlib pull request 45069 for the curvature sign and signature `(-,+,…,+)`.
Reference for the content: Wald, General Relativity (1984), eq. (3.2.12) and Section 3.2; not yet a verified location in docs/tasks/sources.yaml.
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
