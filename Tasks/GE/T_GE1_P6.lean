import Lightlike.Spacetime.Connection
import Lightlike.GR.Einstein

/-!
# Task T-GE1-P6

The manifold-level Einstein equations are the coordinate ones in every chart.

The statement is `Lightlike.satisfiesEinstein_iff_chart`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. T-GE1-P5 and its Ricci version in a chart; the `IsCoordMetric` part is `LorentzianMetric.isCoordMetric_coordMetric`.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* Lightlike/Spacetime/Connection.lean: `LorentzianMetric.SatisfiesEinstein`; Lightlike/GR/Einstein.lean: `IsVacuumSolution`

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.satisfiesEinstein_iff_chart

## References

Milestone GE1 (smooth curvature from connections), ROADMAP section "Lorentzian and Riemannian geometry".
Structural: statement of the manifold-level theory of `Lightlike/Spacetime/Connection.lean`; the
conventions are those of Mathlib pull request 45069 for the curvature sign and signature `(-,+,…,+)`.
Reference for the content: Wald, General Relativity (1984), eq. (4.3.1) with cosmological constant (Appendix D); not yet a verified location in docs/tasks/sources.yaml.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle
open scoped Manifold ContDiff

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 1 M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]

/-- **Einstein equations in a chart.** With `cov` the Levi-Civita connection, the manifold-level
Einstein equations `Ric - (S/2) g + Λ g = 0` hold iff the chart components of `g` solve the
coordinate equations `G + Λ g = 0` (`IsVacuumSolution`) in every chart. -/
theorem satisfiesEinstein_iff_chart (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (h : cov.IsLeviCivita g) (Λ : ℝ) :
    g.SatisfiesEinstein cov Λ ↔
      ∀ x₀ : M, IsVacuumSolution Λ (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
  sorry

end Lightlike
