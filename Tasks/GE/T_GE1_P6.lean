import Lightlike.Spacetime.Connection
import Lightlike.GR.Einstein

/-!
# Task T-GE1-P6

The manifold-level Einstein equations are the coordinate ones in every chart.

The statement is `Lightlike.satisfiesEinstein_iff_chart`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. T-GE1-P5 and its Ricci version in a chart; the `IsCoordMetric` part is
`LorentzianMetric.isCoordMetric_coordMetric`.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Connection.lean`: `Connection`, `Connection.IsLeviCivita`,
  `LorentzianMetric.SatisfiesEinstein`
* `Lightlike/GR/Einstein.lean`: `IsVacuumSolution`
* `Lightlike/Spacetime/Curvature.lean`: `LorentzianMetric.coordMetric`

Lemmas about them, which a proof may use:

* `satisfiesEinstein_iff_chart_proved` (`Lightlike/Spacetime/ChartAgreement.lean`)
* `gamHat_coord` (`Lightlike/Spacetime/ChartAgreement.lean`)
* `ricciAt_coord` (`Lightlike/Spacetime/ChartAgreement.lean`)
* `riemann_coord_comp` (`Lightlike/Spacetime/ChartAgreement.lean`)
* `mvfderiv_gamHat_coord` (`Lightlike/Spacetime/ChartAgreement.lean`)
* `scalarCurvatureAt_coord` (`Lightlike/Spacetime/ChartAgreement.lean`)
* `leviCivita_unique` (`Lightlike/Spacetime/LeviCivita.lean`)
* `einsteinField_eq_bilOf` (`Lightlike/Spacetime/ChartTensor.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.satisfiesEinstein_iff_chart

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
