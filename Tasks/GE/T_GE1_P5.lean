import Lightlike.Spacetime.Connection
import Lightlike.GR.Einstein

/-!
# Task T-GE1-P5

The intrinsic scalar curvature is the coordinate scalar curvature in every chart.

The statement is `Lightlike.scalarCurvatureAt_chart`, at the end of this file. Replace its `sorry`
by a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. In a chart the coordinate fields have vanishing brackets and `∇_{∂ᵢ} ∂ⱼ = Γᵏᵢⱼ ∂ₖ` (Koszul
formula); the coordinate formula of `Lightlike/Spacetime/Curvature.lean` is then the trace of
`curvatureAt`. This fixes the sign convention of the two definitions.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Connection.lean`: `Connection`, `Connection.IsLeviCivita`,
  `Connection.scalarCurvatureAt`
* `Lightlike/Spacetime/Curvature.lean`: `scalarCurvature`, `LorentzianMetric.coordMetric`

Lemmas about them, which a proof may use:

* `scalarCurvatureAt_coord` (`Lightlike/Spacetime/ChartAgreement.lean`)
* `gamHat_coord` (`Lightlike/Spacetime/ChartAgreement.lean`)
* `ricciAt_coord` (`Lightlike/Spacetime/ChartAgreement.lean`)
* `riemann_coord_comp` (`Lightlike/Spacetime/ChartAgreement.lean`)
* `mvfderiv_gamHat_coord` (`Lightlike/Spacetime/ChartAgreement.lean`)
* `divBilinAt_einstein_coord` (`Lightlike/Spacetime/DivergenceFree.lean`)
* `covDerivBilinAt_einstein_value` (`Lightlike/Spacetime/DivergenceFree.lean`)
* `satisfiesEinstein_iff_chart_proved` (`Lightlike/Spacetime/ChartAgreement.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.scalarCurvatureAt_chart

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

/-- **Agreement with the coordinate curvature.** For the Levi-Civita connection of a Lorentzian
metric on a manifold modelled on `ℝⁿ`, the intrinsic scalar curvature at a point of a chart is the
coordinate `scalarCurvature` of the chart components. -/
theorem scalarCurvatureAt_chart (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (h : cov.IsLeviCivita g) (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    cov.scalarCurvatureAt g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) =
      scalarCurvature (g.coordMetric x₀) y := by
  sorry

end Lightlike
