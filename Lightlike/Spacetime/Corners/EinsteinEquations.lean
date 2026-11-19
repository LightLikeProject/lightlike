import Lightlike.Spacetime.CurvatureSymmetries
import Lightlike.Spacetime.Corners.CurvatureSymmetries
/-!
# The Einstein equations on a manifold: basic API

* `NondegMetric.EinsteinEqW g cov Λ κ T`: `cov` is the Levi-Civita connection of `g` and `G + Λ g = κ T` for a source `T`
  (a field of bilinear forms); `satisfiesEinstein_iff_einsteinEq_zero`: the equations of `Connection.lean`
  (`SatisfiesEinstein`) are the case `κ = 1`, `T = 0`.
* `scalarCurvatureAt_of_ricci_eq`: if `Ric = c g` at a point, the scalar curvature is `c d`, `d` the dimension.
* `satisfiesEinstein_iff_ricci`: in dimension `d ≠ 2`, `SatisfiesEinstein cov Λ` is `Ric = (2 Λ / (d - 2)) g` for the
  Levi-Civita connection; `satisfiesEinstein_zero_iff_ricci_eq_zero`: the vacuum equations are `Ric = 0`.

The relation to the coordinate equations in every chart is `satisfiesEinstein_iff_chart_proved` (`ChartAgreement.lean`), the
divergence-free property of `G` is `einstein_divergence_free_proved` (`DivergenceFree.lean`).

**Limits.** `C²` manifolds with corners (any `ModelWithCorners I`) modelled on a finite-dimensional space (the setting of
`CurvatureSymmetries.lean`); dimension `d = finrank ≠ 2` for the Ricci forms. No statement about the source `T` (its conservation
is not proved here).

This is the Corners layer of the CO30 branch: the versions for any model with corners of the declarations of
`Lightlike/Spacetime/EinsteinEquations.lean` that the CO30 and GE11 files use, with a `W` suffix where the boundaryless file owns the name.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology Matrix
noncomputable section
namespace Lightlike
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 2 M] [CompleteSpace E] (g : NondegMetric I M)
variable (cov : Connection I M)

/-- **The Einstein equations with a cosmological constant `Λ`, a coupling `κ` and a source `T`**: `cov` is the Levi-Civita connection of `g`
and `G + Λ g = κ T`. -/
def _root_.Lightlike.NondegMetric.EinsteinEqW (cov : Connection I M) (Λ κ : ℝ)
    (T : Π x : M, TangentSpace I x → TangentSpace I x → ℝ) : Prop :=
  cov.IsLeviCivita g ∧ ∀ x (v w : TangentSpace I x),
    cov.einsteinField g x v w + Λ * g.g x v w = κ * T x v w

end Lightlike
