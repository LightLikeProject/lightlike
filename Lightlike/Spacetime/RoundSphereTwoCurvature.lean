import Mathlib
import Lightlike.Spacetime.RoundSphereTwoCoord
import Lightlike.Spacetime.Corners.ChartAgreement
import Lightlike.Spacetime.Corners.LeviCivitaSmooth
import Lightlike.Spacetime.SchwarzschildManifold
import Lightlike.Geometry.HeatKernel.RoundCurvature

/-!
# The round 2-sphere of radius `r` has scalar curvature `2 / r²`

`roundSphere2_scalarCurvatureAt`: for every locally smooth Levi-Civita connection of the metric `r² h` of the round
2-sphere `S²` (Mathlib's manifold, modelled on `Fin 2 → ℝ` through `I2`), the intrinsic scalar curvature `scalarCurvatureAt`
is `2 / r²` at **every point of the whole sphere**.

Proof. The scalar curvature is the coordinate one in every chart (`scalarCurvatureAt_coordW`), and Mathlib's atlas has,
at every point `x`, the stereographic chart from `-x`, which sends `x` to the origin; there the coordinate metric is
`16 r² / (|y|² + 4)²` times the identity (`coordMetric_round2`) on the whole chart (its target is all of `ℝ²`), whose scalar
curvature at the origin is `2 / r²` (`scalarCurvature_roundF_zero`).

**Differences from the cited statement** (comparison with Lee, *Introduction to Riemannian Manifolds*, ch. 7, pending):
the sphere of radius `r` is the unit sphere of Mathlib with the metric `r² h` (isometric to it), `r ≠ 0`.
-/

open Manifold Metric Bundle TopologicalSpace Set
open scoped ContDiff
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

variable (r : ℝ) (hr : r ≠ 0)

/-- The chart of Mathlib's atlas at `x` sends `x` to the origin. -/
theorem extChartAt_I2_self (x : S2) : extChartAt I2 x x = 0 := by
  simp [extChartAt, I2, modelEquiv2]
  change (stereographic' 2 (-x)) x = 0
  simp only [stereographic', OpenPartialHomeomorph.trans_apply]
  have h0 := stereographic_neg_apply (E := EuclideanSpace ℝ (Fin (2 + 1))) x
  erw [h0]
  exact map_zero (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere (-x))).repr

/-- The coordinate metric of the round sphere in every chart is the conformally flat metric `roundF`. -/
theorem coordMetric_round2_eq (x : S2) :
    (roundMetric2I r hr).coordMetricW x = HeatKernel.confMetric (HeatKernel.roundF 2 r) := by
  funext y
  have hy : y ∈ (extChartAt I2 x).target := by
    simp only [I2, ModelWithCorners.extChartAt_transContinuousLinearEquiv_target, Set.mem_preimage,
      target_sphere_chart2]
    trivial
  rw [coordMetric_round2 r hr x hy]
  unfold HeatKernel.confMetric HeatKernel.roundF HeatKernel.roundQ
  congr 1
  have : (∑ i, y i ^ 2 + 4) = 4 + ∑ i, y i ^ 2 := by ring
  rw [this]
  field_simp

variable (cov : Connection I2 S2) [LocallySmoothConnectionW cov]

/-- **The round 2-sphere of radius `r` has scalar curvature `2 / r²`**: for the intrinsic `scalarCurvatureAt` of every locally
smooth Levi-Civita connection of `roundMetric2I r hr`, at every point of the whole sphere `S²`. -/
theorem roundSphere2_scalarCurvatureAt (h : cov.IsLeviCivita (roundMetric2I r hr)) (x : S2) :
    cov.scalarCurvatureAt (roundMetric2I r hr) x = 2 / r ^ 2 := by
  have hzs : x ∈ (extChartAt I2 x).source := mem_extChartAt_source x
  have hy : extChartAt I2 x x ∈ (extChartAt I2 x).target := (extChartAt I2 x).map_source hzs
  have hS := scalarCurvatureAt_coordW cov x (roundMetric2I r hr) h hy
  rw [(extChartAt I2 x).left_inv hzs] at hS
  rw [hS, range_I2, scalarCurvatureW_univ, coordMetric_round2_eq r hr x, extChartAt_I2_self]
  exact HeatKernel.scalarCurvature_roundF_zero hr

/-- **Non-vacuity**: the Levi-Civita connection `leviCivita` of the round metric is a locally smooth Levi-Civita connection
of `roundMetric2I r hr`, so the theorem applies to it. -/
theorem roundSphere2_exists_leviCivita :
    ∃ cov : Connection I2 S2, LocallySmoothConnectionW cov ∧ cov.IsLeviCivita (roundMetric2I r hr) :=
  ⟨leviCivita (roundMetric2I r hr), inferInstance, ⟨leviCivita_torsion _, leviCivita_compat _⟩⟩

end Lightlike
