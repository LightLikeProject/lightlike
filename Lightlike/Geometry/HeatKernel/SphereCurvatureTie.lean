import Lightlike.Geometry.HeatKernel.StereoCurvature
import Lightlike.Geometry.HeatKernel.Sphere3Expansion
import Lightlike.Geometry.HeatKernel.Consistency

/-!
# The scalar-curvature input of the sphere heat-trace expansions is Lightlike's curvature

On the round unit spheres `S²` and `S³`, the exact heat traces `Σ (2l+1) e^{-t l(l+1)}` and
`Σ (l+1)² e^{-t l(l+2)}` have the Seeley–DeWitt coefficients `heatCoeffs n V R ric riem` where `R` is
*Lightlike's coordinate scalar curvature* `Lightlike.scalarCurvature` of the stereographic metric
`4(1+|y|²)⁻² δ` at the origin (`scalarCurvature_stereo`), not a literal.  Only `R` (the quantity in `a₁`)
is computed from the curvature API; `|Ric|²` and `|Riem|²` (entering `a₂` only) remain literals.
-/

open Filter Topology Asymptotics Real

noncomputable section

namespace Lightlike.HeatKernel

/-- **`S³` heat trace with `R` = Lightlike's scalar curvature.** -/
theorem hasHeatExpansionTo_sphere3Trace_curv :
    HasHeatExpansionTo 3 3 sphere3Trace
      (heatCoeffs 3 (2 * π ^ 2) (scalarCurvature (confMetric (stereoF 3)) 0) 12 12) := by
  rw [scalarCurvature_stereo_three]
  exact hasHeatExpansionTo_sphere3Trace_geom

/-- **`S²` heat trace with `R` = Lightlike's scalar curvature.** -/
theorem hasHeatExpansionTo_sphereTrace_curv :
    HasHeatExpansionTo 2 3 sphereTrace
      (heatCoeffs 2 (4 * π) (scalarCurvature (confMetric (stereoF 2)) 0) 2 4) := by
  rw [scalarCurvature_stereo_two]
  exact hasHeatExpansionTo_sphereTrace_geom

/-- **`a₁ = (4π)^{-3/2} V R/6` on the round `S³`** for any expansion of the heat trace to order
`≥ 2`, with `R` Lightlike's scalar curvature of the round metric. -/
theorem sphere3_a1_curv {a : ℕ → ℝ}
    (ha : HasHeatExpansionTo 3 3 sphere3Trace a) :
    a 1 = (4 * π) ^ (-((3 : ℕ) / 2 : ℝ)) * (2 * π ^ 2) *
      scalarCurvature (confMetric (stereoF 3)) 0 / 6 :=
  heatCoeffs_one_unique (by norm_num) ha hasHeatExpansionTo_sphere3Trace_curv

/-- **`a₁ = (4π)^{-1} V R/6` on the round `S²`** for any expansion of the heat trace to order
`≥ 2`, with `R` Lightlike's scalar curvature of the round metric. -/
theorem sphere2_a1_curv {a : ℕ → ℝ}
    (ha : HasHeatExpansionTo 2 3 sphereTrace a) :
    a 1 = (4 * π) ^ (-((2 : ℕ) / 2 : ℝ)) * (4 * π) *
      scalarCurvature (confMetric (stereoF 2)) 0 / 6 :=
  heatCoeffs_one_unique (by norm_num) ha hasHeatExpansionTo_sphereTrace_curv

end Lightlike.HeatKernel
