import Lightlike.Geometry.HeatKernel.ProductGeom
import Lightlike.Geometry.HeatKernel.Sphere3Expansion

/-!
# Heat traces of products with the round `S³`

Products of the unit round `S³` with the flat torus, `S²` and `S³` itself: the heat trace is the
product of the heat traces, and its expansion coefficients are the Cauchy product, which
`heatCoeffs_conv` identifies with the Seeley–DeWitt coefficients of the product manifold
(volume `V V'`, scalar curvature `R + R'`, `|Ric|²` and `|Riem|²` additive).

## Main results

* `hasHeatExpansionTo_sphere3_prod_torus`: `S³ × Tⁿ`.
* `hasHeatExpansionTo_sphere3_prod_sphere`: `S³ × S²`.
* `hasHeatExpansionTo_sphere3_prod_sphere3`: `S³ × S³`.
* `heatCoeffs_one_sphere3_prod_torus`: `a₁(S³ × Tⁿ) = (4π)^{-(3+n)/2} V R / 6` with `R = 6`.
-/

open Filter Topology Asymptotics Real

noncomputable section

namespace Lightlike.HeatKernel

/-- **Heat trace of `S³ × Tⁿ`** (unit round `S³`, flat torus `ℝⁿ/(2πℤ)ⁿ`): expansion to order `t²`
relative to `t^{-(3+n)/2}`, with `V = 2π² (2π)ⁿ`, `R = 6`, `|Ric|² = |Riem|² = 12`. -/
theorem hasHeatExpansionTo_sphere3_prod_torus (n : ℕ) :
    HasHeatExpansionTo (3 + n) 3 (fun t => sphere3Trace t * torusTrace n t)
      (heatCoeffs (3 + n) ((2 * π ^ 2) * (2 * π) ^ n) (6 + 0) (12 + 0) (12 + 0)) := by
  refine (hasHeatExpansionTo_sphere3Trace_geom.mul
    ((hasHeatExpansion_torusTrace_geom n).to 3)).congr_coeff ?_
  intro k hk
  exact heatCoeffs_conv 3 n _ _ _ _ _ _ _ _ hk

/-- **Heat trace of `S³ × S²`** (unit round factors): `V = 2π² · 4π`, `R = 6 + 2`,
`|Ric|² = 12 + 2`, `|Riem|² = 12 + 4`. -/
theorem hasHeatExpansionTo_sphere3_prod_sphere :
    HasHeatExpansionTo (3 + 2) 3 (fun t => sphere3Trace t * sphereTrace t)
      (heatCoeffs (3 + 2) ((2 * π ^ 2) * (4 * π)) (6 + 2) (12 + 2) (12 + 4)) := by
  refine (hasHeatExpansionTo_sphere3Trace_geom.mul hasHeatExpansionTo_sphereTrace_geom).congr_coeff ?_
  intro k hk
  exact heatCoeffs_conv 3 2 _ _ _ _ _ _ _ _ hk

/-- **Heat trace of `S³ × S³`** (unit round factors): `V = (2π²)²`, `R = 12`, `|Ric|² = |Riem|² = 24`. -/
theorem hasHeatExpansionTo_sphere3_prod_sphere3 :
    HasHeatExpansionTo (3 + 3) 3 (fun t => sphere3Trace t * sphere3Trace t)
      (heatCoeffs (3 + 3) ((2 * π ^ 2) * (2 * π ^ 2)) (6 + 6) (12 + 12) (12 + 12)) := by
  refine (hasHeatExpansionTo_sphere3Trace_geom.mul hasHeatExpansionTo_sphere3Trace_geom).congr_coeff ?_
  intro k hk
  exact heatCoeffs_conv 3 3 _ _ _ _ _ _ _ _ hk

/-- On `S³ × Tⁿ` the coefficient `a₁` of the heat trace is the geometric
`(4π)^{-(3+n)/2} V R / 6`, `R = 6`: any expansion of the trace to order `≥ 2` has this `a₁`. -/
theorem heatCoeffs_one_sphere3_prod_torus (n : ℕ) {a : ℕ → ℝ}
    (ha : HasHeatExpansionTo (3 + n) 3 (fun t => sphere3Trace t * torusTrace n t) a) :
    a 1 = (4 * π) ^ (-(((3 + n : ℕ) : ℝ) / 2)) * ((2 * π ^ 2) * (2 * π) ^ n) * 6 / 6 := by
  have := heatCoeffs_one_unique (by norm_num : 2 ≤ 3) ha (hasHeatExpansionTo_sphere3_prod_torus n)
  simpa using this

end Lightlike.HeatKernel
