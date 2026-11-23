import Lightlike.Geometry.HeatKernel.Product
import Lightlike.Geometry.HeatKernel.Consistency

/-!
# Seeley–DeWitt coefficients are compatible with Riemannian products

For a product `M × M'` of closed manifolds with constant curvature invariants, the volume is
`V V'`, the scalar curvature `R + R'`, and `|Ric|²`, `|Riem|²` add (the curvature tensors are block
diagonal). The heat trace is the product of heat traces, whose expansion coefficients are the Cauchy
product (`HasHeatExpansionTo.mul`). We prove that `heatCoeffs` is multiplicative in exactly this
sense up to `a₂` (`heatCoeffs_conv`): in particular `a₁(M × M') = a₀(M) a₁(M') + a₁(M) a₀(M')`
equals `(4π)^{-(n+m)/2} V V' (R + R')/6`.  This is a consistency check of the formula for `a₁`
(and `a₂`) on a family of manifolds beyond the two base cases, with products of the unit `S²` and
flat tori as examples.

## Main results

* `heatCoeffs_conv`: `convCoeff (heatCoeffs n …) (heatCoeffs m …) = heatCoeffs (n+m) …` for `k < 3`.
* `hasHeatExpansionTo_sphere_prod_sphere`: heat trace of `S² × S²`.
* `hasHeatExpansionTo_sphere_prod_torus`: heat trace of `S² × Tⁿ`.
-/

open Filter Topology Asymptotics Real

noncomputable section

namespace Lightlike.HeatKernel

/-- `heatCoeffs` turns products of manifolds into Cauchy products, up to `a₂`. -/
theorem heatCoeffs_conv (n m : ℕ) (V V' R R' r r' s s' : ℝ) {k : ℕ} (hk : k < 3) :
    convCoeff (heatCoeffs n V R r s) (heatCoeffs m V' R' r' s') k
      = heatCoeffs (n + m) (V * V') (R + R') (r + r') (s + s') k := by
  have hcc : (4 * π) ^ (-((n : ℝ) / 2)) * (4 * π) ^ (-((m : ℝ) / 2))
      = (4 * π) ^ (-(((n + m : ℕ) : ℝ) / 2)) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    push_cast
    ring
  interval_cases k
  · rw [convCoeff_zero]
    simp only [heatCoeffs]
    rw [← hcc]
    ring
  · rw [convCoeff_one]
    simp only [heatCoeffs]
    rw [← hcc]
    ring
  · rw [convCoeff_two]
    simp only [heatCoeffs]
    rw [← hcc]
    ring

/-- **Heat trace of `S² × S²`** (unit round factors): expansion to order `t²` relative to
`t^{-2}`, with the Seeley–DeWitt coefficients of `V = 16π²`, `R = 4`, `|Ric|² = 4`, `|Riem|² = 8`. -/
theorem hasHeatExpansionTo_sphere_prod_sphere :
    HasHeatExpansionTo (2 + 2) 3 (fun t => sphereTrace t * sphereTrace t)
      (heatCoeffs (2 + 2) ((4 * π) * (4 * π)) (2 + 2) (2 + 2) (4 + 4)) := by
  refine (hasHeatExpansionTo_sphereTrace_geom.mul hasHeatExpansionTo_sphereTrace_geom).congr_coeff ?_
  intro k hk
  exact heatCoeffs_conv 2 2 _ _ _ _ _ _ _ _ hk

/-- **Heat trace of `S² × Tⁿ`** (unit round `S²`, flat torus `ℝⁿ/(2πℤ)ⁿ`): `V = 4π (2π)ⁿ`,
`R = 2`, `|Ric|² = 2`, `|Riem|² = 4`. -/
theorem hasHeatExpansionTo_sphere_prod_torus (n : ℕ) :
    HasHeatExpansionTo (2 + n) 3 (fun t => sphereTrace t * torusTrace n t)
      (heatCoeffs (2 + n) ((4 * π) * (2 * π) ^ n) (2 + 0) (2 + 0) (4 + 0)) := by
  refine (hasHeatExpansionTo_sphereTrace_geom.mul
    ((hasHeatExpansion_torusTrace_geom n).to 3)).congr_coeff ?_
  intro k hk
  exact heatCoeffs_conv 2 n _ _ _ _ _ _ _ _ hk

end Lightlike.HeatKernel
