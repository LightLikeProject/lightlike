import Mathlib
import Lightlike.Geometry.HeatKernel.Unique
import Lightlike.Geometry.HeatKernel.Torus
import Lightlike.Geometry.HeatKernel.SphereTrace

/-!
# Seeley–DeWitt coefficients of `-Δ` on the two trust-check manifolds

For the scalar Laplacian `D = -Δ` on a closed Riemannian `n`-manifold of volume `V`, with constant
scalar curvature `R`, the Seeley–DeWitt coefficients (the row's `a₀, a₁, a₂`) are
`a₀ = (4π)^{-n/2} V`, `a₁ = (4π)^{-n/2} V R / 6` and (Gilkey's form, `E = 0`, constant curvature
invariants)
`a₂ = (4π)^{-n/2} V (5R² - 2|Ric|² + 2|Riem|²) / 360`.
We do not prove these for a general manifold (there is no Laplace–Beltrami operator or spectral
theory on manifolds in Mathlib or Lightlike); we record them as the function `heatCoeffs`, and prove
that the two concrete heat traces proved elsewhere in this folder have exactly these coefficients:

* unit round `S²` (`V = 4π`, `R = 2`, `|Ric|² = 2`, `|Riem|² = 4`):
  `hasHeatExpansionTo_sphereTrace_geom`, with `a₁ = 1/3`;
* flat torus `ℝⁿ/(2πℤ)ⁿ` (`V = (2π)ⁿ`, all curvature `0`): `hasHeatExpansion_torusTrace_geom`.

## Main results

* `heatCoeffs`: the coefficients `a₀, a₁, a₂` from the volume and curvature data.
* `HasHeatExpansionTo.congr_coeff`: only the first `m` coefficients matter.
* `heatCoeffs_one_unique`: `a₁` of any expansion of the trace is the geometric `(4π)^{-n/2} V R/6`.

## References

* Vassilevich, *Heat kernel expansion: user's manual* (key `vassilevich-2003`), eq. (4.27).
* Berline–Getzler–Vergne (key `bgv-1992`), chapter "Asymptotic Expansion of the Heat Kernel".
-/

open Filter Topology Asymptotics Real

noncomputable section

namespace Lightlike.HeatKernel

/-- Seeley–DeWitt coefficients `a₀, a₁, a₂` (others set to `0`) of `-Δ` on a closed `n`-manifold of
volume `V` with constant scalar curvature `R` and constant `|Ric|² = ric`, `|Riem|² = riem`:
`a₀ = (4π)^{-n/2} V`, `a₁ = (4π)^{-n/2} V R/6`,
`a₂ = (4π)^{-n/2} V (5R² - 2 ric + 2 riem)/360`. -/
def heatCoeffs (n : ℕ) (V R ric riem : ℝ) : ℕ → ℝ
  | 0 => (4 * π) ^ (-((n : ℝ) / 2)) * V
  | 1 => (4 * π) ^ (-((n : ℝ) / 2)) * V * R / 6
  | 2 => (4 * π) ^ (-((n : ℝ) / 2)) * V * (5 * R ^ 2 - 2 * ric + 2 * riem) / 360
  | _ => 0

/-- Only the first `m` coefficients enter `HasHeatExpansionTo n m`. -/
theorem HasHeatExpansionTo.congr_coeff {n m : ℕ} {K : ℝ → ℝ} {a b : ℕ → ℝ}
    (h : HasHeatExpansionTo n m K a) (hab : ∀ k < m, a k = b k) :
    HasHeatExpansionTo n m K b := by
  unfold HasHeatExpansionTo at *
  refine h.congr_left ?_
  intro t
  rw [Finset.sum_congr rfl (fun k hk => by rw [hab k (Finset.mem_range.1 hk)])]

/-- **`a₁` is geometric.** If the heat trace `K` has an expansion to order `≥ 2` with some
coefficients `a`, and the geometry gives `heatCoeffs`, then `a 1 = (4π)^{-n/2} V R/6`
as soon as `K` also has the expansion with `heatCoeffs` (uniqueness of coefficients). -/
theorem heatCoeffs_one_unique {n m : ℕ} (hm : 2 ≤ m) {K : ℝ → ℝ} {a : ℕ → ℝ} {V R ric riem : ℝ}
    (ha : HasHeatExpansionTo n m K a) (hg : HasHeatExpansionTo n m K (heatCoeffs n V R ric riem)) :
    a 1 = (4 * π) ^ (-((n : ℝ) / 2)) * V * R / 6 :=
  ha.coeff_unique hg 1 (by omega)

/-- **Heat trace of the unit round `S²`, geometric form.** The expansion of
`∑ (2l+1) e^{-t l(l+1)}` to order `t²` has the Seeley–DeWitt coefficients of `-Δ` with `V = 4π`,
`R = 2`, `|Ric|² = 2`, `|Riem|² = 4`; in particular `a₁ = (4π)⁻¹ · 4π · 2/6 = 1/3`. -/
theorem hasHeatExpansionTo_sphereTrace_geom :
    HasHeatExpansionTo 2 3 sphereTrace (heatCoeffs 2 (4 * π) 2 2 4) := by
  refine hasHeatExpansionTo_sphereTrace.congr_coeff ?_
  have h4 : (4 * π) ^ (-(((2 : ℕ) : ℝ) / 2)) = (4 * π)⁻¹ := by
    have : -(((2 : ℕ) : ℝ) / 2) = -1 := by norm_num
    rw [this, Real.rpow_neg_one]
  have hp : (π : ℝ) ≠ 0 := pi_ne_zero
  intro k hk
  interval_cases k
  · simp only [sphereCoeff, heatCoeffs, h4]; field_simp
  · simp only [sphereCoeff, heatCoeffs, h4]; field_simp; norm_num
  · simp only [sphereCoeff, heatCoeffs, h4]; field_simp; norm_num

/-- `heatCoeffs` for zero curvature is `a₀` only. -/
theorem heatCoeffs_flat (n : ℕ) (V : ℝ) (k : ℕ) :
    heatCoeffs n V 0 0 0 k = if k = 0 then (4 * π) ^ (-((n : ℝ) / 2)) * V else 0 := by
  rcases k with _ | _ | _ | k <;> simp [heatCoeffs]

/-- The volume term of the flat torus: `(4π)^{-n/2} (2π)ⁿ = π^{n/2}`. -/
theorem torus_a0 (n : ℕ) : (4 * π) ^ (-((n : ℝ) / 2)) * (2 * π) ^ n = π ^ ((n : ℝ) / 2) := by
  have h1 : (2 * π) ^ n = (4 * π ^ 2) ^ ((n : ℝ) / 2) := by
    have : (4 * π ^ 2 : ℝ) = (2 * π) ^ (2 : ℝ) := by
      rw [Real.rpow_two]; ring
    rw [this, ← Real.rpow_mul (by positivity)]
    rw [show (2 : ℝ) * ((n : ℝ) / 2) = (n : ℝ) by ring, Real.rpow_natCast]
  rw [h1, Real.rpow_neg (by positivity), inv_mul_eq_div,
    ← Real.div_rpow (by positivity) (by positivity)]
  congr 1
  field_simp

/-- **Heat trace of the flat torus, geometric form.** `Σ_{k∈ℤⁿ} e^{-t|k|²}` has the Seeley–DeWitt
expansion of `-Δ` with `V = (2π)ⁿ` and vanishing curvature: `a₀ = π^{n/2}`, `a₁ = 0`, all higher
coefficients `0` (the flat torus has no `t⁰` term). -/
theorem hasHeatExpansion_torusTrace_geom (n : ℕ) :
    HasHeatExpansion n (torusTrace n) (heatCoeffs n ((2 * π) ^ n) 0 0 0) := by
  have : heatCoeffs n ((2 * π) ^ n) 0 0 0 = fun k => if k = 0 then π ^ ((n : ℝ) / 2) else 0 := by
    funext k
    rw [heatCoeffs_flat, torus_a0]
  rw [this]
  exact hasHeatExpansion_torusTrace n

end Lightlike.HeatKernel
