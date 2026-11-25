import Mathlib

/-!
# The Γ Γ form of the Einstein–Hilbert density at a point (jets)

Row G3-255 (milestone PG6 uses the graviton vertices read off from the expansion of the Einstein–Hilbert action
around flat space; see Donoghue 1994, source key `donoghue-1994`, and Bjerrum-Bohr–Donoghue–Holstein 2003,
source key `bjerrum-bohr-donoghue-holstein-2003`).

This file fixes the objects at the level of jets at one point. A *jet* is a pair `(g, dg)`: a symmetric matrix
`g i j` (the metric at the point) and an array `dg k i j = ∂_k g_ij`. The Γ Γ Lagrangian (Landau–Lifshitz form of the
Einstein–Hilbert density, which differs from `√|g| R` by a total derivative; that bridge is *not* proved here)
is, with `Γ_{ρμν} = ½ (∂_μ g_ρν + ∂_ν g_ρμ - ∂_ρ g_μν)`,

`L(g, dg) = √|det g| · g^{μν} (Γ^α_{μβ} Γ^β_{να} - Γ^α_{μν} Γ^β_{αβ})`.

## Main definitions

* `gammaLow dg ρ μ ν`: the Christoffel symbol of the first kind of the array `dg`.
* `gammaGamma g gi dg`: the Γ Γ Lagrangian for the metric `g` with inverse `gi` and derivative array `dg`.

## Conventions

Indices are `Fin n`, lower indices for `g` and `dg`, upper for `gi`. The inverse is passed as a separate matrix
(with the hypothesis `g * gi = 1` where needed), so that no `Matrix.inv` rewriting is required.

## Limits

Jets at a point only: no fields, no integration, no manifold.
-/

open Finset

namespace Lightlike.GR.EinsteinHilbertExpansion

variable {n : ℕ}

/-- The Christoffel symbol of the first kind `Γ_{ρμν} = ½ (∂_μ g_ρν + ∂_ν g_ρμ - ∂_ρ g_μν)` of the
array `dg k i j = ∂_k g_ij`. -/
noncomputable def gammaLow (dg : Fin n → Fin n → Fin n → ℝ) (ρ μ ν : Fin n) : ℝ :=
  (dg μ ρ ν + dg ν ρ μ - dg ρ μ ν) / 2

/-- The Γ Γ Lagrangian `√|det g| g^{μν} (Γ^α_{μβ} Γ^β_{να} - Γ^α_{μν} Γ^β_{αβ})` of the jet `(g, dg)`,
with `gi` the inverse of `g`, written with all indices of `Γ` lowered by `gi`. -/
noncomputable def gammaGamma (g gi : Matrix (Fin n) (Fin n) ℝ) (dg : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  Real.sqrt |g.det| *
    ∑ μ, ∑ ν, ∑ α, ∑ ρ, ∑ β, ∑ σ, gi μ ν * gi α ρ * gi β σ *
      (gammaLow dg ρ μ β * gammaLow dg σ ν α - gammaLow dg ρ μ ν * gammaLow dg σ α β)

/-- The Lagrangian is homogeneous of degree two in the derivative array. -/
theorem gammaGamma_smul (g gi : Matrix (Fin n) (Fin n) ℝ) (dg : Fin n → Fin n → Fin n → ℝ) (c : ℝ) :
    gammaGamma g gi (fun k i j => c * dg k i j) = c ^ 2 * gammaGamma g gi dg := by
  unfold gammaGamma gammaLow
  rw [mul_left_comm]
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  refine Finset.sum_congr rfl fun ν _ => ?_
  refine Finset.sum_congr rfl fun α _ => ?_
  refine Finset.sum_congr rfl fun ρ _ => ?_
  refine Finset.sum_congr rfl fun β _ => ?_
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

end Lightlike.GR.EinsteinHilbertExpansion

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_255.gammaGamma := _root_.Lightlike.GR.EinsteinHilbertExpansion.gammaGamma
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_255.gammaGamma_smul := _root_.Lightlike.GR.EinsteinHilbertExpansion.gammaGamma_smul
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_255.gammaLow := _root_.Lightlike.GR.EinsteinHilbertExpansion.gammaLow
