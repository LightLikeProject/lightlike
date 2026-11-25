import Lightlike.Spacetime.ScalarEnergyConditions.KleinGordonNEC

/-!
# Null focusing for the Klein–Gordon field (G1-010, generalisation)

Under `G = κ T` with `T` the Klein–Gordon stress-energy, the Ricci tensor on a null vector `k` is
`Ric(k, k) = κ (dφ k)²` (the trace term and the potential drop out, since `g(k, k) = 0`). This is the geometric form of
the null energy condition for the field (`nullECField_iff_ricci`, Curiel, arXiv 1405.0403v1, p. 6, as in
`EnergyConditionsField.lean`) with the value computed, and it is the hypothesis of the Raychaudhuri focusing argument.

* `scalarField_ricciAt_null`: `Ric(k, k) = κ (dφ k)²` for null `k`.
* `scalarField_ricciAt_null_nonneg`: hence `Ric(k, k) ≥ 0` for `κ ≥ 0`.
* `scalarField_ricciAt_null_eq_zero_iff`: equality case, for `κ > 0`, `Ric(k, k) = 0` iff `dφ k = 0`.

**Limits.** Pointwise statements, Lorentzian 4-manifold, cosmological constant `0` (one absorbs `Λ` by
`einsteinEq_iff_absorb`, which changes the potential only by a constant, so does not affect null vectors).
-/

open Manifold
open scoped ContDiff

noncomputable section
namespace Lightlike

section Geometric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E]
  {g : LorentzianMetric 𝓘(ℝ, E) M 4} {cov : Connection 𝓘(ℝ, E) M} {κ : ℝ}

/-- **Ricci tensor of an Einstein–Klein–Gordon solution on null vectors**: `Ric(k, k) = κ (dφ k)²`. -/
theorem scalarField_ricciAt_null (φ : M → ℝ) (Vpot : ℝ → ℝ)
    (h : g.toNondegMetric.EinsteinEq cov 0 κ (fun x v w => g.scalarField φ Vpot x v w)) (x : M)
    {k : TangentSpace 𝓘(ℝ, E) x} (hk : g.g x k k = 0) :
    cov.ricciAt x k k = κ * (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ x k) ^ 2 := by
  rw [LorentzianMetric.ricciAt_of_einsteinEq h x, hk, mul_zero, add_zero]
  congr 1
  exact scalarT_null (g.g x) (g.lorentzian x) _ _ hk

/-- **Null focusing hypothesis**: for `κ ≥ 0`, `Ric(k, k) ≥ 0` on null `k`. -/
theorem scalarField_ricciAt_null_nonneg (φ : M → ℝ) (Vpot : ℝ → ℝ) (hκ : 0 ≤ κ)
    (h : g.toNondegMetric.EinsteinEq cov 0 κ (fun x v w => g.scalarField φ Vpot x v w)) (x : M)
    {k : TangentSpace 𝓘(ℝ, E) x} (hk : g.g x k k = 0) : 0 ≤ cov.ricciAt x k k := by
  rw [scalarField_ricciAt_null φ Vpot h x hk]; positivity

/-- Equality case: for `κ > 0` and null `k`, `Ric(k, k) = 0` iff `dφ k = 0`. -/
theorem scalarField_ricciAt_null_eq_zero_iff (φ : M → ℝ) (Vpot : ℝ → ℝ) (hκ : 0 < κ)
    (h : g.toNondegMetric.EinsteinEq cov 0 κ (fun x v w => g.scalarField φ Vpot x v w)) (x : M)
    {k : TangentSpace 𝓘(ℝ, E) x} (hk : g.g x k k = 0) :
    cov.ricciAt x k k = 0 ↔ (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ x k) = 0 := by
  rw [scalarField_ricciAt_null φ Vpot h x hk]
  constructor
  · intro h0
    exact pow_eq_zero_iff (two_ne_zero) |>.1 ((mul_eq_zero.1 h0).resolve_left hκ.ne')
  · intro h0; rw [h0]; simp

end Geometric

end Lightlike
