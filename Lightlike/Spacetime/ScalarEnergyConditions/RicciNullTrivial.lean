import Lightlike.Spacetime.ScalarEnergyConditions.KleinGordonRicci
import Lightlike.Spacetime.ScalarEnergyConditions.NullCovector

/-!
# Null-trivial Ricci tensor of an Einstein–Klein–Gordon solution (G1-010)

For `G = κ T` with `κ > 0` and `T` the Klein–Gordon stress-energy, `Ric(k, k) = κ (dφ k)²` on null `k`
(`scalarField_ricciAt_null`). Hence `Ric(k, k) = 0` for all null `k` at a point `x` exactly when `dφ = 0` at `x`.

* `scalarField_ricciAt_null_trivial_iff`: pointwise equivalence, `(∀ null k, Ric(k, k) = 0) ↔ mfderiv φ x = 0`.
* `scalarField_ricci_null_trivial_iff_mfderiv`: global form, over all points.

**Limits.** Lorentzian 4-manifold, `Λ = 0`, `κ > 0`; the sources are those of `KleinGordonRicci.lean`.
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

/-- **Null-trivial Ricci tensor at a point**: for `κ > 0`, `Ric(k, k) = 0` for every `g`-null `k` iff `dφ = 0` at `x`. -/
theorem scalarField_ricciAt_null_trivial_iff (φ : M → ℝ) (Vpot : ℝ → ℝ) (hκ : 0 < κ)
    (h : g.toNondegMetric.EinsteinEq cov 0 κ (fun x v w => g.scalarField φ Vpot x v w)) (x : M) :
    (∀ k : TangentSpace 𝓘(ℝ, E) x, g.g x k k = 0 → cov.ricciAt x k k = 0) ↔
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ x = 0 := by
  have key : (∀ k : TangentSpace 𝓘(ℝ, E) x, g.g x k k = 0 → cov.ricciAt x k k = 0) ↔
      (∀ k : TangentSpace 𝓘(ℝ, E) x, g.g x k k = 0 →
        (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ x k) = 0) :=
    forall_congr' fun k => imp_congr_right fun hk =>
      scalarField_ricciAt_null_eq_zero_iff φ Vpot hκ h x hk
  rw [key]
  exact covector_null_eq_zero_iff (n := 2) (g.lorentzian x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ x)

/-- Global form: `Ric` vanishes on all null vectors at every point iff `φ` has zero derivative everywhere. -/
theorem scalarField_ricci_null_trivial_iff_mfderiv (φ : M → ℝ) (Vpot : ℝ → ℝ) (hκ : 0 < κ)
    (h : g.toNondegMetric.EinsteinEq cov 0 κ (fun x v w => g.scalarField φ Vpot x v w)) :
    (∀ (x : M) (k : TangentSpace 𝓘(ℝ, E) x), g.g x k k = 0 → cov.ricciAt x k k = 0) ↔
      ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ x = 0 :=
  forall_congr' fun x => scalarField_ricciAt_null_trivial_iff φ Vpot hκ h x

end Geometric

end Lightlike
