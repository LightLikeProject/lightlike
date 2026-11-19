import Lightlike.Geodesic.ExpDiffeo
import Lightlike.GR.AdSPoincare

/-!
# Checks for the exponential map

The hypotheses of `Lightlike.Geodesic.exists_expMap_diffeo` are met by a Lorentzian metric:
anti-de Sitter space in the Poincaré patch, at any point with `z > 0`. So the statement is not
restricted to positive definite metrics.
-/

open Set Metric
open scoped ContDiff

noncomputable section

namespace Lightlike.Geodesic.Tests

/-- **Non-vacuity of `exists_expMap_diffeo`, Lorentzian signature**: the exponential map of
anti-de Sitter space (Poincaré patch, radius `L ≠ 0`) is a diffeomorphism near `0` at every point
with `z > 0`. -/
theorem exists_expMap_diffeo_ads {L : ℝ} (hL : L ≠ 0) {x : Fin 4 → ℝ} (hx : x ∈ Lightlike.adsU) :
    ∃ (ρ : ℝ) (φ : OpenPartialHomeomorph (Fin 4 → ℝ) (Fin 4 → ℝ)), 0 < ρ ∧
      φ.source = ball 0 ρ ∧ φ 0 = x ∧ ContDiffOn ℝ ∞ φ φ.source ∧
      ContDiffOn ℝ ∞ φ.symm φ.target ∧
      HasFDerivAt φ (ContinuousLinearMap.id ℝ (Fin 4 → ℝ)) 0 ∧
      ∀ v ∈ ball (0 : Fin 4 → ℝ) ρ, ∃ γ w : ℝ → Fin 4 → ℝ, γ 0 = x ∧ w 0 = v ∧ γ 1 = φ v ∧
        IsGeodesicOn (Lightlike.adsMetric L) γ w (Ioo (-1) 2) :=
  exists_expMap_diffeo (Lightlike.isCoordMetric_ads L hL) hx

end Lightlike.Geodesic.Tests
