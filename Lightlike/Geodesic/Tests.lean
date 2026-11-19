import Lightlike.Geodesic.Gauss
import Lightlike.GR.AdSPoincare

/-!
# Checks for the exponential map

The hypotheses of `Lightlike.Geodesic.exists_expMap_diffeo` are met by a Lorentzian metric:
anti-de Sitter space in the Poincaré patch, at any point with `z > 0`. So the statement is not
restricted to positive definite metrics. The same holds for the Gauss lemma
(`exists_normal_chart_gauss_ads`), and the pairing reduces to the dot product for the identity
matrix (`pairing_one`).
-/

open Set Metric Matrix
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
      HasFDerivAt φ (ContinuousLinearMap.id ℝ (Fin 4 → ℝ)) 0 ∧ φ.target ⊆ Lightlike.adsU ∧
      ∀ v ∈ ball (0 : Fin 4 → ℝ) ρ, ∃ γ w : ℝ → Fin 4 → ℝ, γ 0 = x ∧ w 0 = v ∧ γ 1 = φ v ∧
        IsGeodesicOn (Lightlike.adsMetric L) γ w (Ioo (-1) 2) ∧
        ∀ t ∈ Icc (-1 : ℝ) 1, γ t = φ (t • v) :=
  exists_expMap_diffeo (Lightlike.isCoordMetric_ads L hL) hx

/-- **Non-vacuity of the Gauss lemma, Lorentzian signature**: anti-de Sitter space has a normal
chart at every point with `z > 0`, and its exponential map is a radial isometry. -/
theorem exists_normal_chart_gauss_ads {L : ℝ} (hL : L ≠ 0) {x : Fin 4 → ℝ}
    (hx : x ∈ Lightlike.adsU) :
    ∃ (ρ : ℝ) (φ : OpenPartialHomeomorph (Fin 4 → ℝ) (Fin 4 → ℝ)),
      IsNormalChart (Lightlike.adsMetric L) Lightlike.adsU x ρ φ ∧
      ∀ v ∈ ball (0 : Fin 4 → ℝ) ρ, ∀ w : Fin 4 → ℝ,
        pairing (Lightlike.adsMetric L) (φ v) (fderiv ℝ φ v v) (fderiv ℝ φ v w) =
          pairing (Lightlike.adsMetric L) x v w :=
  exists_normal_chart_gauss (Lightlike.isCoordMetric_ads L hL) hx

/-- **Known value for the pairing**: for the identity matrix it is the dot product. -/
theorem pairing_one {n : ℕ} (y a b : Fin n → ℝ) :
    pairing (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) y a b = a ⬝ᵥ b := by
  rw [pairing_eq_dotProduct, Matrix.one_mulVec]

end Lightlike.Geodesic.Tests
