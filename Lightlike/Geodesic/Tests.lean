import Lightlike.Geodesic.Gauss
import Lightlike.Geodesic.Convex
import Lightlike.Geodesic.GaussMaximal
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

/-- **Non-vacuity of `exists_convex_neighbourhood`, Lorentzian signature**: every point of
anti-de Sitter space with `z > 0` has a convex neighbourhood inside the unit ball about it. -/
theorem exists_convex_neighbourhood_ads {L : ℝ} (hL : L ≠ 0) {x : Fin 4 → ℝ}
    (hx : x ∈ Lightlike.adsU) :
    ∃ C : Set (Fin 4 → ℝ), IsOpen C ∧ x ∈ C ∧ C ⊆ ball x 1 ∧ C ⊆ Lightlike.adsU := by
  obtain ⟨C, h1, h2, h3, h4, -⟩ :=
    exists_convex_neighbourhood (Lightlike.isCoordMetric_ads L hL) hx one_pos
  exact ⟨C, h1, h2, h3, h4⟩

/-- **Known value for `sqDist`**: it is the square of the distance on the line. -/
theorem sqDist_fin_one (x q : Fin 1 → ℝ) : sqDist x q = (q 0 - x 0) ^ 2 := by
  simp [sqDist]

/-- **Non-vacuity of `exists_expMap_along_gauss`**: through every point of the domain of a
coordinate metric there is a geodesic that satisfies its hypotheses (defined on an open set
containing `[0, 1]`, with values in `U` on `[0, 1]`). -/
theorem exists_geodesic_on_unit_interval {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {U : Set (Fin n → ℝ)} (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) :
    ∃ γ w : ℝ → Fin n → ℝ, Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 ∧
      IsGeodesicOn g γ w (Ioo (-1) 2) ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U := by
  obtain ⟨ρ, φ, h⟩ := exists_isNormalChart hg hx
  obtain ⟨γ, w, -, -, -, hgeo, hφ⟩ := h.geodesic 0 (mem_ball_self h.pos)
  refine ⟨γ, w, fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩, hgeo, fun t ht => ?_⟩
  rw [hφ t ⟨by linarith [ht.1], ht.2⟩, smul_zero, h.map_zero]
  exact hx

end Lightlike.Geodesic.Tests
