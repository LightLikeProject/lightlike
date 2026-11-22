import Lightlike.Upstream.GeodesicExpansion.Final
import Mathlib

/-!
# Consequences of the fifth-order expansion of the squared Riemannian distance

Lower-order and comparison forms of `IsRiemMetric.riemannianEDist_sq_expansion`, uniform for the
base point in a compact `K ⊆ U`:

* `IsRiemMetric.chartDist_sq_third`, `IsRiemMetric.riemannianEDist_sq_third`:
  `d(x, x + w)² = g_x(w, w) + O(‖w‖³)`.
* `IsRiemMetric.chartDist_sq_two_sided`, `IsRiemMetric.riemannianEDist_sq_two_sided`:
  `c ‖w‖² ≤ d(x, x + w)² ≤ C ‖w‖²`.
-/

open Matrix Set Filter Topology Metric MeasureTheory Manifold Bundle
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Upstream.GeodesicExpansion

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
  {U : TopologicalSpace.Opens (Fin n → ℝ)}

/-- **Third-order expansion of the squared distance (chart form).** For a compact `K ⊆ U` there
are `C` and `r > 0` with `|d(x, x + w)² - g_x(w, w)| ≤ C ‖w‖³` for `x ∈ K`, `‖w‖ ≤ r`. -/
theorem IsRiemMetric.chartDist_sq_third (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C r : ℝ, 0 < r ∧ ∀ x ∈ K, ∀ w : Fin n → ℝ, ‖w‖ ≤ r →
      |chartDist g U x (x + w) ^ 2 - w ⬝ᵥ (g x *ᵥ w)| ≤ C * ‖w‖ ^ 3 := by
  obtain ⟨B, δ, l, hJ⟩ := hg.exists_localJet hK hKU
  obtain ⟨C, r, hr, h⟩ := hg.dist_sq_expansion hK hKU
  refine ⟨|C| + B ^ 3, min r 1, lt_min hr one_pos, fun x hx w hw => ?_⟩
  have hw1 : ‖w‖ ≤ 1 := hw.trans (min_le_right _ _)
  have hwr : ‖w‖ ≤ r := hw.trans (min_le_left _ _)
  have h1 := h x hx w hwr
  have h2 := (hJ x hx).abs_distJet_sub_le hw1
  have h3 : ‖w‖ ^ 5 ≤ ‖w‖ ^ 3 := pow_le_pow_of_le_one (norm_nonneg _) hw1 (by norm_num)
  have h4 : C * ‖w‖ ^ 5 ≤ |C| * ‖w‖ ^ 3 :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h3 (abs_nonneg C))
  calc |chartDist g U x (x + w) ^ 2 - w ⬝ᵥ (g x *ᵥ w)|
      = |(chartDist g U x (x + w) ^ 2 - distJet g x w) + (distJet g x w - w ⬝ᵥ (g x *ᵥ w))| := by
        ring_nf
    _ ≤ |chartDist g U x (x + w) ^ 2 - distJet g x w| + |distJet g x w - w ⬝ᵥ (g x *ᵥ w)| :=
        abs_add_le _ _
    _ ≤ C * ‖w‖ ^ 5 + B ^ 3 * ‖w‖ ^ 3 := add_le_add h1 h2
    _ ≤ (|C| + B ^ 3) * ‖w‖ ^ 3 := by nlinarith

/-- **Third-order expansion of the squared Riemannian distance (Mathlib form).** With the
Riemannian bundle structure of `IsRiemMetric.riemannianBundle`, for `x ∈ K`, `y ∈ U` with
`‖y - x‖ ≤ r`: `|d(x, y)² - g_x(y - x, y - x)| ≤ C ‖y - x‖³`. -/
theorem IsRiemMetric.riemannianEDist_sq_third (hg : IsRiemMetric g U)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    letI := hg.riemannianBundle
    ∃ C r : ℝ, 0 < r ∧ ∀ x y : U, (x : Fin n → ℝ) ∈ K → ‖(y : Fin n → ℝ) - x‖ ≤ r →
      |(riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y).toReal ^ 2 -
          ((y : Fin n → ℝ) - (x : Fin n → ℝ)) ⬝ᵥ
            (g (x : Fin n → ℝ) *ᵥ ((y : Fin n → ℝ) - (x : Fin n → ℝ)))| ≤
        C * ‖(y : Fin n → ℝ) - x‖ ^ 3 := by
  let := hg.riemannianBundle
  obtain ⟨C, r, hr, h⟩ := hg.chartDist_sq_third hK hKU
  refine ⟨C, r, hr, fun x y hx hxy => ?_⟩
  rw [← hg.chartDist_eq_toReal_riemannianEDist x y]
  have := h x hx ((y : Fin n → ℝ) - x) hxy
  rwa [add_sub_cancel] at this

/-- **Two-sided comparison of the distance with the Euclidean one (chart form).** For a compact
`K ⊆ U` there are `0 < c`, `C`, `r > 0` with
`c ‖w‖² ≤ d(x, x + w)² ≤ C ‖w‖²` for `x ∈ K`, `‖w‖ ≤ r`. -/
theorem IsRiemMetric.chartDist_sq_two_sided (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < r ∧ ∀ x ∈ K, ∀ w : Fin n → ℝ, ‖w‖ ≤ r →
      c * ‖w‖ ^ 2 ≤ chartDist g U x (x + w) ^ 2 ∧ chartDist g U x (x + w) ^ 2 ≤ C * ‖w‖ ^ 2 := by
  obtain ⟨B, δ, l, hJ⟩ := hg.exists_localJet hK hKU
  obtain ⟨C, r, hr, h⟩ := hg.dist_sq_expansion hK hKU
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨1, 1, 1, one_pos, one_pos, fun x hx => absurd hx (Set.notMem_empty x)⟩
  have h₀ := hJ x₀ hx₀
  have hB1 := h₀.one_le
  have hB : 0 < B := by linarith
  have hl := h₀.l_pos
  have hC : 0 < |C| + 1 := by positivity
  have hB3 : 0 < B ^ 3 := by positivity
  refine ⟨l / 4, 2 * B ^ 3 + |C|, min (min r 1) (min (l / (2 * B ^ 3)) (l / (4 * (|C| + 1)))),
    by positivity, lt_min (lt_min hr one_pos) (lt_min (by positivity) (by positivity)),
    fun x hx w hw => ?_⟩
  have hw1 : ‖w‖ ≤ 1 := (hw.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hwr : ‖w‖ ≤ r := (hw.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hwl : ‖w‖ ≤ l / (2 * B ^ 3) := (hw.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hwC : ‖w‖ ≤ l / (4 * (|C| + 1)) := (hw.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hJx := hJ x hx
  have h1 := abs_le.mp (h x hx w hwr)
  have hn := norm_nonneg w
  have h3 : ‖w‖ ^ 5 ≤ ‖w‖ * ‖w‖ ^ 2 := by
    have : ‖w‖ ^ 3 ≤ ‖w‖ := by
      calc ‖w‖ ^ 3 = ‖w‖ * ‖w‖ ^ 2 := by ring
        _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hn hw1) hn
        _ = ‖w‖ := mul_one _
    calc ‖w‖ ^ 5 = ‖w‖ ^ 3 * ‖w‖ ^ 2 := by ring
      _ ≤ ‖w‖ * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hCw : |C| * ‖w‖ ≤ l / 4 := by
    have : |C| * ‖w‖ ≤ (|C| + 1) * (l / (4 * (|C| + 1))) :=
      mul_le_mul (by linarith) hwC hn hC.le
    refine this.trans_eq ?_
    field_simp
  have hC5 : |C * ‖w‖ ^ 5| ≤ l / 4 * ‖w‖ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w‖ ^ 5)]
    calc |C| * ‖w‖ ^ 5 ≤ |C| * (‖w‖ * ‖w‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg C)
      _ = (|C| * ‖w‖) * ‖w‖ ^ 2 := by ring
      _ ≤ l / 4 * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right hCw (sq_nonneg _)
  have hBw : B ^ 3 * ‖w‖ ≤ l / 2 := by
    have := mul_le_mul_of_nonneg_left hwl hB3.le
    refine this.trans_eq ?_
    field_simp
  have hlow := hJx.distJet_ge_half hw1 hBw
  have hup := hJx.distJet_le hw1
  have hC5' := abs_le.mp hC5
  have h5 : ‖w‖ ^ 5 ≤ ‖w‖ ^ 2 := pow_le_pow_of_le_one hn hw1 (by norm_num)
  have h6 : C * ‖w‖ ^ 5 ≤ |C| * ‖w‖ ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h5 (abs_nonneg C))
  constructor
  · linarith [h1.1, h1.2, hC5'.1, hC5'.2]
  · linarith [h1.1, h1.2, hup]

/-- **Two-sided comparison of the squared Riemannian distance with the Euclidean one (Mathlib
form).** For `x ∈ K`, `y ∈ U` with `‖y - x‖ ≤ r`:
`c ‖y - x‖² ≤ d(x, y)² ≤ C ‖y - x‖²`. -/
theorem IsRiemMetric.riemannianEDist_sq_two_sided (hg : IsRiemMetric g U)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    letI := hg.riemannianBundle
    ∃ c C r : ℝ, 0 < c ∧ 0 < r ∧ ∀ x y : U, (x : Fin n → ℝ) ∈ K →
      ‖(y : Fin n → ℝ) - x‖ ≤ r →
      c * ‖(y : Fin n → ℝ) - x‖ ^ 2 ≤ (riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y).toReal ^ 2 ∧
        (riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y).toReal ^ 2 ≤ C * ‖(y : Fin n → ℝ) - x‖ ^ 2 := by
  let := hg.riemannianBundle
  obtain ⟨c, C, r, hc, hr, h⟩ := hg.chartDist_sq_two_sided hK hKU
  refine ⟨c, C, r, hc, hr, fun x y hx hxy => ?_⟩
  rw [← hg.chartDist_eq_toReal_riemannianEDist x y]
  have := h x hx ((y : Fin n → ℝ) - x) hxy
  rwa [add_sub_cancel] at this

end Lightlike.Upstream.GeodesicExpansion
