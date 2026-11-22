import Lightlike.Upstream.GeodesicExpansion.Regge
import Mathlib

/-!
# Regge edge lengths (not squared) of a small coordinate simplex (Tier 2)

* `IsRiemMetric.normSq_lower`: uniform local positive-definiteness `λ ‖w‖² ≤ g_x(w, w)` on a compact.
* `IsRiemMetric.chartDist_sq_simplex_edge'`: the squared edge error carries the factor `‖v - u‖²`.
* `IsRiemMetric.chartDist_simplex_edge`: `|d(x + h u, x + h v) - h √(g_x(v - u, v - u))| ≤ C h² ‖v - u‖`.
-/

open Matrix Set Filter Topology Metric

noncomputable section

namespace Lightlike.Upstream.GeodesicExpansion

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
  {U : TopologicalSpace.Opens (Fin n → ℝ)}

/-- **Uniform quadratic lower bound for the metric on a compact.** For a compact `K ⊆ U` there are
`λ > 0` and `r > 0` with `λ ‖w‖² ≤ g_x(w, w)` for `x ∈ K` and `‖w‖ ≤ r`. -/
theorem IsRiemMetric.normSq_lower (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ l r : ℝ, 0 < l ∧ 0 < r ∧ ∀ x ∈ K, ∀ w : Fin n → ℝ, ‖w‖ ≤ r →
      l * ‖w‖ ^ 2 ≤ w ⬝ᵥ (g x *ᵥ w) := by
  obtain ⟨c, C, r₂, hc, hr₂, h₂⟩ := hg.chartDist_sq_two_sided hK hKU
  obtain ⟨C₁, r₁, hr₁, h₁⟩ := hg.chartDist_sq_third hK hKU
  have hC : 0 < |C₁| + 1 := by positivity
  refine ⟨c / 2, min (min r₁ r₂) (c / (2 * (|C₁| + 1))), half_pos hc,
    lt_min (lt_min hr₁ hr₂) (by positivity), fun x hx w hw => ?_⟩
  have hw₁ : ‖w‖ ≤ r₁ := (hw.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hw₂ : ‖w‖ ≤ r₂ := (hw.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hw₃ : ‖w‖ ≤ c / (2 * (|C₁| + 1)) := hw.trans (min_le_right _ _)
  have hn := norm_nonneg w
  have e1 := (abs_le.mp (h₁ x hx w hw₁)).2
  have e2 := (h₂ x hx w hw₂).1
  have e3 : |C₁| * ‖w‖ ≤ c / 2 := by
    have : |C₁| * ‖w‖ ≤ (|C₁| + 1) * (c / (2 * (|C₁| + 1))) :=
      mul_le_mul (by linarith) hw₃ hn hC.le
    refine this.trans_eq ?_
    field_simp
  have e4 : C₁ * ‖w‖ ^ 3 ≤ c / 2 * ‖w‖ ^ 2 := by
    calc C₁ * ‖w‖ ^ 3 ≤ |C₁| * ‖w‖ ^ 3 :=
          mul_le_mul_of_nonneg_right (le_abs_self C₁) (by positivity)
      _ = (|C₁| * ‖w‖) * ‖w‖ ^ 2 := by ring
      _ ≤ c / 2 * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right e3 (sq_nonneg _)
  linarith

/-- **Edge lengths of a small coordinate simplex, squared, with relative error.** For a compact
`K ⊆ U` and `R ≥ 0` there are `C` and `h₀ > 0` such that for `x ∈ K`, `0 < h ≤ h₀`, `‖u‖, ‖v‖ ≤ R`:
`|d(x + h u, x + h v)² - h² g_x(v - u, v - u)| ≤ C h³ ‖v - u‖²`. -/
theorem IsRiemMetric.chartDist_sq_simplex_edge' (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ x ∈ K, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ u v : Fin n → ℝ,
      ‖u‖ ≤ R → ‖v‖ ≤ R →
      |chartDist g U (x + h • u) (x + h • v) ^ 2 - h ^ 2 * ((v - u) ⬝ᵥ (g x *ᵥ (v - u)))| ≤
        C * h ^ 3 * ‖v - u‖ ^ 2 := by
  obtain ⟨C, r, ε, hr, hε, hE⟩ := hg.chartDist_sq_edge hK hKU
  have hR1 : 0 < R + 1 := by linarith
  refine ⟨|C| * (3 * R), min ε r / (2 * (R + 1)), by positivity,
    fun x hx h hh hh0 u v hu hv => ?_⟩
  have hmin : h * (2 * (R + 1)) ≤ min ε r := by
    rwa [le_div_iff₀ (by positivity)] at hh0
  have hεm : min ε r ≤ ε := min_le_left _ _
  have hrm : min ε r ≤ r := min_le_right _ _
  have hau : ‖x + h • u - x‖ = h * ‖u‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hh.le]
  have hba : (x + h • v) - (x + h • u) = h • (v - u) := by
    rw [add_sub_add_left_eq_sub, smul_sub]
  have hvu : ‖v - u‖ ≤ 2 * R := by
    calc ‖v - u‖ ≤ ‖v‖ + ‖u‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have hbn : ‖(x + h • v) - (x + h • u)‖ = h * ‖v - u‖ := by
    rw [hba, norm_smul, Real.norm_of_nonneg hh.le]
  have hu' : h * ‖u‖ ≤ h * R := mul_le_mul_of_nonneg_left hu hh.le
  have hvu' : h * ‖v - u‖ ≤ h * (2 * R) := mul_le_mul_of_nonneg_left hvu hh.le
  have h1 : ‖x + h • u - x‖ ≤ ε := by
    rw [hau]; nlinarith
  have h2 : ‖(x + h • v) - (x + h • u)‖ ≤ r := by
    rw [hbn]; nlinarith
  have e := hE x hx (x + h • u) (x + h • v) h1 h2
  rw [hbn, hau, hba] at e
  have hq : (h • (v - u)) ⬝ᵥ (g x *ᵥ (h • (v - u))) = h ^ 2 * ((v - u) ⬝ᵥ (g x *ᵥ (v - u))) := by
    rw [mulVec_smul, dotProduct_smul, smul_dotProduct]; simp only [smul_eq_mul]; ring
  rw [hq] at e
  refine e.trans ?_
  have hn : 0 ≤ ‖v - u‖ := norm_nonneg _
  have hnu : 0 ≤ ‖u‖ := norm_nonneg _
  have hsum : (h * ‖v - u‖) ^ 3 + h * ‖u‖ * (h * ‖v - u‖) ^ 2 ≤ (3 * R) * h ^ 3 * ‖v - u‖ ^ 2 := by
    have a1 : ‖v - u‖ ≤ 2 * R := hvu
    have a2 : ‖v - u‖ + ‖u‖ ≤ 3 * R := by linarith
    have a3 : 0 ≤ h ^ 3 * ‖v - u‖ ^ 2 := by positivity
    calc (h * ‖v - u‖) ^ 3 + h * ‖u‖ * (h * ‖v - u‖) ^ 2
        = (‖v - u‖ + ‖u‖) * (h ^ 3 * ‖v - u‖ ^ 2) := by ring
      _ ≤ (3 * R) * (h ^ 3 * ‖v - u‖ ^ 2) := mul_le_mul_of_nonneg_right a2 a3
      _ = _ := by ring
  calc C * ((h * ‖v - u‖) ^ 3 + h * ‖u‖ * (h * ‖v - u‖) ^ 2)
      ≤ |C| * ((h * ‖v - u‖) ^ 3 + h * ‖u‖ * (h * ‖v - u‖) ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * ((3 * R) * h ^ 3 * ‖v - u‖ ^ 2) := mul_le_mul_of_nonneg_left hsum (abs_nonneg C)
    _ = |C| * (3 * R) * h ^ 3 * ‖v - u‖ ^ 2 := by ring

end Lightlike.Upstream.GeodesicExpansion
