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

/-- **Regge edge lengths of a small coordinate simplex.** For a compact `K ⊆ U` and `R ≥ 0` there
are `C` and `h₀ > 0` such that for `x ∈ K`, `0 < h ≤ h₀`, `‖u‖, ‖v‖ ≤ R`:
`|d(x + h u, x + h v) - h √(g_x(v - u, v - u))| ≤ C h² ‖v - u‖`. -/
theorem IsRiemMetric.chartDist_simplex_edge (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ x ∈ K, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ u v : Fin n → ℝ,
      ‖u‖ ≤ R → ‖v‖ ≤ R →
      |chartDist g U (x + h • u) (x + h • v) -
          h * Real.sqrt ((v - u) ⬝ᵥ (g x *ᵥ (v - u)))| ≤ C * h ^ 2 * ‖v - u‖ := by
  obtain ⟨C', h₁, hh₁, hE⟩ := hg.chartDist_sq_simplex_edge' hK hKU hR
  obtain ⟨l, r, hl, hr, hL⟩ := hg.normSq_lower hK hKU
  have hs : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have hR1 : 0 < 2 * R + 1 := by linarith
  refine ⟨C' / Real.sqrt l, min h₁ (r / (2 * R + 1)), lt_min hh₁ (by positivity),
    fun x hx h hh hh0 u v hu hv => ?_⟩
  have hhr : h * (2 * R + 1) ≤ r := by
    have := hh0.trans (min_le_right _ _)
    rwa [le_div_iff₀ hR1] at this
  have hh1 : h ≤ h₁ := hh0.trans (min_le_left _ _)
  have hvu : ‖v - u‖ ≤ 2 * R := by
    calc ‖v - u‖ ≤ ‖v‖ + ‖u‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have hn := norm_nonneg (v - u)
  have hhn : ‖h • (v - u)‖ = h * ‖v - u‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh.le]
  have hhnr : ‖h • (v - u)‖ ≤ r := by
    rw [hhn]; nlinarith
  have hlow := hL x hx (h • (v - u)) hhnr
  have hq : (h • (v - u)) ⬝ᵥ (g x *ᵥ (h • (v - u))) =
      h ^ 2 * ((v - u) ⬝ᵥ (g x *ᵥ (v - u))) := by
    rw [mulVec_smul, dotProduct_smul, smul_dotProduct]; simp only [smul_eq_mul]; ring
  rw [hq, hhn] at hlow
  have hE' := hE x hx h hh hh1 u v hu hv
  have hq0 : 0 ≤ (v - u) ⬝ᵥ (g x *ᵥ (v - u)) := hg.normSq_nonneg (hKU hx) _
  have hd := chartDist_nonneg (g := g) (U := U) (x := x + h • u) (y := x + h • v)
  set d := chartDist g U (x + h • u) (x + h • v) with hddef
  set q := (v - u) ⬝ᵥ (g x *ᵥ (v - u)) with hqdef
  have hsq0 := Real.sqrt_nonneg q
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0
  rcases hn.eq_or_lt with h0 | hpos
  · have hw0 : ‖v - u‖ = 0 := h0.symm
    have hvu0 : v - u = 0 := norm_eq_zero.mp hw0
    have hq00 : q = 0 := by simp [hqdef, hvu0]
    have hd2 : d ^ 2 ≤ 0 := by
      have := (abs_le.mp hE').2
      rw [hw0, hq00] at this
      nlinarith
    have hd0 : d = 0 := by nlinarith
    simp [hd0, hq00, hw0]
  · set s := h * Real.sqrt q with hsdef
    have hs0 : 0 ≤ s := by positivity
    have hss : s ^ 2 = h ^ 2 * q := by rw [hsdef, mul_pow, hsq]
    have hsl : Real.sqrt l * (h * ‖v - u‖) ≤ s := by
      have : (Real.sqrt l * (h * ‖v - u‖)) ^ 2 ≤ s ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hl.le, hss]; linarith
      exact (abs_le_of_sq_le_sq' this hs0).2
    have hprod : |d - s| * (d + s) = |d ^ 2 - h ^ 2 * q| := by
      rw [← abs_of_nonneg (by positivity : 0 ≤ d + s), ← abs_mul]
      congr 1
      nlinarith
    have hkey : |d - s| * (Real.sqrt l * (h * ‖v - u‖)) ≤ C' * h ^ 3 * ‖v - u‖ ^ 2 := by
      calc |d - s| * (Real.sqrt l * (h * ‖v - u‖)) ≤ |d - s| * (d + s) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
        _ = |d ^ 2 - h ^ 2 * q| := hprod
        _ ≤ _ := hE'
    have hhn0 : 0 < h * ‖v - u‖ := mul_pos hh hpos
    have h3 : |d - s| * Real.sqrt l ≤ C' * h ^ 2 * ‖v - u‖ := by
      refine le_of_mul_le_mul_right ?_ hhn0
      nlinarith [hkey]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hs]
    linarith [h3]

end Lightlike.Upstream.GeodesicExpansion
