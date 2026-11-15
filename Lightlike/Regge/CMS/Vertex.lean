import Mathlib
import Lightlike.Regge.Geodesic.DistExpansion

/-!
# The squared geodesic distance to a nearby point, to third order (RC6b, step 4b)

The first consequence of `IsRiemMetric.dist_sq_expansion`: for `x` in a compact set and `w` small,
`d(x, x + w)² = g_x(w, w) + O(‖w‖³)` uniformly. The cubic term is what makes the angles of the
geodesic triangle differ from the frozen-metric angles by `O(h)` (relative errors of order `h`).

## Main results

* `IsRiemMetric.dist_sq_sub_normSq_le`: `|d(x, x + w)² - g_x(w, w)| ≤ C ‖w‖³` for `x ∈ K`,
  `‖w‖ ≤ r`.
-/

open Set Filter Topology
open scoped Matrix

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The jet differs from the frozen quadratic form by a cubic term. -/
theorem abs_distJet_sub_normSq_le {x : Fin n → ℝ} {B δ l : ℝ} (h : LocalJet g U x B δ l)
    {w : Fin n → ℝ} (hw1 : ‖w‖ ≤ 1) :
    |distJet g x w - normSq g x w| ≤ (B / 2 + B / 6 + B ^ 3 / 12) * ‖w‖ ^ 3 := by
  have hB := h.one_le
  have hw0 := norm_nonneg w
  have h1 : |w ⬝ᵥ (dmat g x w *ᵥ w)| ≤ B * ‖w‖ ^ 3 := by
    have := h.d_le w w w
    calc _ ≤ B * ‖w‖ * ‖w‖ * ‖w‖ := this
      _ = _ := by ring
  have h2 : |w ⬝ᵥ (ddmat g x w w *ᵥ w)| ≤ B * ‖w‖ ^ 3 := by
    have := h.dd_le w w w w
    calc _ ≤ B * ‖w‖ * ‖w‖ * ‖w‖ * ‖w‖ := this
      _ ≤ B * ‖w‖ ^ 3 := by
        have : B * ‖w‖ * ‖w‖ * ‖w‖ * ‖w‖ = B * ‖w‖ ^ 3 * ‖w‖ := by ring
        rw [this]
        calc _ ≤ B * ‖w‖ ^ 3 * 1 := by gcongr
          _ = _ := mul_one _
  have h3 : |chr g x w w ⬝ᵥ (g x *ᵥ chr g x w w)| ≤ B ^ 3 * ‖w‖ ^ 3 := by
    have c := h.chr_le w w
    have := h.g_le (chr g x w w) (chr g x w w)
    calc _ ≤ B * ‖chr g x w w‖ * ‖chr g x w w‖ := this
      _ ≤ B * (B * ‖w‖ * ‖w‖) * (B * ‖w‖ * ‖w‖) := by gcongr
      _ = B ^ 3 * ‖w‖ ^ 4 := by ring
      _ ≤ B ^ 3 * ‖w‖ ^ 3 := by
        have : B ^ 3 * ‖w‖ ^ 4 = B ^ 3 * ‖w‖ ^ 3 * ‖w‖ := by ring
        rw [this]
        calc _ ≤ B ^ 3 * ‖w‖ ^ 3 * 1 := by gcongr
          _ = _ := mul_one _
  have e : distJet g x w - normSq g x w = (1 / 2) * (w ⬝ᵥ (dmat g x w *ᵥ w)) +
      (1 / 6) * (w ⬝ᵥ (ddmat g x w w *ᵥ w)) - (1 / 12) * (chr g x w w ⬝ᵥ (g x *ᵥ chr g x w w)) := by
    simp only [distJet, normSq]; ring
  rw [e]
  calc _ ≤ |(1 / 2) * (w ⬝ᵥ (dmat g x w *ᵥ w)) + (1 / 6) * (w ⬝ᵥ (ddmat g x w w *ᵥ w))| +
        |(1 / 12) * (chr g x w w ⬝ᵥ (g x *ᵥ chr g x w w))| := abs_sub _ _
    _ ≤ (|(1 / 2) * (w ⬝ᵥ (dmat g x w *ᵥ w))| + |(1 / 6) * (w ⬝ᵥ (ddmat g x w w *ᵥ w))|) +
        |(1 / 12) * (chr g x w w ⬝ᵥ (g x *ᵥ chr g x w w))| := by gcongr; exact abs_add_le _ _
    _ ≤ (B / 2 * ‖w‖ ^ 3 + B / 6 * ‖w‖ ^ 3) + B ^ 3 / 12 * ‖w‖ ^ 3 := by
        rw [abs_mul, abs_mul, abs_mul]
        norm_num
        refine add_le_add (add_le_add ?_ ?_) ?_ <;> nlinarith [h1, h2, h3]
    _ = _ := by ring

/-- **The squared geodesic distance to a nearby point to third order.** -/
theorem IsRiemMetric.dist_sq_sub_normSq_le (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C r : ℝ, 0 < r ∧ ∀ x ∈ K, ∀ w : Fin n → ℝ, ‖w‖ ≤ r →
      |dist g U x (x + w) ^ 2 - normSq g x w| ≤ C * ‖w‖ ^ 3 := by
  obtain ⟨C₁, r₁, hr₁, h₁⟩ := hg.dist_sq_expansion hK hKU
  obtain ⟨B, δ, l, hJ⟩ := hg.exists_localJet hK hKU
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, 1, one_pos, fun x hx => absurd hx (Set.notMem_empty x)⟩
  have hδ := (hJ x₀ hx₀).δ_pos
  refine ⟨|C₁| + (B / 2 + B / 6 + B ^ 3 / 12), min (min r₁ δ) 1, lt_min (lt_min hr₁ hδ) one_pos,
    fun x hx w hw => ?_⟩
  have hw1 : ‖w‖ ≤ 1 := hw.trans (min_le_right _ _)
  have hwr : ‖w‖ ≤ r₁ := hw.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hB := (hJ x hx).one_le
  have e1 := h₁ x hx w hwr
  have e2 := abs_distJet_sub_normSq_le (hJ x hx) hw1
  have hw0 := norm_nonneg w
  have h5 : ‖w‖ ^ 5 ≤ ‖w‖ ^ 3 := pow_le_pow_of_le_one hw0 hw1 (by norm_num)
  calc _ ≤ |dist g U x (x + w) ^ 2 - distJet g x w| + |distJet g x w - normSq g x w| := by
        have := abs_add_le (dist g U x (x + w) ^ 2 - distJet g x w) (distJet g x w - normSq g x w)
        simpa using this
    _ ≤ C₁ * ‖w‖ ^ 5 + (B / 2 + B / 6 + B ^ 3 / 12) * ‖w‖ ^ 3 := add_le_add e1 e2
    _ ≤ |C₁| * ‖w‖ ^ 3 + (B / 2 + B / 6 + B ^ 3 / 12) * ‖w‖ ^ 3 := by
        have a1 : C₁ * ‖w‖ ^ 5 ≤ |C₁| * ‖w‖ ^ 5 := by gcongr; exact le_abs_self _
        have a2 : |C₁| * ‖w‖ ^ 5 ≤ |C₁| * ‖w‖ ^ 3 := by gcongr
        linarith
    _ = _ := by ring

end Lightlike.Geodesic
