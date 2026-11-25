import Mathlib
import Lightlike.Geometry.HeatTraceExpansion.Level

/-!
# The midpoint sum `h ∑_j gu 1 (m_j)` up to order `h⁶`

Specialising `level` to `(p, m) = (4, 2), (2, 4), (0, 6)` and eliminating the sums `x₅`, `x₃`,
where `x_q (h) = h ∑'_j gu q (mid h j)`, gives
`x₁(h) = 1 + h²/12 + 7 h⁴/480 + O(h⁶)` on `(0, 1]`.
With `h = √t` and `gu 1 (m_l) = 2 m_l e^{-m_l²}` this is the expansion
`∑ (2l+1) e^{-t (l+1/2)²} = 1/t + 1/12 + 7t/480 + O(t²)` used for the 2-sphere trust check of T-GE8.
-/

open Set Filter Topology

namespace Lightlike.Geometry.HeatTraceExpansion

/-- The scaled midpoint sum `x_q(h) = h ∑'_j gu q (mid h j)`. -/
noncomputable def xs (q : ℕ) (h : ℝ) : ℝ := h * ∑' j : ℕ, gu q (mid h j)

lemma level_five : ∃ c : ℝ, 0 ≤ c ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → |12 - xs 5 h| ≤ c * h ^ 2 := by
  obtain ⟨c, hc0, hc⟩ := level 4 2
  refine ⟨c, hc0, fun h h0 h1 => ?_⟩
  have := hc h h0 h1
  have e : -gu 4 0 - ∑ k ∈ Finset.range (2 + 1),
        ((h / 2) ^ k - (-(h / 2)) ^ k) / (k.factorial : ℝ) * ∑' j : ℕ, gu (4 + k) (mid h j)
      = 12 - xs 5 h := by
    rw [gu_four_zero]
    simp [Finset.sum_range_succ, Nat.factorial, xs]
  rwa [e] at this

lemma level_three : ∃ c : ℝ, 0 ≤ c ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
    |-2 - xs 3 h - h ^ 2 / 24 * xs 5 h| ≤ c * h ^ 4 := by
  obtain ⟨c, hc0, hc⟩ := level 2 4
  refine ⟨c, hc0, fun h h0 h1 => ?_⟩
  have := hc h h0 h1
  have e : -gu 2 0 - ∑ k ∈ Finset.range (4 + 1),
        ((h / 2) ^ k - (-(h / 2)) ^ k) / (k.factorial : ℝ) * ∑' j : ℕ, gu (2 + k) (mid h j)
      = -2 - xs 3 h - h ^ 2 / 24 * xs 5 h := by
    rw [gu_two_zero]
    simp [Finset.sum_range_succ, Nat.factorial, xs]
    ring
  rwa [e] at this

lemma level_one : ∃ c : ℝ, 0 ≤ c ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
    |1 - xs 1 h - h ^ 2 / 24 * xs 3 h - h ^ 4 / 1920 * xs 5 h| ≤ c * h ^ 6 := by
  obtain ⟨c, hc0, hc⟩ := level 0 6
  refine ⟨c, hc0, fun h h0 h1 => ?_⟩
  have := hc h h0 h1
  have e : -gu 0 0 - ∑ k ∈ Finset.range (6 + 1),
        ((h / 2) ^ k - (-(h / 2)) ^ k) / (k.factorial : ℝ) * ∑' j : ℕ, gu (0 + k) (mid h j)
      = 1 - xs 1 h - h ^ 2 / 24 * xs 3 h - h ^ 4 / 1920 * xs 5 h := by
    rw [gu_zero_zero]
    simp [Finset.sum_range_succ, Nat.factorial, xs]
    ring
  rwa [e] at this

/-- `h ∑'_j gu 1 (m_j) = 1 + h²/12 + 7h⁴/480 + O(h⁶)` uniformly on `(0, 1]`. -/
theorem xs_one_expansion : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
    |xs 1 h - 1 - h ^ 2 / 12 - 7 * h ^ 4 / 480| ≤ C * h ^ 6 := by
  obtain ⟨c1, hc1, H1⟩ := level_five
  obtain ⟨c3, hc3, H3⟩ := level_three
  obtain ⟨c5, hc5, H5⟩ := level_one
  refine ⟨c5 + c3 / 24 + c1 / 576 + c1 / 1920, by positivity, fun h h0 h1 => ?_⟩
  have a1 := H1 h h0 h1
  have a3 := H3 h h0 h1
  have a5 := H5 h h0 h1
  have key : xs 1 h - 1 - h ^ 2 / 12 - 7 * h ^ 4 / 480
      = -(1 - xs 1 h - h ^ 2 / 24 * xs 3 h - h ^ 4 / 1920 * xs 5 h)
        - h ^ 2 / 24 * (xs 3 h + 2 + h ^ 2 / 2) + h ^ 4 / 1920 * (12 - xs 5 h) := by ring
  -- d3 := xs 3 h + 2 + h^2/2 = -E2 + h^2/24 * (12 - xs 5)
  have d3 : xs 3 h + 2 + h ^ 2 / 2
      = -(-2 - xs 3 h - h ^ 2 / 24 * xs 5 h) + h ^ 2 / 24 * (12 - xs 5 h) := by ring
  have hh2 : 0 ≤ h ^ 2 := by positivity
  have b3 : |xs 3 h + 2 + h ^ 2 / 2| ≤ (c3 + c1 / 24) * h ^ 4 := by
    rw [d3]
    calc |-(-2 - xs 3 h - h ^ 2 / 24 * xs 5 h) + h ^ 2 / 24 * (12 - xs 5 h)|
        ≤ |-(-2 - xs 3 h - h ^ 2 / 24 * xs 5 h)| + |h ^ 2 / 24 * (12 - xs 5 h)| := abs_add_le _ _
      _ = |-2 - xs 3 h - h ^ 2 / 24 * xs 5 h| + h ^ 2 / 24 * |12 - xs 5 h| := by
          rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ h ^ 2 / 24)]
      _ ≤ c3 * h ^ 4 + h ^ 2 / 24 * (c1 * h ^ 2) := by gcongr
      _ = (c3 + c1 / 24) * h ^ 4 := by ring
  rw [key]
  have hh4 : 0 ≤ h ^ 4 := by positivity
  calc |-(1 - xs 1 h - h ^ 2 / 24 * xs 3 h - h ^ 4 / 1920 * xs 5 h)
        - h ^ 2 / 24 * (xs 3 h + 2 + h ^ 2 / 2) + h ^ 4 / 1920 * (12 - xs 5 h)|
      ≤ |-(1 - xs 1 h - h ^ 2 / 24 * xs 3 h - h ^ 4 / 1920 * xs 5 h)|
        + |h ^ 2 / 24 * (xs 3 h + 2 + h ^ 2 / 2)| + |h ^ 4 / 1920 * (12 - xs 5 h)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ = |1 - xs 1 h - h ^ 2 / 24 * xs 3 h - h ^ 4 / 1920 * xs 5 h|
        + h ^ 2 / 24 * |xs 3 h + 2 + h ^ 2 / 2| + h ^ 4 / 1920 * |12 - xs 5 h| := by
        rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ h ^ 2 / 24),
          abs_of_nonneg (by positivity : 0 ≤ h ^ 4 / 1920)]
    _ ≤ c5 * h ^ 6 + h ^ 2 / 24 * ((c3 + c1 / 24) * h ^ 4) + h ^ 4 / 1920 * (c1 * h ^ 2) := by
        gcongr
    _ ≤ (c5 + c3 / 24 + c1 / 576 + c1 / 1920) * h ^ 6 := by
        apply le_of_eq
        ring

end Lightlike.Geometry.HeatTraceExpansion

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_062.level_five := _root_.Lightlike.Geometry.HeatTraceExpansion.level_five
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_062.level_one := _root_.Lightlike.Geometry.HeatTraceExpansion.level_one
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_062.level_three := _root_.Lightlike.Geometry.HeatTraceExpansion.level_three
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_062.xs := _root_.Lightlike.Geometry.HeatTraceExpansion.xs
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_062.xs_one_expansion := _root_.Lightlike.Geometry.HeatTraceExpansion.xs_one_expansion
