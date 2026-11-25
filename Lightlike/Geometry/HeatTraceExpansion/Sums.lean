import Mathlib
import Lightlike.Geometry.HeatTraceExpansion.Gauss

/-!
# Uniform bounds for the midpoint sums of the Gaussian chain

For a step `h ∈ (0, 1]` and the midpoints `m_j = (j + 1/2) h`, the sums
`h ∑_j |gu q m_j|` are bounded uniformly in `h`.  The two ingredients are the decay bound
`|gu q y| ≤ C / (1 + x)^2` for `y ≥ x ≥ 0` (`gu_le`) and the telescoping bound
`∑_{j<N} h / (1 + j h)^2 ≤ 1 + h` (`sumW_le`).
-/

open Set

namespace Lightlike.Rows.G1_062

/-- Decay of the derivative chain, in the form used on an interval `[x, y]`, `0 ≤ x ≤ y`. -/
lemma gu_le (q : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, 0 ≤ x → x ≤ y → |gu q y| ≤ C / (1 + x) ^ 2 := by
  obtain ⟨C, hC⟩ := gu_decay q
  have hC0 : 0 ≤ C := by simpa using (abs_nonneg (gu q 0)).trans (by simpa using hC 0)
  refine ⟨2 * C, by positivity, fun x y hx hxy => ?_⟩
  have h1 := hC y
  have hpos : 0 < (1 + x) ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  have h2 : (1 + x) ^ 2 ≤ 2 * (1 + y ^ 2) := by nlinarith [sq_nonneg (y - 1)]
  calc |gu q y| * (1 + x) ^ 2 ≤ |gu q y| * (2 * (1 + y ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = 2 * (|gu q y| * (1 + y ^ 2)) := by ring
    _ ≤ 2 * C := by linarith

/-- Telescoping bound for the weights `h / (1 + j h)^2`. -/
lemma sumW_aux {h : ℝ} (h0 : 0 < h) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), h / (1 + (j : ℝ) * h) ^ 2 ≤ h + 1 - 1 / (1 + (N : ℝ) * h) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have ha : 0 < 1 + (N : ℝ) * h := by positivity
    have hb : 0 < 1 + ((N + 1 : ℕ) : ℝ) * h := by positivity
    have hab : 1 + ((N + 1 : ℕ) : ℝ) * h = (1 + (N : ℝ) * h) + h := by push_cast; ring
    have h1 : 1 / (1 + (N : ℝ) * h) - 1 / (1 + ((N + 1 : ℕ) : ℝ) * h)
        = h / ((1 + (N : ℝ) * h) * (1 + ((N + 1 : ℕ) : ℝ) * h)) := by
      rw [hab]; field_simp; ring
    have h2 : h / (1 + ((N + 1 : ℕ) : ℝ) * h) ^ 2
        ≤ h / ((1 + (N : ℝ) * h) * (1 + ((N + 1 : ℕ) : ℝ) * h)) := by
      rw [sq]
      apply div_le_div_of_nonneg_left h0.le (by positivity)
      exact mul_le_mul_of_nonneg_right (by rw [hab]; linarith) hb.le
    linarith

/-- `∑_{j<N} h / (1 + j h)^2 ≤ 1 + h`. -/
lemma sumW_le {h : ℝ} (h0 : 0 < h) (N : ℕ) :
    ∑ j ∈ Finset.range N, h / (1 + (j : ℝ) * h) ^ 2 ≤ 1 + h := by
  cases N with
  | zero => simp; linarith
  | succ N =>
    have := sumW_aux h0 N
    have h3 : 0 < 1 / (1 + (N : ℝ) * h) := by positivity
    linarith

/-- The `j`-th midpoint. -/
noncomputable def mid (h : ℝ) (j : ℕ) : ℝ := ((j : ℝ) + 1 / 2) * h

lemma mid_nonneg {h : ℝ} (h0 : 0 ≤ h) (j : ℕ) : 0 ≤ mid h j := by
  unfold mid; positivity

lemma le_mid {h : ℝ} (h0 : 0 ≤ h) (j : ℕ) : (j : ℝ) * h ≤ mid h j := by
  unfold mid; nlinarith

/-- Partial sums of `h |gu q (mid h j)|` are bounded by `2 C`, uniformly in `h ∈ (0,1]`. -/
lemma sum_abs_gu_mid_le (q : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ N : ℕ,
    ∑ j ∈ Finset.range N, h * |gu q (mid h j)| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := gu_le q
  refine ⟨2 * C, by positivity, fun h h0 h1 N => ?_⟩
  have hb : ∀ j ∈ Finset.range N, h * |gu q (mid h j)| ≤ C * (h / (1 + (j : ℝ) * h) ^ 2) := by
    intro j _
    have := hC ((j : ℝ) * h) (mid h j) (by positivity) (le_mid h0.le j)
    calc h * |gu q (mid h j)| ≤ h * (C / (1 + (j : ℝ) * h) ^ 2) :=
          mul_le_mul_of_nonneg_left this h0.le
      _ = _ := by ring
  calc ∑ j ∈ Finset.range N, h * |gu q (mid h j)|
      ≤ ∑ j ∈ Finset.range N, C * (h / (1 + (j : ℝ) * h) ^ 2) := Finset.sum_le_sum hb
    _ = C * ∑ j ∈ Finset.range N, h / (1 + (j : ℝ) * h) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left (by linarith [sumW_le h0 N]) hC0
    _ = 2 * C := by ring

/-- For fixed `h > 0` the midpoint values of `gu q` are summable. -/
lemma summable_gu_mid (q : ℕ) {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) :
    Summable (fun j : ℕ => gu q (mid h j)) := by
  obtain ⟨C, -, hC⟩ := sum_abs_gu_mid_le q
  have hs : Summable (fun j : ℕ => h * |gu q (mid h j)|) :=
    summable_of_sum_range_le (fun j => by positivity) (fun N => hC h h0 h1 N)
  have hs' : Summable (fun j : ℕ => |gu q (mid h j)|) :=
    (summable_mul_left_iff h0.ne').mp hs
  exact hs'.of_abs

end Lightlike.Rows.G1_062
