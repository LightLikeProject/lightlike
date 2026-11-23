import Mathlib
import Lightlike.Rows.G1_062.Sphere
import Lightlike.Rows.G1_062.Defs

/-!
# The half-integer theta sum and the 2-sphere heat trace

With `S(t) = ∑ₗ (2l+1) e^{-t (l+1/2)²}` we show

* `xs 1 h = h² S(h²)`, hence `S(t) = 1/t + 1/12 + 7t/480 + O(t²)` on `(0, 1]`;
* the heat trace of the unit 2-sphere (eigenvalues `l(l+1)`, multiplicity `2l+1`) is
  `Z(t) = e^{t/4} S(t)`.
-/

open Set Filter Topology

namespace Lightlike.Rows.G1_062

/-- The half-integer theta sum `S(t) = ∑ₗ (2l+1) e^{-t (l+1/2)²}`. -/
noncomputable def thetaHalf (t : ℝ) : ℝ :=
  ∑' l : ℕ, (2 * (l : ℝ) + 1) * Real.exp (-t * ((l : ℝ) + 1 / 2) ^ 2)

lemma gu_one_mid (h : ℝ) (l : ℕ) :
    gu 1 (mid h l) = h * ((2 * (l : ℝ) + 1) * Real.exp (-h ^ 2 * ((l : ℝ) + 1 / 2) ^ 2)) := by
  rw [gu_one, mid]
  have : -(((l : ℝ) + 1 / 2) * h) ^ 2 = -h ^ 2 * ((l : ℝ) + 1 / 2) ^ 2 := by ring
  rw [this]
  ring

lemma xs_one_eq (h : ℝ) : xs 1 h = h ^ 2 * thetaHalf (h ^ 2) := by
  unfold xs thetaHalf
  simp_rw [gu_one_mid]
  rw [tsum_mul_left]
  ring

/-- `S(t) = 1/t + 1/12 + 7t/480 + O(t²)` uniformly on `(0, 1]`. -/
theorem thetaHalf_expansion : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
    |thetaHalf t - 1 / t - 1 / 12 - 7 * t / 480| ≤ C * t ^ 2 := by
  obtain ⟨C, hC, H⟩ := xs_one_expansion
  refine ⟨C, hC, fun t ht0 ht1 => ?_⟩
  have hs := Real.sqrt_pos.mpr ht0
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hle : Real.sqrt t ≤ 1 := by
    rw [Real.sqrt_le_one]; exact ht1
  have h := H (Real.sqrt t) hs hle
  rw [xs_one_eq, hsq] at h
  have h6 : Real.sqrt t ^ 6 = t ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hsq]
  have h4 : Real.sqrt t ^ 4 = t ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
  rw [h6, h4] at h
  have e : thetaHalf t - 1 / t - 1 / 12 - 7 * t / 480
      = (t * thetaHalf t - 1 - t / 12 - 7 * t ^ 2 / 480) / t := by
    field_simp
  rw [e, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
  calc _ ≤ C * t ^ 3 := h
    _ = C * t ^ 2 * t := by ring

/-- The 2-sphere heat trace `∑ₗ (2l+1) e^{-t l(l+1)}` (eigenvalues `l(l+1)`, multiplicity `2l+1`). -/
noncomputable def sphereTrace (t : ℝ) : ℝ :=
  heatTrace (fun l : ℕ => (l : ℝ) * ((l : ℝ) + 1)) (fun l => 2 * l + 1) t

lemma sphereTrace_eq (t : ℝ) : sphereTrace t = Real.exp (t / 4) * thetaHalf t := by
  unfold sphereTrace heatTrace thetaHalf
  rw [← tsum_mul_left]
  refine tsum_congr fun l => ?_
  have : -t * ((l : ℝ) * ((l : ℝ) + 1)) = t / 4 + -t * ((l : ℝ) + 1 / 2) ^ 2 := by ring
  rw [this, Real.exp_add]
  push_cast
  ring

end Lightlike.Rows.G1_062
