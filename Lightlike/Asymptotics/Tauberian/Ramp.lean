import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Field

/-!
# Continuous one-sided approximations of the indicator of `[e⁻¹, 1]`

For `0 < c < e⁻¹ < d` the continuous functions on `[0, 1]`

* `rampUp c y = max 0 (min 1 ((y - c) / (e⁻¹ - c))) / max y e⁻¹`,
* `rampDown d y = max 0 (min 1 ((y - e⁻¹) / (d - e⁻¹))) / max y e⁻¹`

satisfy `y · rampDown d y ≤ 1_{y ≥ e⁻¹} ≤ y · rampUp c y`-type bounds
(`mul_rampUp_le`, `mul_rampUp_eq_one`, `mul_rampDown_le`, `mul_rampDown_eq_one`): they sandwich the
indicator of `{x ≤ t}` after the substitution `y = exp (-x/t)`.
-/

open Real

noncomputable section

namespace Lightlike.Tauberian

/-- The ramp `max 0 (min 1 ((y - a) / (b - a)))`. -/
def ramp (a b y : ℝ) : ℝ := max 0 (min 1 ((y - a) / (b - a)))

lemma ramp_nonneg (a b y : ℝ) : 0 ≤ ramp a b y := le_max_left _ _

lemma ramp_le_one (a b y : ℝ) : ramp a b y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma continuous_ramp (a b : ℝ) : Continuous (ramp a b) := by
  unfold ramp; fun_prop

lemma ramp_eq_zero {a b y : ℝ} (hy : y ≤ a) (hab : a < b) : ramp a b y = 0 := by
  unfold ramp
  have : (y - a) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  simp [this]

lemma ramp_eq_one {a b y : ℝ} (hy : b ≤ y) (hab : a < b) : ramp a b y = 1 := by
  unfold ramp
  have : 1 ≤ (y - a) / (b - a) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  simp [this]

/-- `e⁻¹`. -/
abbrev einv : ℝ := Real.exp (-1)

lemma einv_pos : 0 < einv := Real.exp_pos _

/-- The upper ramp function. -/
def rampUp (c y : ℝ) : ℝ := ramp c einv y / max y einv

/-- The lower ramp function. -/
def rampDown (d y : ℝ) : ℝ := ramp einv d y / max y einv

lemma continuous_rampUp (c : ℝ) : Continuous (rampUp c) := by
  unfold rampUp
  exact (continuous_ramp c einv).div (continuous_id.max continuous_const)
    (fun y => (lt_of_lt_of_le einv_pos (le_max_right _ _)).ne')

lemma continuous_rampDown (d : ℝ) : Continuous (rampDown d) := by
  unfold rampDown
  exact (continuous_ramp einv d).div (continuous_id.max continuous_const)
    (fun y => (lt_of_lt_of_le einv_pos (le_max_right _ _)).ne')

lemma rampUp_nonneg (c y : ℝ) : 0 ≤ rampUp c y :=
  div_nonneg (ramp_nonneg _ _ _) (lt_of_lt_of_le einv_pos (le_max_right _ _)).le

lemma rampDown_nonneg (d y : ℝ) : 0 ≤ rampDown d y :=
  div_nonneg (ramp_nonneg _ _ _) (lt_of_lt_of_le einv_pos (le_max_right _ _)).le

/-- `y * rampUp c y ≤ 1` for `y ≥ 0`, and it vanishes for `y ≤ c`. -/
lemma mul_rampUp_le (c : ℝ) {y : ℝ} (hy : 0 ≤ y) : y * rampUp c y ≤ 1 := by
  unfold rampUp
  have hm : 0 < max y einv := lt_of_lt_of_le einv_pos (le_max_right _ _)
  rw [mul_div_assoc', div_le_one hm]
  calc y * ramp c einv y ≤ max y einv * 1 :=
        mul_le_mul (le_max_left _ _) (ramp_le_one _ _ _) (ramp_nonneg _ _ _) hm.le
    _ = max y einv := mul_one _

lemma mul_rampUp_eq_zero {c y : ℝ} (hy : y ≤ c) (hc : c < einv) : y * rampUp c y = 0 := by
  unfold rampUp
  rw [ramp_eq_zero hy hc]; simp

/-- `y * rampUp c y = 1` for `y ≥ e⁻¹`. -/
lemma mul_rampUp_eq_one {c y : ℝ} (hy : einv ≤ y) (hc : c < einv) : y * rampUp c y = 1 := by
  unfold rampUp
  rw [ramp_eq_one hy hc, max_eq_left hy]
  have : y ≠ 0 := (lt_of_lt_of_le einv_pos hy).ne'
  field_simp

/-- `y * rampDown d y ≤ 1` for `y ≥ 0` and `= 0` for `y ≤ e⁻¹`. -/
lemma mul_rampDown_le (d : ℝ) {y : ℝ} (hy : 0 ≤ y) : y * rampDown d y ≤ 1 := by
  unfold rampDown
  have hm : 0 < max y einv := lt_of_lt_of_le einv_pos (le_max_right _ _)
  rw [mul_div_assoc', div_le_one hm]
  calc y * ramp einv d y ≤ max y einv * 1 :=
        mul_le_mul (le_max_left _ _) (ramp_le_one _ _ _) (ramp_nonneg _ _ _) hm.le
    _ = max y einv := mul_one _

lemma mul_rampDown_eq_zero {d y : ℝ} (hy : y ≤ einv) (hd : einv < d) : y * rampDown d y = 0 := by
  unfold rampDown
  rw [ramp_eq_zero hy hd]; simp

lemma mul_rampDown_eq_one {d y : ℝ} (hy : d ≤ y) (hd : einv < d) : y * rampDown d y = 1 := by
  unfold rampDown
  have hy' : einv ≤ y := hd.le.trans hy
  rw [ramp_eq_one hy hd, max_eq_left hy']
  have : y ≠ 0 := (lt_of_lt_of_le einv_pos hy').ne'
  field_simp

end Lightlike.Tauberian
