import Mathlib
import Lightlike.Regge.CMS.Angle

/-!
# `arccos` is Lipschitz away from `±1` (RC6b, step 2)

A fat triangle has all its angles in `[κ, π - κ]`, so the cosines of its angles stay in `[-s, s]`
with `s = cos κ < 1`. On that interval `arccos` is Lipschitz with constant `1 / √(1 - s²)`. This is
the sensitivity estimate that turns a relative error of the squared edge lengths into an error of
the angles.

## Main results

* `abs_cosArg_sub_le`: if the squared lengths `a, b, c` of a triangle with `a + b ≤ R √(a b)` and
  `|a + b - c| ≤ 2 √(a b)` change by relative errors at most `ε ≤ 1/2`, the cosine
  `(a + b - c) / (2 √(a b))` changes by at most `2 (R + 1) ε`.
* `abs_arccos_sub_arccos_le`: for `x, y ∈ [-s, s]` with `0 ≤ s < 1`,
  `|arccos x - arccos y| ≤ |x - y| / √(1 - s²)`.
-/

open Real

namespace Lightlike.CMS

/-- **`arccos` is Lipschitz on `[-s, s]`, `s < 1`, with constant `1 / √(1 - s²)`.** -/
theorem abs_arccos_sub_arccos_le {s x y : ℝ} (hs0 : 0 ≤ s) (hs : s < 1) (hx : x ∈ Set.Icc (-s) s)
    (hy : y ∈ Set.Icc (-s) s) : |arccos x - arccos y| ≤ |x - y| / √(1 - s ^ 2) := by
  have hpos : 0 < √(1 - s ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hder : ∀ z ∈ Set.Icc (-s) s, HasDerivWithinAt arccos (-(1 / √(1 - z ^ 2))) (Set.Icc (-s) s) z :=
    fun z hz => (hasDerivAt_arccos (by linarith [hz.1]) (by linarith [hz.2])).hasDerivWithinAt
  have hbd : ∀ z ∈ Set.Icc (-s) s, ‖-(1 / √(1 - z ^ 2))‖ ≤ 1 / √(1 - s ^ 2) := by
    intro z hz
    have hz2 : z ^ 2 ≤ s ^ 2 := by nlinarith [hz.1, hz.2]
    have hle : √(1 - s ^ 2) ≤ √(1 - z ^ 2) := Real.sqrt_le_sqrt (by linarith)
    rw [norm_neg, Real.norm_of_nonneg (by positivity)]
    exact one_div_le_one_div_of_le hpos hle
  have := (convex_Icc (-s) s).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd hy hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  rw [div_eq_mul_inv, mul_comm, ← one_div]
  exact this

/-- **Sensitivity of the cosine to relative errors of the squared lengths.** The squared lengths
`a, b` (adjacent edges) change to `a', b'` by at most the relative error `ε ≤ 1/2`, the opposite
one `c` to `c'` by at most `ε (a + b)`. If the triangle has `a + b ≤ R √(a b)` (bounded side ratio)
and a genuine angle, `|a + b - c| ≤ 2 √(a b)`, then the cosine of its angle changes by at most
`2 (R + 1) ε`. -/
theorem abs_cosArg_sub_le {a b c a' b' c' R ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) (ha' : |a' - a| ≤ ε * a) (hb' : |b' - b| ≤ ε * b)
    (hc' : |c' - c| ≤ ε * (a + b)) (hR : a + b ≤ R * √(a * b))
    (hc : |a + b - c| ≤ 2 * √(a * b)) :
    |(a' + b' - c') / (2 * √(a' * b')) - (a + b - c) / (2 * √(a * b))| ≤ 2 * (R + 1) * ε := by
  set q := √(a * b) with hq
  set q' := √(a' * b') with hq'
  have hq0 : 0 < q := Real.sqrt_pos.mpr (mul_pos ha hb)
  have ha1 := abs_le.mp ha'
  have hb1 := abs_le.mp hb'
  have ha'0 : 0 ≤ a' := by nlinarith [ha1.1, mul_nonneg hε0 ha.le]
  have hb'0 : 0 ≤ b' := by nlinarith [hb1.1, mul_nonneg hε0 hb.le]
  have hlo : (1 - ε) * q ≤ q' := by
    rw [hq', hq, ← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 1 - ε), ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a' - (1 - ε) * a) (by linarith : (0 : ℝ) ≤ b' - (1 - ε) * b),
      mul_nonneg (by linarith : (0 : ℝ) ≤ a' - (1 - ε) * a) hb.le,
      mul_nonneg (by linarith : (0 : ℝ) ≤ b' - (1 - ε) * b) ha.le]
  have hhi : q' ≤ (1 + ε) * q := by
    rw [hq', hq, ← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 1 + ε), ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (1 + ε) * a - a') (by linarith : (0 : ℝ) ≤ (1 + ε) * b - b'),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (1 + ε) * a - a') hb'0,
      mul_nonneg (by linarith : (0 : ℝ) ≤ (1 + ε) * b - b') ha'0]
  have hq'0 : 0 < q' := lt_of_lt_of_le (by nlinarith) hlo
  have hN : |(a' + b' - c') - (a + b - c)| ≤ 2 * ε * (a + b) := by
    rw [abs_le] at hc' ⊢; constructor <;> nlinarith [hc'.1, hc'.2]
  have hD : |q' - q| ≤ ε * q := by rw [abs_le]; constructor <;> nlinarith
  have hRq : a + b ≤ R * q := hR
  have hεq : (1 - ε) ≥ 1 / 2 := by linarith
  have key : (a' + b' - c') / (2 * q') - (a + b - c) / (2 * q) =
      ((a' + b' - c') - (a + b - c)) / (2 * q') + (a + b - c) / (2 * q) * (q / q' - 1) := by
    field_simp; ring
  rw [key]
  have hR0 : 0 ≤ R := by
    by_contra h; have h := not_le.mp h; nlinarith [mul_pos hq0 hq0, add_pos ha hb]
  have t1 : |((a' + b' - c') - (a + b - c)) / (2 * q')| ≤ R * ε / (1 - ε) * 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * q'), div_le_iff₀ (by positivity)]
    have : 2 * ε * (a + b) ≤ 2 * ε * (R * q) := by gcongr
    have h3 : R * ε / (1 - ε) * (2 * ((1 - ε) * q)) = 2 * ε * (R * q) := by
      field_simp
    have h4 : R * ε / (1 - ε) * (2 * ((1 - ε) * q)) ≤ R * ε / (1 - ε) * 1 * (2 * q') := by
      rw [mul_one]; gcongr
    linarith
  have t2 : |(a + b - c) / (2 * q) * (q / q' - 1)| ≤ ε / (1 - ε) := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * q)]
    have h1 : |a + b - c| / (2 * q) ≤ 1 := by rw [div_le_one (by positivity)]; exact hc
    have h2 : |q / q' - 1| ≤ ε / (1 - ε) := by
      rw [show q / q' - 1 = (q - q') / q' by field_simp, abs_div, abs_of_pos hq'0,
        div_le_div_iff₀ hq'0 (by linarith)]
      rw [abs_sub_comm] at hD
      nlinarith [abs_nonneg (q - q')]
    calc _ ≤ 1 * (ε / (1 - ε)) := by gcongr
      _ = _ := one_mul _
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ R * ε / (1 - ε) * 1 + ε / (1 - ε) := add_le_add t1 t2
    _ ≤ 2 * (R + 1) * ε := by
        rw [mul_one, ← add_div, div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg hR0 hε0, mul_nonneg hε0 hε0]

/-- **The angle of a fat triangle is Lipschitz in the squared lengths.** Under the hypotheses of
`abs_cosArg_sub_le`, if the cosines of the angle before and after lie in `[-s, s]`, `s < 1`
(the angle is in `[arccos s, π - arccos s]`), the angle changes by at most
`2 (R + 1) ε / √(1 - s²)`. -/
theorem abs_triAngle_sub_le {a b c a' b' c' R ε s : ℝ} (ha : 0 < a) (hb : 0 < b) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) (ha' : |a' - a| ≤ ε * a) (hb' : |b' - b| ≤ ε * b)
    (hc' : |c' - c| ≤ ε * (a + b)) (hR : a + b ≤ R * √(a * b))
    (hc : |a + b - c| ≤ 2 * √(a * b)) (hs0 : 0 ≤ s) (hs : s < 1)
    (hu : (a + b - c) / (2 * √(a * b)) ∈ Set.Icc (-s) s)
    (hu' : (a' + b' - c') / (2 * √(a' * b')) ∈ Set.Icc (-s) s) :
    |triAngle a' b' c' - triAngle a b c| ≤ 2 * (R + 1) * ε / √(1 - s ^ 2) := by
  have h1 := abs_arccos_sub_arccos_le hs0 hs hu' hu
  have h2 := abs_cosArg_sub_le (R := R) ha hb hε0 hε ha' hb' hc' hR hc
  have hpos : 0 < √(1 - s ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  unfold triAngle
  calc _ ≤ _ := h1
    _ ≤ _ := by gcongr

/-- **Non-vacuity.** The hypotheses of `abs_triAngle_sub_le` hold for the equilateral triangle with
unit squared lengths, perturbed by `ε = 1/10` (`R = 2`, `s = 3/5`). -/
example : |triAngle (11 / 10) (11 / 10) (9 / 10) - triAngle 1 1 1| ≤
    2 * (2 + 1) * (1 / 10) / √(1 - (3 / 5 : ℝ) ^ 2) := by
  have h1 : √((1 : ℝ) * 1) = 1 := by simp
  have h2 : √((11 / 10 : ℝ) * (11 / 10)) = 11 / 10 := by
    rw [← sq, Real.sqrt_sq (by norm_num)]
  refine abs_triAngle_sub_le (R := 2) (ε := 1 / 10) (s := 3 / 5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [abs_le])
    (by norm_num [abs_le]) (by rw [h1]; norm_num) (by rw [h1]; norm_num [abs_le])
    (by norm_num) (by norm_num) ?_ ?_
  · rw [h1]; constructor <;> norm_num
  · rw [h2]; constructor <;> norm_num

end Lightlike.CMS
