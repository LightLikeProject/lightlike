import Lightlike.Asymptotics.Tauberian.Majorant
import Lightlike.Asymptotics.Tauberian.LocalBound
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Facts about the smoothing kernel `κ(u) = (2 b sinc (b u))⁴`

`0 ≤ κ ≤ 16 b⁴`, `κ(u) ≤ 16 / u⁴`, `κ` is even, continuous and integrable; its tail
`∫_y^∞ κ ≤ 16 / (3 y³)` and its second moment is finite.
-/

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Lightlike.Tauberian

/-- The kernel `κ(u) = (2 b sinc (b u))⁴`. -/
def kap (b u : ℝ) : ℝ := (2 * b * Real.sinc (b * u)) ^ 4

lemma kap_nonneg (b u : ℝ) : 0 ≤ kap b u := by unfold kap; positivity

lemma kap_even (b u : ℝ) : kap b (-u) = kap b u := by
  unfold kap; rw [mul_neg, Real.sinc_neg]

lemma continuous_kap (b : ℝ) : Continuous (kap b) := by
  unfold kap; exact (continuous_const.mul (Real.continuous_sinc.comp (continuous_const.mul continuous_id))).pow 4

lemma kap_le_const (b u : ℝ) : kap b u ≤ 16 * b ^ 4 := by
  unfold kap
  have h := Real.abs_sinc_le_one (b * u)
  have : Real.sinc (b * u) ^ 4 ≤ 1 := by
    calc Real.sinc (b * u) ^ 4 = |Real.sinc (b * u)| ^ 4 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
      _ ≤ 1 := pow_le_one₀ (abs_nonneg _) h
  calc (2 * b * Real.sinc (b * u)) ^ 4 = 16 * b ^ 4 * Real.sinc (b * u) ^ 4 := by ring
    _ ≤ 16 * b ^ 4 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
    _ = 16 * b ^ 4 := mul_one _

/-- `κ(u) ≤ 16 / u⁴`. -/
lemma kap_le_inv {b : ℝ} (hb : 0 < b) {u : ℝ} (hu : u ≠ 0) : kap b u ≤ 16 / u ^ 4 := by
  unfold kap
  have hbu : b * u ≠ 0 := mul_ne_zero hb.ne' hu
  rw [Real.sinc_of_ne_zero hbu]
  have h1 : |Real.sin (b * u)| ≤ 1 := Real.abs_sin_le_one _
  have h2 : (Real.sin (b * u) / (b * u)) ^ 4 ≤ (1 / (b * u)) ^ 4 := by
    have : |Real.sin (b * u) / (b * u)| ≤ |1 / (b * u)| := by
      rw [abs_div, abs_div, abs_one]
      exact div_le_div_of_nonneg_right h1 (abs_nonneg _)
    calc (Real.sin (b * u) / (b * u)) ^ 4 = |Real.sin (b * u) / (b * u)| ^ 4 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
      _ ≤ |1 / (b * u)| ^ 4 := pow_le_pow_left₀ (abs_nonneg _) this 4
      _ = (1 / (b * u)) ^ 4 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  calc (2 * b * (Real.sin (b * u) / (b * u))) ^ 4 = 16 * b ^ 4 * (Real.sin (b * u) / (b * u)) ^ 4 := by ring
    _ ≤ 16 * b ^ 4 * (1 / (b * u)) ^ 4 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 16 / u ^ 4 := by field_simp

lemma integrable_kap {b : ℝ} (hb : 0 < b) : Integrable (kap b) := by
  have h1 : Integrable (fun u : ℝ => 32 * b ^ 4 / (1 + (b * u) ^ 2)) := by
    have := (integrable_inv_one_add_sq).comp_mul_left' hb.ne'
    exact (this.const_mul (32 * b ^ 4)).congr (Filter.Eventually.of_forall fun u => by
      simp only [div_eq_mul_inv])
  refine h1.mono' (continuous_kap b).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (kap_nonneg b u)]
  unfold kap
  have h := sinc_pow_four_le (b * u)
  calc (2 * b * Real.sinc (b * u)) ^ 4 = 16 * b ^ 4 * Real.sinc (b * u) ^ 4 := by ring
    _ ≤ 16 * b ^ 4 * (2 / (1 + (b * u) ^ 2)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = 32 * b ^ 4 / (1 + (b * u) ^ 2) := by ring

/-- The total mass `N = ∫ κ`. -/
def kapN (b : ℝ) : ℝ := ∫ u, kap b u

lemma kapN_pos {b : ℝ} (hb : 0 < b) : 0 < kapN b := by
  unfold kapN
  rw [integral_pos_iff_support_of_nonneg (kap_nonneg b) (integrable_kap hb)]
  have h0 : kap b 0 ≠ 0 := by
    unfold kap; simp; exact hb.ne'
  have hopen : IsOpen (Function.support (kap b)) :=
    (continuous_kap b).isOpen_support
  have : (Function.support (kap b)).Nonempty := ⟨0, h0⟩
  exact hopen.measure_pos volume this

/-- The tail `∫_{u > y} κ ≤ 16/(3 y³)`. -/
lemma tail_kap_le {b : ℝ} (hb : 0 < b) {y : ℝ} (hy : 0 < y) :
    ∫ u in Ioi y, kap b u ≤ 16 / (3 * y ^ 3) := by
  have hI : IntegrableOn (fun u : ℝ => 16 * u ^ (-4 : ℝ)) (Ioi y) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hy).const_mul 16
  have hint : IntegrableOn (kap b) (Ioi y) := (integrable_kap hb).integrableOn
  calc ∫ u in Ioi y, kap b u ≤ ∫ u in Ioi y, 16 * u ^ (-4 : ℝ) := by
        refine setIntegral_mono_on hint hI measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 < u := lt_trans hy hu
        have := kap_le_inv hb hu0.ne'
        rw [Real.rpow_neg hu0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        calc kap b u ≤ 16 / u ^ 4 := this
          _ = 16 * (u ^ 4)⁻¹ := by rw [div_eq_mul_inv]
    _ = 16 / (3 * y ^ 3) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hy]
        rw [show (-4 : ℝ) + 1 = -3 by norm_num, Real.rpow_neg hy.le,
          show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp

/-- `|e^s - 1 - s| ≤ s² e^{max(s,0)}`. -/
lemma abs_exp_sub_one_sub_le (s : ℝ) : |Real.exp s - 1 - s| ≤ s ^ 2 * Real.exp (max s 0) := by
  by_cases h1 : |s| ≤ 1
  · have := Real.abs_exp_sub_one_sub_id_le h1
    refine this.trans ?_
    have : 1 ≤ Real.exp (max s 0) := Real.one_le_exp (le_max_right _ _)
    nlinarith [sq_nonneg s]
  · push Not at h1
    rcases lt_or_ge s 0 with hs | hs
    · -- `s < -1`
      have hs1 : s < -1 := by rw [abs_of_neg hs] at h1; linarith
      have h0 : 0 < Real.exp s := Real.exp_pos s
      have he : Real.exp s ≤ 1 := Real.exp_le_one_iff.2 hs.le
      have : |Real.exp s - 1 - s| ≤ -s := by
        rw [abs_le]; constructor <;> nlinarith
      refine this.trans ?_
      rw [max_eq_right hs.le, Real.exp_zero]
      nlinarith
    · have hs1 : 1 < s := by rw [abs_of_nonneg hs] at h1; exact h1
      rw [max_eq_left hs]
      have h0 : 0 < Real.exp s := Real.exp_pos s
      have : |Real.exp s - 1 - s| ≤ Real.exp s := by
        rw [abs_le]; constructor <;> nlinarith [Real.add_one_le_exp s]
      refine this.trans ?_
      have : 1 ≤ s ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right this h0.le]

lemma integrable_sq_kap {b : ℝ} (hb : 0 < b) : Integrable (fun u : ℝ => u ^ 2 * kap b u) := by
  have h1 : Integrable (fun u : ℝ => (32 + 32 * b ^ 4) * (1 + u ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine h1.mono' ((continuous_pow 2).mul (continuous_kap b)).aestronglyMeasurable
    ?_
  refine Filter.Eventually.of_forall fun u => ?_
  have hk0 := kap_nonneg b u
  rw [Real.norm_of_nonneg (by positivity)]
  show u ^ 2 * kap b u ≤ (32 + 32 * b ^ 4) * (1 + u ^ 2)⁻¹
  rw [← div_eq_mul_inv (32 + 32 * b ^ 4), le_div_iff₀ (by positivity)]
  by_cases hu : |u| ≤ 1
  · have h1 := kap_le_const b u
    have h2 : u ^ 2 ≤ 1 := by nlinarith [sq_abs u, abs_nonneg u]
    have hb4 : 0 ≤ b ^ 4 := by positivity
    nlinarith [mul_nonneg hk0 (sq_nonneg u), mul_le_mul_of_nonneg_left h2 hk0, sq_nonneg u]
  · push Not at hu
    have hu0 : u ≠ 0 := by intro h; rw [h, abs_zero] at hu; linarith
    have h1 := kap_le_inv hb hu0
    have h2 : 1 ≤ u ^ 2 := by nlinarith [sq_abs u]
    have h3 : u ^ 2 * kap b u ≤ 16 / u ^ 2 := by
      calc u ^ 2 * kap b u ≤ u ^ 2 * (16 / u ^ 4) := mul_le_mul_of_nonneg_left h1 (sq_nonneg u)
        _ = 16 / u ^ 2 := by field_simp
    have hb4 : 0 ≤ 32 * b ^ 4 := by positivity
    have h4 : 16 / u ^ 2 * (1 + u ^ 2) ≤ 32 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    calc u ^ 2 * kap b u * (1 + u ^ 2) ≤ 16 / u ^ 2 * (1 + u ^ 2) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ ≤ 32 := h4
      _ ≤ 32 + 32 * b ^ 4 := by linarith

end Lightlike.Tauberian
