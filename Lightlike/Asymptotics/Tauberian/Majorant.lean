import Lightlike.Asymptotics.Tauberian.Hks

/-!
# The Fejér-type majorant

`sinc` is decreasing on `[0, π]`, so `x ↦ (sinc (a))⁻⁴ sinc(x)⁴` is at least `1` for `|x| ≤ a < π`
and nonnegative everywhere: the majorant `φ₊` of MZ (4.9) for the indicator of `[-a, a]`.
-/

open Set Real

noncomputable section

namespace Lightlike.Tauberian

/-- `sinc` is decreasing on `[0, π]` (from the concavity of `sin`). -/
lemma sinc_antitoneOn : AntitoneOn Real.sinc (Icc 0 π) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hx.1 with h0 | hxpos
  · rw [← h0, Real.sinc_zero]; exact Real.sinc_le_one y
  · have hypos : 0 < y := hxpos.trans_le hxy
    have hc := strictConcaveOn_sin_Icc.concaveOn
    have h := hc.2 (show y ∈ Icc 0 π from hy) (show (0 : ℝ) ∈ Icc 0 π from ⟨le_refl _, pi_pos.le⟩)
      (show 0 ≤ x / y from by positivity) (show 0 ≤ 1 - x / y from by
        rw [sub_nonneg, div_le_one hypos]; exact hxy) (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.sin_zero] at h
    rw [show x / y * y = x by field_simp] at h
    rw [Real.sinc_of_ne_zero hxpos.ne', Real.sinc_of_ne_zero hypos.ne']
    rw [div_le_div_iff₀ hypos hxpos]
    have := mul_le_mul_of_nonneg_right h hypos.le
    rw [show x / y * Real.sin y * y = x * Real.sin y by field_simp] at this
    linarith

/-- The majorant `φ₊(x) = sinc(x)⁴ / sinc(a)⁴`. -/
def majorant (a x : ℝ) : ℝ := Real.sinc x ^ 4 / Real.sinc a ^ 4

lemma majorant_nonneg (a x : ℝ) : 0 ≤ majorant a x := by
  unfold majorant; positivity

/-- `φ₊ ≥ 1` on `[-a, a]` for `0 < a < π`. -/
lemma one_le_majorant {a : ℝ} (ha : 0 < a) (haπ : a < π) {x : ℝ} (hx : |x| ≤ a) :
    1 ≤ majorant a x := by
  have hapos : 0 < Real.sinc a := Real.sinc_pos (by rw [abs_of_pos ha]; exact haπ)
  have h1 : Real.sinc a ≤ Real.sinc |x| :=
    sinc_antitoneOn ⟨abs_nonneg x, hx.trans haπ.le⟩ ⟨ha.le, haπ.le⟩ hx
  have h2 : Real.sinc |x| = Real.sinc x := by
    rcases abs_choice x with h | h <;> rw [h]
    rw [Real.sinc_neg]
  unfold majorant
  rw [le_div_iff₀ (by positivity), one_mul]
  rw [h2] at h1
  exact pow_le_pow_left₀ hapos.le h1 4

/-- The majorant dominates the indicator of `[-a, a]`. -/
lemma indicator_le_majorant {a : ℝ} (ha : 0 < a) (haπ : a < π) (x : ℝ) :
    (Icc (-a) a).indicator (fun _ => (1 : ℝ)) x ≤ majorant a x := by
  by_cases hx : x ∈ Icc (-a) a
  · rw [Set.indicator_of_mem hx]
    exact one_le_majorant ha haπ (abs_le.2 hx)
  · rw [Set.indicator_of_notMem hx]; exact majorant_nonneg a x

end Lightlike.Tauberian
