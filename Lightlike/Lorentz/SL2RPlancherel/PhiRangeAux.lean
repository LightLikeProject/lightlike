import Mathlib

/-!
# A crude `L²` bound for bounded functions with bounded support

Used for the `H¹` approximation in the surjectivity of the spherical Plancherel isometry for
`SL(2,ℝ)` (milestone HA3).
-/

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- If `D` vanishes for `|t| > T` and `‖D‖ ≤ B`, then `∫ ‖D‖² ≤ 2 T B²`. -/
theorem integral_norm_sq_le_of_support (D : ℝ → ℂ) (T B : ℝ) (hT : 0 ≤ T)
    (hs : ∀ t, T < |t| → D t = 0) (hb : ∀ t, ‖D t‖ ≤ B) :
    ∫ x, ‖D x‖ ^ 2 ≤ 2 * T * B ^ 2 := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb 0)
  have h1 : ∫ x, ‖D x‖ ^ 2 = ∫ x in Icc (-T) T, ‖D x‖ ^ 2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have : T < |x| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · exact lt_of_lt_of_le h (le_abs_self x)
    simp [hs x this]
  rw [h1]
  have h2 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (-T) T)
    (f := fun x => ‖D x‖ ^ 2) (C := B ^ 2) (by simp) (fun x _ => by
      rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2)
  refine (le_abs_self _).trans (h2.trans ?_)
  rw [Real.volume_real_Icc_of_le (by linarith)]
  apply le_of_eq; ring

end Lightlike.Lorentz.SL2RPlancherel
