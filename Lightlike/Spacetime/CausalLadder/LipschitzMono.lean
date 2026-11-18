import Mathlib

/-!
# Monotonicity of Lipschitz functions from an almost-everywhere derivative bound

A function that is Lipschitz on an interval is absolutely continuous, so it is the integral of its
derivative (Mathlib: `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`). Hence a Lipschitz
function whose derivative is almost everywhere nonnegative is monotone, and two Lipschitz
functions with `f' ≤ h'` almost everywhere satisfy `f b - f a ≤ h b - h a`. These are the real
analysis steps of the cone estimate for causal curves (`Lightlike.Causal`).

Supporting lemmas for the causal ladder; no catalogue entry.
-/

open Set MeasureTheory intervalIntegral

namespace Lightlike.Causal

/-- If `f` and `h` are Lipschitz on `[a, b]` and `f' ≤ h'` almost everywhere on `(a, b)`, then
`f b - f a ≤ h b - h a`. -/
theorem sub_le_sub_of_ae_deriv_le {f h : ℝ → ℝ} {a b : ℝ} {K L : NNReal} (hab : a ≤ b)
    (hf : LipschitzOnWith K f (Icc a b)) (hh : LipschitzOnWith L h (Icc a b))
    (hd : ∀ᵐ t, t ∈ Ioo a b →
      DifferentiableAt ℝ f t ∧ DifferentiableAt ℝ h t ∧ deriv f t ≤ deriv h t) :
    f b - f a ≤ h b - h a := by
  have hf' : LipschitzOnWith K f (uIcc a b) := by rwa [uIcc_of_le hab]
  have hh' : LipschitzOnWith L h (uIcc a b) := by rwa [uIcc_of_le hab]
  have hg : AbsolutelyContinuousOnInterval (h - f) a b :=
    (hh'.absolutelyContinuousOnInterval.sub hf'.absolutelyContinuousOnInterval)
  have key := hg.integral_deriv_eq_sub
  have hnn : 0 ≤ ∫ x in a..b, deriv (h - f) x := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict hab ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [hd, (Measure.ae_ne volume a), Measure.ae_ne volume b] with t ht hta htb hmem
    have hmem' : t ∈ Ioo a b := ⟨lt_of_le_of_ne hmem.1 (Ne.symm hta), lt_of_le_of_ne hmem.2 htb⟩
    obtain ⟨d1, d2, d3⟩ := ht hmem'
    have : deriv (h - f) t = deriv h t - deriv f t := deriv_sub d2 d1
    simp only [Pi.zero_apply, this]; linarith
  simp only [Pi.sub_apply] at key
  linarith
end Lightlike.Causal
