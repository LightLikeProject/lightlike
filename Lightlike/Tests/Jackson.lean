import Lightlike.TuraevViro.Reflect.JacksonWZ

/-!
# Non-vacuity of Jackson's sum `jackson_sum`

The hypotheses `JHyp` of `jackson_sum` hold at `q = 2`, `a = 3`, `b = 5`, `c = 7`, `N = 1`, so the
theorem is not vacuous; its instance at `n = 1` is a sum of two terms. A control with a changed
parameter on the right side fails. The sharper hypotheses `JHypT` hold, and `JHyp` fails, at
`q = 2`, `a = 3`, `b = 24`, `c = 7`, `N = 1`.
-/

namespace Lightlike.TV.Refl

/-- Non-vacuity: the hypotheses of `jackson_sum` hold at `q = 2`, `a = 3`, `b = 5`, `c = 7`, `N = 1`. -/
theorem jhyp_example : JHyp (2 : ℂ) 3 5 7 1 := by
  unfold JHyp
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; interval_cases i <;> norm_num
  · intro i hi; interval_cases i <;> norm_num
  · intro i hi; interval_cases i <;> norm_num
  · intro n hn; interval_cases n <;> intro i hi <;> interval_cases i <;> norm_num
  · intro n hn; interval_cases n <;> norm_num

/-- `jackson_sum` at those values, `n = 1`: a sum of two terms equals the right side. -/
theorem jackson_example :
    ∑ k ∈ Finset.range 2, Tj (2 : ℂ) 3 5 7 ((2 : ℂ) ^ 1) k = jacksonRhs 2 3 5 7 1 :=
  jackson_sum (N := 1) jhyp_example 1 le_rfl

/-- Wrong-input control: changing the parameter `c` of the right side breaks the equality. -/
theorem jackson_example_wrong :
    ∑ k ∈ Finset.range 2, Tj (2 : ℂ) 3 5 7 ((2 : ℂ) ^ 1) k ≠ jacksonRhs 2 3 5 8 1 := by
  rw [jackson_example]
  simp only [jacksonRhs, pk]
  norm_num

/-- The sharper hypotheses `JHypT` hold at `q = 2`, `a = 3`, `b = 24`, `c = 7`, `N = 1`, where
`aq/b = q⁻²`, so `1 - aq/b · q²` vanishes at index `2 ≤ N + 2`. -/
theorem jhypT_example : JHypT (2 : ℂ) 3 24 7 1 := by
  unfold JHypT
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; interval_cases i <;> norm_num
  · intro i hi; interval_cases i <;> norm_num
  · intro i hi; interval_cases i <;> norm_num
  · intro n hn; interval_cases n; intro i hi; interval_cases i <;> norm_num
  · intro n hn; interval_cases n; norm_num

/-- The stronger hypotheses `JHyp` fail at those values: `JHypT` is strictly weaker. -/
theorem not_jhyp_example : ¬ JHyp (2 : ℂ) 3 24 7 1 := by
  intro h
  have := h.2.2.2.2.2.1 2 (by norm_num)
  apply this; norm_num

/-- `jackson_sumT` at those values, `n = 1`, where `jackson_sum` does not apply. -/
theorem jackson_sumT_example :
    ∑ k ∈ Finset.range 2, Tj (2 : ℂ) 3 24 7 ((2 : ℂ) ^ 1) k = jacksonRhs 2 3 24 7 1 :=
  jackson_sumT (N := 1) jhypT_example 1 le_rfl

end Lightlike.TV.Refl
