import Lightlike.TuraevViro.Reflect.JacksonDegenerate

/-!
# Checks of the partial sums of the degenerate Jackson series

`tDeg_sum` at `q = 2`, `a = 3`, `c = 5`, `n = 2` is an equality of two explicit complex numbers,
and the closed form with a changed parameter is a different number.
-/

namespace Lightlike.TV.Refl
open Finset

/-- `tDeg_sum` at `q = 2`, `a = 3`, `c = 5`, `N = n = 2`. -/
theorem tDeg_sum_example :
    ∑ k ∈ range 3, tDeg (2 : ℂ) 3 5 k = sDeg 2 3 5 2 :=
  tDeg_sum (N := 2) (by norm_num) (by norm_num) (by norm_num)
    (by
      intro i hi
      interval_cases i <;> norm_num) 2 le_rfl

/-- Wrong-input control: with `c = 7` in the closed form the sum differs. -/
theorem tDeg_sum_example_wrong :
    ∑ k ∈ range 3, tDeg (2 : ℂ) 3 5 k ≠ sDeg 2 3 7 2 := by
  rw [tDeg_sum_example]
  simp only [sDeg, pk]
  norm_num

end Lightlike.TV.Refl
