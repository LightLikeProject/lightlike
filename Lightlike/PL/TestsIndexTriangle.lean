import Lightlike.PL.IndexTriangle
import Lightlike.PL.TestsIndex

/-!
# Checks of the index of a triangle

The triangle with corners `1`, `i`, `-1 - i` has index `1` about the origin. Wrong-model check: with the first two
corners exchanged the orientation hypothesis fails, so the lemma does not claim the same value for a clockwise
triangle. The index of the unit circle loop is zero about a point far away and about a point above it.
-/

open Complex unitInterval Real

namespace Lightlike.PL

/-- A concrete triangle around the origin has index `1`. -/
example : loopIndex (triangleLoop 1 Complex.I (-1 - Complex.I)) 0 = 1 := by
  refine loopIndex_triangle (q := 0) ?_ ?_ ?_ <;> simp [Complex.mul_im]

/-- Wrong model: for the clockwise order `i`, `1` the orientation hypothesis of `loopIndex_triangle` fails. -/
example : ¬ 0 < ((1 - (0 : ℂ)) * (starRingEnd ℂ) (Complex.I - 0)).im := by
  simp

/-- A loop in the unit disc has index zero about the point `2`. -/
example : loopIndex circleLoop 2 = 0 := by
  refine loopIndex_eq_zero_of_far circleLoop (ρ := 1) (fun t => ?_) ?_
  · simp [circleLoop, Complex.norm_exp]
  · norm_num

/-- The straight segment from `1` to `i` has increment `i π / 2` about the origin. -/
example : logInc (segPath 1 Complex.I) 0 = Complex.log Complex.I := by
  rw [logInc_segPath (by simp) (by simp [Complex.mem_slitPlane_iff])]
  simp

end Lightlike.PL
