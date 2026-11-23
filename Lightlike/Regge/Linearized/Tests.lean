import Mathlib
import Lightlike.Regge.Linear.Deficit
import Lightlike.Regge.Linearized.ThinTriangle

/-!
# Trust checks for linearized Regge calculus (RC3)

* Flat background: the vertex deficit of the regular hexagonal star vanishes at every scale.
* Non-fat check: the angle sensitivity exceeds any prescribed bound, so no uniform constant exists
  over thin triangles (angle-level statement only).
-/

namespace Lightlike.Regge.Linearized

open Real Lightlike.Regge.Linear

/-- Flat background gives zero deficit: restatement of `flat_vertexDeficit` at scale `1`. -/
theorem flat_background_zero :
    2 * π - ∑ j : Fin 6, Lightlike.CMS.triAngle (1 ^ 2 * sqA j) (1 ^ 2 * sqB j) (1 ^ 2 * sqC j) = 0 :=
  flat_vertexDeficit one_pos

/-- Non-fat check, concrete instance: a triangle with angle sensitivity above `1000`. -/
theorem thin_sensitivity_exceeds_1000 :
    ∃ c d : ℝ, 0 < c ∧ c < 4 ∧
      HasDerivAt (fun ε : ℝ => Lightlike.CMS.triAngle (1 + ε * 0) (1 + ε * 0) (c + ε * 1)) d 0 ∧
        1000 < d :=
  thin_triangle_sensitivity_unbounded 1000

end Lightlike.Regge.Linearized
