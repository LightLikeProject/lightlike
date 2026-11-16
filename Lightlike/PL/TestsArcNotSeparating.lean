import Lightlike.PL.ArcNotSeparating
import Lightlike.PL.TestsJordan

/-!
# Checks of the arc theorem

Non-vacuity of `arc_not_separating`: a segment is an arc, so its complement is connected.
Wrong-model check: the unit circle is not an arc (it is a closed curve) and its complement is not
connected, by the weak Jordan theorem; so the hypothesis that the set is an arc cannot be dropped.
-/

open Set

namespace Lightlike.PL

/-- Non-vacuity: the complement of a segment is connected. -/
example : IsPreconnected (segment ℝ ((0 : ℝ), (0 : ℝ)) (1, 0))ᶜ :=
  arc_not_separating (IsArc.of_segment (by simp [Prod.ext_iff]))

/-- Wrong model: the complement of the unit circle is not connected (weak Jordan theorem), so the
conclusion of `arc_not_separating` fails for this closed curve. -/
example : ¬ IsPreconnected (range unitCircle)ᶜ :=
  weak_jordan unitCircle_continuous unitCircle_injective

end Lightlike.PL
