import Mathlib
import Lightlike.Regge.Geodesic.Riemannian

/-!
# Triangle angles from squared edge lengths (RC6b, step 1)

The first brick of the convergence of Regge's deficit angles in dimension two (Cheeger, Müller and
Schrader). A piecewise flat surface is given by the squared lengths of its edges. The angle of a
triangle at a vertex is computed from them by the law of cosines. This file defines that angle and
proves that it is the Euclidean angle for every triangle in an inner product space, and that the
three angles of a triangle sum to `π`.

## Definitions

* `triAngle a b c`: the angle at the vertex whose two edges have squared lengths `a`, `b`, opposite
  to the edge of squared length `c`: `arccos ((a + b - c) / (2 √(a b)))`.

## Main results

* `triAngle_eq_angle`: for points `x v w`, `triAngle ‖x - v‖² ‖w - v‖² ‖x - w‖² = ∠ x v w`.
* `triAngle_sum`: the three angles of a triangle with distinct vertices sum to `π`.
-/

open Real EuclideanGeometry InnerProductGeometry

namespace Lightlike.CMS

/-- The angle at a vertex of a triangle from squared edge lengths: the two adjacent edges have
squared lengths `a`, `b`, the opposite edge `c`. It is `arccos ((a + b - c) / (2 √(a b)))`, a junk
value when `a` or `b` is `0`. -/
noncomputable def triAngle (a b c : ℝ) : ℝ := arccos ((a + b - c) / (2 * √(a * b)))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The law of cosines gives the Euclidean angle.** For points `x v w` of an inner product space,
the angle at `v` computed from the three squared distances is the Euclidean angle `∠ x v w`. -/
theorem triAngle_eq_angle (x v w : E) :
    triAngle (dist x v ^ 2) (dist w v ^ 2) (dist x w ^ 2) = ∠ x v w := by
  have hinner : inner ℝ (x -ᵥ v) (w -ᵥ v) =
      (dist x v ^ 2 + dist w v ^ 2 - dist x w ^ 2) / 2 := by
    have h := real_inner_sub_sub_self (x -ᵥ v) (w -ᵥ v)
    have h2 := norm_sub_sq_real (x -ᵥ v) (w -ᵥ v)
    simp only [vsub_eq_sub, dist_eq_norm] at h2 ⊢
    rw [sub_sub_sub_cancel_right] at h2
    nlinarith [h2, norm_sub_rev x w]
  unfold triAngle EuclideanGeometry.angle InnerProductGeometry.angle
  rw [hinner]
  congr 1
  have : √(dist x v ^ 2 * dist w v ^ 2) = dist x v * dist w v := by
    rw [← mul_pow, Real.sqrt_sq (by positivity)]
  simp only [vsub_eq_sub, dist_eq_norm] at this ⊢
  rw [this]
  field_simp

/-- **Angle sum.** The three angles computed from the squared lengths of a triangle with distinct
vertices add up to `π`. -/
theorem triAngle_sum (x y z : E) (hxy : x ≠ y) :
    triAngle (dist y x ^ 2) (dist z x ^ 2) (dist y z ^ 2) +
      triAngle (dist x y ^ 2) (dist z y ^ 2) (dist x z ^ 2) +
      triAngle (dist x z ^ 2) (dist y z ^ 2) (dist x y ^ 2) = π := by
  rw [triAngle_eq_angle, triAngle_eq_angle, triAngle_eq_angle]
  have := angle_add_angle_add_angle_eq_pi z (p₁ := x) (p₂ := y) (Ne.symm hxy)
  linarith [this, angle_comm y x z, angle_comm x y z, angle_comm x z y]

end Lightlike.CMS
