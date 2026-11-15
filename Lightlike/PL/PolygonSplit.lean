import Lightlike.PL.PolygonDiagonal3

/-!
# Splitting a polygon along a diagonal

The crossing test of the horizontal ray does not depend on the direction in which an edge is
traversed. This is what makes the parities of the two polygons obtained by cutting along a
diagonal add up to the parity of the original polygon: the diagonal is an edge of both, traversed
in opposite directions, and contributes twice.

## Main results

* `Lightlike.PL.crossesRay_symm`: the ray crosses `[u, v]` exactly when it crosses `[v, u]`
-/

namespace Lightlike.PL

/-- The abscissa of the line through two points at a given height does not depend on the order of
the points, when they are at different heights. -/
lemma xAt_symm {u v : ℝ × ℝ} (h : u.2 ≠ v.2) (t : ℝ) : xAt u v t = xAt v u t := by
  unfold xAt
  have h1 : v.2 - u.2 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have h2 : u.2 - v.2 ≠ 0 := sub_ne_zero.2 h
  field_simp
  ring

/-- **The ray crosses an edge independently of the direction of the edge.** -/
theorem crossesRay_symm (u v x : ℝ × ℝ) : CrossesRay u v x ↔ CrossesRay v u x := by
  unfold CrossesRay
  by_cases h : u.2 = v.2
  · constructor <;> rintro ⟨h1 | h1, -⟩ <;> exfalso <;> linarith [h1.1, h1.2]
  · rw [xAt_symm h]
    exact and_congr_left' (or_comm)

end Lightlike.PL
