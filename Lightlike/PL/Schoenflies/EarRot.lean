import Mathlib
import Lightlike.PL.Schoenflies.EarStep

/-!
# Rotating the starting vertex in the polygonal Schoenflies induction

Piece 14 of the polygonal Schoenflies theorem (row G3-188, milestone PL5).  The ear step needs an
ear at the vertex `0`; `two_ears` gives an ear at some vertex.  Re-indexing both polygons by the same
rotation does not change the problem: `spec_of_rot`.
-/

namespace Lightlike.PL.Schoenflies

open Set

/-- The region of a polygon does not depend on the starting vertex. -/
lemma region_rot {n : ℕ} [NeZero n] (p : Polygon n) (β : Fin n) : region (p.rot β) = region p := by
  unfold region
  rw [Polygon.inside_rot, Polygon.carrier_rot]

/-- **Rotation invariance of the induction statement.**  A solution for the rotated pair of polygons
is a solution for the original pair. -/
lemma spec_of_rot {n : ℕ} [NeZero n] {p c : Polygon n} {f : ℝ × ℝ → ℝ × ℝ} (β : Fin n)
    (h : Spec (p.rot β) (c.rot β) f) : Spec p c f := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rwa [region_rot, range_rot] at h1
  · intro i t ht
    have hβ := β.2
    have e0 : ∀ r : Polygon n, (r.rot β).cyc (i + (n - β)) = r.cyc i := fun r => by
      rw [Polygon.rot_cyc, show i + (n - (β : ℕ)) + β = n + i by omega, Polygon.cyc_self_add]
    have e1 : ∀ r : Polygon n, (r.rot β).cyc (i + (n - β) + 1) = r.cyc (i + 1) := fun r => by
      rw [Polygon.rot_cyc, show i + (n - (β : ℕ)) + 1 + β = n + (i + 1) by omega,
        Polygon.cyc_self_add]
    have := h2 (i + (n - β)) t ht
    rwa [e0, e1, e0, e1] at this
  · rwa [region_rot] at h3

end Lightlike.PL.Schoenflies
