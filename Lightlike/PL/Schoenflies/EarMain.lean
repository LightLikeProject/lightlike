import Mathlib
import Lightlike.PL.Schoenflies.EarRot
import Lightlike.PL.PolygonEars

/-!
# The ear induction: existence of the Schoenflies map

Piece 15 of the polygonal Schoenflies theorem (row G3-188, milestone PL5).  By strong induction on
the number of vertices: a triangle is the base case (`spec_triangle`); a simple polygon with at least
`4` vertices has an ear (`two_ears`), which we rotate to the vertex `0` (`spec_of_rot`) and clip
(`ear_step`).
-/

namespace Lightlike.PL.Schoenflies

open Set

/-- **Polygonal Schoenflies, existence form.**  For a simple polygon `p` and a convex polygon `c`
(strictly convex position, counterclockwise) with the same number `n ≥ 3` of vertices there is a map
`f` carrying the closed region of `p` bijectively onto the convex hull of `c`, edge by edge affinely
(`p i ↦ c i`), and piecewise affine on finitely many triangles covering the region. -/
theorem exists_spec : ∀ (n : ℕ) [NeZero n] (p c : Polygon n), 3 ≤ n → p.IsSimple →
    StrictConvexPos c → ∃ f, Spec p c f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro _ p c h3 hs hc
    rcases Nat.lt_or_ge n 4 with h | h4
    · obtain rfl : n = 3 := by omega
      exact spec_triangle hs hc
    · obtain ⟨k, hk, hE⟩ := (Polygon.two_ears n p h4 hs).exists_nowrap
      let β : Fin n := ⟨k, by omega⟩
      have hear : (p.rot β).Ear 0 := by
        rw [Polygon.ear_rot]; simpa [β] using hE
      obtain ⟨f, hf⟩ := ear_step h4 (Polygon.isSimple_rot hs β) hear (scp_rot hc β)
        (fun p' c' hs' hc' => ih (n - 2 + 1) (by omega) p' c' (by omega) hs' hc')
      exact ⟨f, spec_of_rot β hf⟩

end Lightlike.PL.Schoenflies
