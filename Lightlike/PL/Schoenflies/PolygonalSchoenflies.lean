import Mathlib
import Lightlike.PL.Schoenflies.EarFrontier
import Lightlike.PL.TestsPolygon

/-!
# The polygonal Schoenflies theorem

Row G3-188, milestone PL5.  **Version proved: the polygonal (PL) Schoenflies theorem in the plane, in
the convex-model form.**  Every simple closed polygon `p` with `n ≥ 3` vertices is carried onto any
convex polygon `c` with the same number of vertices (strictly convex position, counterclockwise) by a
piecewise affine bijection `f` of the closed regions that sends each vertex `p i` to `c i`, each edge
affinely onto the corresponding edge, the carrier of `p` onto the frontier of `hull c` and the inside
of `p` onto the interior of `hull c`.

The topological Schoenflies theorem (an arbitrary Jordan curve) is not proved here.  The Jordan
curve theorem for polygons is `Lightlike.PL.Polygon.polygon_jordan` on main.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL

/-- **Polygonal Schoenflies theorem (boundary form).**  Let `p` be a simple polygon and `c` a polygon
in strictly convex position (counterclockwise), both with `n ≥ 3` vertices.  Then there is a map `f`
of the plane such that
* `f` maps the closed region of `p` (inside and carrier) bijectively onto the convex hull of the
  vertices of `c`;
* `f (p i) = c i` for every vertex, and `f` is affine on each edge, sending the edge `p i → p (i+1)`
  onto the edge `c i → c (i+1)` (`EdgeAff`);
* `f` is piecewise affine: finitely many nondegenerate triangles cover the region and `f` is the
  affine map `triMap` on each (`PiecewiseTri`);
* `f` maps the carrier of `p` onto the frontier of the hull and the inside of `p` onto its
  interior. -/
theorem polygonal_schoenflies {n : ℕ} [NeZero n] {p c : Polygon n} (h3 : 3 ≤ n)
    (hs : p.IsSimple) (hc : StrictConvexPos c) :
    ∃ f : ℝ × ℝ → ℝ × ℝ,
      BijOn f (region p) (convexHull ℝ (range c)) ∧ (∀ i, f (p i) = c i) ∧ EdgeAff p c f ∧
      PiecewiseTri f (region p) ∧
      f '' p.carrier = frontier (convexHull ℝ (range c)) ∧
      f '' p.inside = interior (convexHull ℝ (range c)) := by
  obtain ⟨f, hbij, hedge, hpw⟩ := exists_spec n p c h3 hs hc
  have hcar : f '' p.carrier = frontier (convexHull ℝ (range c)) := by
    rw [image_carrier (by omega) hedge, carrier_eq_frontier_hull_scp h3 hc]
  refine ⟨f, hbij, ?_, hedge, hpw, hcar, ?_⟩
  · intro i
    have h := hedge i 0 ⟨le_rfl, zero_le_one⟩
    simp only [zero_smul, add_zero] at h
    rwa [p.cyc_of_lt i.2, c.cyc_of_lt i.2] at h
  · have hin : p.inside = region p \ p.carrier := by
      ext y
      constructor
      · intro hy; exact ⟨Or.inl hy, hy.1⟩
      · rintro ⟨hy | hy, hn⟩
        · exact hy
        · exact absurd hy hn
    have hsub : p.carrier ⊆ region p := subset_union_right
    rw [hin, hbij.injOn.image_sdiff_subset hsub, hbij.image_eq, hcar,
      (isClosed_hull c).frontier_eq, sdiff_sdiff_cancel_left interior_subset]

/-! ### Checks -/

/-- The triangle `(0,0), (1,0), (0,1)` is in strictly convex position. -/
lemma scp_triangle : StrictConvexPos Polygon.triangle := by
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | (exfalso; revert hij hjk; decide)
    | norm_num [Polygon.triangle, det3, cross]

/-- **Non-vacuity.**  The theorem applies to the unit triangle as source and target. -/
example : ∃ f : ℝ × ℝ → ℝ × ℝ,
    BijOn f (region Polygon.triangle) (convexHull ℝ (range Polygon.triangle)) ∧
    (∀ i, f (Polygon.triangle i) = Polygon.triangle i) :=
  let ⟨f, h1, h2, _⟩ := polygonal_schoenflies (by norm_num : 3 ≤ 3) Polygon.triangle_isSimple
    scp_triangle
  ⟨f, h1, h2⟩

/-- **Wrong input is rejected.**  A polygon in clockwise order is not in strictly convex position:
the theorem needs the counterclockwise orientation (a bijection preserving the cyclic vertex order
cannot match a clockwise `c` with a counterclockwise convex hull boundary). -/
example : ¬ StrictConvexPos (![(0, 0), (0, 1), (1, 0)] : Fin 3 → ℝ × ℝ) := by
  intro h
  have := h 0 1 2 (by decide) (by decide)
  norm_num [det3, cross] at this

end Lightlike.PL.Schoenflies
