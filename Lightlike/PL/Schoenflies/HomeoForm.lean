import Mathlib
import Lightlike.PL.Schoenflies.PolygonalSchoenflies

/-!
# Polygonal Schoenflies: homeomorphism form and the convex model

Row G3-188, milestone PL5 (second pass).  Two consequences of `polygonal_schoenflies` that bring it
closer to the topological Schoenflies theorem:

* `exists_scp`: for every `n ≥ 3` there is a polygon in strictly convex position (points on a
  parabola), so the convex model needs no hypothesis;
* `PiecewiseTri.continuousOn`, `PiecewiseTri.isCompact`: a piecewise affine map is continuous on its
  (compact) region;
* `polygonal_schoenflies_homeo`: the closed region of every simple polygon with `n ≥ 3` vertices is
  homeomorphic to a compact convex polygon, by a homeomorphism that is piecewise affine, sends vertices
  to the vertices of the convex polygon and the carrier onto the frontier.

The topological Schoenflies theorem (arbitrary Jordan curve) is still not proved.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL

/-- Points on a parabola, indexed by `Fin n`. -/
def parabola (n : ℕ) : Polygon n := fun i => ((i : ℕ) , ((i : ℕ) : ℝ) ^ 2)

/-- The `det3` of three points on the parabola `y = x²`. -/
lemma det3_parabola (x y z : ℝ) :
    det3 (x, x ^ 2) (y, y ^ 2) (z, z ^ 2) = (y - x) * (z - x) * (z - y) := by
  simp only [det3, cross, Prod.fst_sub, Prod.snd_sub]; ring

/-- Points on a parabola are in strictly convex position. -/
lemma scp_parabola (n : ℕ) : StrictConvexPos (parabola n) := by
  intro i j k hij hjk
  have h1 : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
  have h2 : ((j : ℕ) : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast hjk
  simp only [parabola]
  rw [det3_parabola]
  have := sub_pos.mpr h1
  have := sub_pos.mpr h2
  have := sub_pos.mpr (h1.trans h2)
  positivity

/-- Strictly convex polygons exist for every number of vertices. -/
lemma exists_scp (n : ℕ) : ∃ c : Polygon n, StrictConvexPos c := ⟨parabola n, scp_parabola n⟩

/-- The affine map `triMap` is continuous. -/
lemma continuous_triMap (a b c a' b' c' : ℝ × ℝ) : Continuous (triMap a b c a' b' c') := by
  unfold triMap tmB tmC cross
  fun_prop

/-- Source triangles are compact. -/
lemma Tri.isCompact_src (t : Tri) : IsCompact t.src := by
  unfold Tri.src
  exact Set.Finite.isCompact_convexHull (𝕜 := ℝ) (Set.toFinite _)

/-- A map that is affine on each triangle of a finite list is continuous on the union. -/
lemma continuousOn_biUnion_src (f : ℝ × ℝ → ℝ × ℝ) :
    ∀ L : List Tri, (∀ t ∈ L, t.Good f) → ContinuousOn f (⋃ t ∈ L, t.src)
  | [], _ => by simp [continuousOn_empty]
  | t :: L, h => by
    have ht : ContinuousOn f t.src :=
      ((continuous_triMap t.a t.b t.c t.a' t.b' t.c').continuousOn).congr (h t (by simp)).2.2
    have hL := continuousOn_biUnion_src f L (fun s hs => h s (List.mem_cons_of_mem _ hs))
    have hcl : IsClosed (⋃ s ∈ L, s.src) :=
      (List.finite_toSet L).isClosed_biUnion (fun s _ => (Tri.isCompact_src s).isClosed)
    have := ht.union_of_isClosed hL (Tri.isCompact_src t).isClosed hcl
    simpa [List.mem_cons, iUnion_or, iUnion_union_distrib, or_comm] using this

/-- A piecewise affine map is continuous on its region. -/
lemma PiecewiseTri.continuousOn {f : ℝ × ℝ → ℝ × ℝ} {R : Set (ℝ × ℝ)} (h : PiecewiseTri f R) :
    ContinuousOn f R := by
  obtain ⟨L, hL, rfl⟩ := h
  exact continuousOn_biUnion_src f L hL

/-- The region of a piecewise affine map is compact. -/
lemma PiecewiseTri.isCompact {f : ℝ × ℝ → ℝ × ℝ} {R : Set (ℝ × ℝ)} (h : PiecewiseTri f R) :
    IsCompact R := by
  obtain ⟨L, hL, rfl⟩ := h
  exact (List.finite_toSet L).isCompact_biUnion (fun s _ => Tri.isCompact_src s)

/-- A piecewise affine bijection from a region onto a set `T` is a homeomorphism of the subtypes
(the region is compact, the target is Hausdorff). -/
noncomputable def PiecewiseTri.homeo {f : ℝ × ℝ → ℝ × ℝ} {R T : Set (ℝ × ℝ)}
    (h : PiecewiseTri f R) (hb : BijOn f R T) : R ≃ₜ T :=
  haveI : CompactSpace R := isCompact_iff_compactSpace.mp h.isCompact
  Continuous.homeoOfEquivCompactToT2 (f := hb.equiv f)
    ((continuousOn_iff_continuous_domRestrict.mp (PiecewiseTri.continuousOn h)).subtype_mk
      (fun x => hb.mapsTo x.2))

/-- The homeomorphism of `PiecewiseTri.homeo` is `f`. -/
lemma PiecewiseTri.homeo_apply {f : ℝ × ℝ → ℝ × ℝ} {R T : Set (ℝ × ℝ)}
    (h : PiecewiseTri f R) (hb : BijOn f R T) (x : R) : ((h.homeo hb x : T) : ℝ × ℝ) = f x := rfl

/-- **Polygonal Schoenflies theorem, homeomorphism form.**  For a simple polygon `p` with `n ≥ 3`
vertices there are a polygon `c` in strictly convex position and a homeomorphism of the closed region
of `p` onto the convex hull of `c` that is piecewise affine, sends `p i` to `c i`, and carries the
carrier of `p` onto the frontier of the hull. -/
theorem polygonal_schoenflies_homeo {n : ℕ} [NeZero n] {p : Polygon n} (h3 : 3 ≤ n)
    (hs : p.IsSimple) :
    ∃ (c : Polygon n) (e : region p ≃ₜ convexHull ℝ (range c)) (f : ℝ × ℝ → ℝ × ℝ),
      StrictConvexPos c ∧ PiecewiseTri f (region p) ∧ (∀ x, (e x : ℝ × ℝ) = f x) ∧
      (∀ i, f (p i) = c i) ∧ f '' p.carrier = frontier (convexHull ℝ (range c)) := by
  obtain ⟨c, hc⟩ := exists_scp n
  obtain ⟨f, hb, hv, -, hpw, hcar, -⟩ := polygonal_schoenflies h3 hs hc
  exact ⟨c, hpw.homeo hb, f, hc, hpw, fun x => rfl, hv, hcar⟩

end Lightlike.PL.Schoenflies
