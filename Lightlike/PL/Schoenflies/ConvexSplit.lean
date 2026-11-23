import Mathlib
import Lightlike.PL.PolygonSplit
import Lightlike.PL.Schoenflies.EarCut

/-!
# The convex side of the ear induction

Piece 10 of the polygonal Schoenflies theorem (row G3-188, milestone PL5).  A list of points
`c : Fin n → ℝ × ℝ` is in *strictly convex position* (counterclockwise) when every triple of indices
`i < j < k` is positively oriented.  Clipping the ear at vertex `1` (the clipped list is
`c.right 2`, with vertices `c 0, c 2, c 3, …`) keeps strictly convex position, and the convex hull
splits as the hull of the clipped list plus the triangle `c 0, c 1, c 2`, meeting in the segment
`[c 0, c 2]`.
-/

namespace Lightlike.PL.Schoenflies

open Set

/-- `c` is in strictly convex position, counterclockwise: all triples `i < j < k` are positively
oriented. -/
def StrictConvexPos {n : ℕ} (c : Fin n → ℝ × ℝ) : Prop :=
  ∀ i j k : Fin n, i < j → j < k → 0 < det3 (c i) (c j) (c k)

lemma det3_self_right (a b : ℝ × ℝ) : det3 a b b = 0 := by
  simp only [det3, cross, Prod.fst_sub, Prod.snd_sub]; ring

lemma det3_self_left_right (a b : ℝ × ℝ) : det3 a b a = 0 := by
  simp only [det3, cross, Prod.fst_sub, Prod.snd_sub]; ring

/-- Strict convex position, read with cyclic indices (the index `n` is the index `0`). -/
lemma scp_cyc {n : ℕ} [NeZero n] {c : Polygon n} (hc : StrictConvexPos c) {i j k : ℕ}
    (hij : i < j) (hjk : j < k) (hk : k ≤ n) (h : k < n ∨ 0 < i) :
    0 < det3 (c.cyc i) (c.cyc j) (c.cyc k) := by
  by_cases hkn : k < n
  · rw [c.cyc_of_lt (show i < n by omega), c.cyc_of_lt (show j < n by omega), c.cyc_of_lt hkn]
    exact hc _ _ _ (Fin.mk_lt_mk.2 hij) (Fin.mk_lt_mk.2 hjk)
  · have hkn' : k = n := by omega
    have hi : 0 < i := by omega
    have e : c.cyc k = c.cyc 0 := by
      have := Polygon.cyc_self_add (p := c) 0
      rw [hkn']; simpa using this
    rw [e, c.cyc_of_lt (show i < n by omega), c.cyc_of_lt (show j < n by omega),
      show c.cyc 0 = c ⟨0, by omega⟩ from c.cyc_of_lt (by omega), det3_cyc]
    exact hc _ _ _ (Fin.mk_lt_mk.2 hi) (Fin.mk_lt_mk.2 hij)

/-- Clipping the ear at vertex `1` keeps strictly convex position. -/
lemma scp_right {n : ℕ} [NeZero n] {c : Polygon n} (hc : StrictConvexPos c) :
    StrictConvexPos (c.right 2) := by
  intro i j k hij hjk
  have hij' : (i : ℕ) < j := hij
  have hjk' : (j : ℕ) < k := hjk
  have hk := k.2
  exact scp_cyc hc (i := 2 + i) (j := 2 + j) (k := 2 + k) (by omega) (by omega) (by omega)
    (Or.inr (by omega))

/-- Every vertex of `c` other than the vertex `1` is a vertex of the clipped list, and conversely. -/
lemma insert_range_right {n : ℕ} [NeZero n] (c : Polygon n) (hn : 2 ≤ n) :
    insert (c.cyc 1) (range (c.right 2)) = range c := by
  ext x
  constructor
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨⟨1, by omega⟩, (c.cyc_of_lt (show 1 < n by omega)).symm⟩
    · by_cases hj : (2 + (j : ℕ)) < n
      · exact ⟨⟨2 + j, hj⟩, (c.cyc_of_lt hj).symm⟩
      · have : 2 + (j : ℕ) = n + 0 := by have := j.2; omega
        refine ⟨⟨0, by omega⟩, ?_⟩
        show c ⟨0, _⟩ = c.cyc (2 + j)
        rw [this, Polygon.cyc_self_add, c.cyc_of_lt (show 0 < n by omega)]
  · rintro ⟨i, rfl⟩
    by_cases h1 : (i : ℕ) = 1
    · left
      rw [c.cyc_of_lt (show 1 < n by omega)]
      congr 1; ext; simp [h1]
    · right
      by_cases h0 : (i : ℕ) = 0
      · refine ⟨⟨n - 2, by omega⟩, ?_⟩
        show c.cyc (2 + (n - 2)) = c i
        have : 2 + (n - 2) = n + 0 := by omega
        rw [this, Polygon.cyc_self_add, c.cyc_of_lt (show 0 < n by omega)]
        congr 1; ext; simp [h0]
      · refine ⟨⟨i - 2, by have := i.2; omega⟩, ?_⟩
        show c.cyc (2 + (i - 2)) = c i
        have : 2 + ((i : ℕ) - 2) = i := by omega
        rw [this, c.cyc_of_lt i.2]

/-- **Clipping an ear off a convex polygon.**  If `c` is in strictly convex position with at least
`3` vertices, the convex hull of its vertices is the hull of the clipped list `c.right 2` together
with the triangle on `c 0, c 1, c 2`, and the two meet exactly in the segment `[c 0, c 2]`. -/
theorem hull_range_ear_split {n : ℕ} [NeZero n] {c : Polygon n} (hc : StrictConvexPos c)
    (h3 : 3 ≤ n) :
    convexHull ℝ (range c) = convexHull ℝ (range (c.right 2)) ∪
        convexHull ℝ {c.cyc 0, c.cyc 1, c.cyc 2} ∧
      convexHull ℝ (range (c.right 2)) ∩ convexHull ℝ {c.cyc 0, c.cyc 1, c.cyc 2} =
        segment ℝ (c.cyc 0) (c.cyc 2) := by
  have e0 : c.cyc 0 = c.cyc (2 + (n - 2)) := by
    have : 2 + (n - 2) = n + 0 := by omega
    rw [this, Polygon.cyc_self_add]
  have h0 : c.cyc 0 ∈ range (c.right 2) := ⟨⟨n - 2, by omega⟩, e0.symm⟩
  have h2 : c.cyc 2 ∈ range (c.right 2) := ⟨0, by simp [Polygon.right]⟩
  have hD : 0 < det3 (c.cyc 0) (c.cyc 1) (c.cyc 2) :=
    scp_cyc hc (by omega) (by omega) (by omega) (Or.inl (by omega))
  have key : ∀ (P : ℝ × ℝ → Prop), (∀ m : ℕ, 2 ≤ m → m ≤ n → P (c.cyc m)) →
      ∀ u ∈ range (c.right 2), P u := by
    intro P hP u hu
    obtain ⟨j, rfl⟩ := hu
    exact hP (2 + j) (by omega) (by have := j.2; omega)
  have hgeom := hull_ear_geom (S := range (c.right 2)) (p0 := c.cyc 0) (p1 := c.cyc 1)
    (p2 := c.cyc 2) h0 h2 hD
    (key (fun u => 0 ≤ det3 (c.cyc 0) (c.cyc 2) u) (fun m hm hmn => by
      by_cases h2m : m = 2
      · subst h2m; rw [det3_self_right]
      · by_cases hmn' : m < n
        · exact (scp_cyc hc (by omega) (by omega) (by omega) (Or.inl hmn')).le
        · have : m = n + 0 := by omega
          rw [this, Polygon.cyc_self_add, det3_self_left_right]))
    (key (fun u => 0 ≤ det3 (c.cyc 0) (c.cyc 1) u) (fun m hm hmn => by
      by_cases hmn' : m < n
      · exact (scp_cyc hc (by omega) (by omega) (by omega) (Or.inl hmn')).le
      · have : m = n + 0 := by omega
        rw [this, Polygon.cyc_self_add, det3_self_left_right]))
    (key (fun u => 0 ≤ det3 (c.cyc 1) (c.cyc 2) u) (fun m hm hmn => by
      by_cases h2m : m = 2
      · subst h2m; rw [det3_self_right]
      · exact (scp_cyc hc (by omega) (by omega) hmn (Or.inr (by omega))).le))
  rw [insert_range_right c (by omega)] at hgeom
  exact hgeom

/-- Non-vacuity: the unit square `(0,0),(1,0),(1,1),(0,1)` is in strictly convex position. -/
example : StrictConvexPos (![(0, 0), (1, 0), (1, 1), (0, 1)] : Fin 4 → ℝ × ℝ) := by
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [det3, cross]

/-- Wrong input gives a different answer: a clockwise triple is not strictly convex. -/
example : ¬ StrictConvexPos (![(0, 0), (0, 1), (1, 0)] : Fin 3 → ℝ × ℝ) := by
  intro h
  have := h 0 1 2 (by decide) (by decide)
  norm_num [det3, cross] at this

end Lightlike.PL.Schoenflies
