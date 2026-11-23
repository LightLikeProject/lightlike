import Mathlib
import Lightlike.PL.PolygonBall
import Lightlike.PL.PolygonTriangle
import Lightlike.PL.PolygonSplit

/-!
# The region of a polygon with an ear clipped

Piece 9 of the polygonal Schoenflies theorem (row G3-188, milestone PL5).  Polygon side of the ear
induction: if a simple polygon `q` has an ear at the vertex `0` (the open diagonal from vertex `0`
to vertex `2` lies inside), then the closed region of `q` (inside together with the carrier) is the
union of the closed region of the clipped polygon `q.right 2` and the triangle on the vertices
`0, 1, 2`, and these two meet exactly in the diagonal.
-/

namespace Lightlike.PL.Schoenflies

open Set

/-- The closed region bounded by a polygon: its inside together with its carrier. -/
def region {n : ℕ} (p : Polygon n) : Set (ℝ × ℝ) := p.inside ∪ p.carrier

/-- The closed region of a simple triangle is the convex hull of its vertices. -/
lemma region_triangle {p : Polygon 3} (hs : p.IsSimple) :
    region p = convexHull ℝ (range p) := by
  unfold region
  rw [Polygon.inside_eq_interior_hull hs, Polygon.carrier_eq_frontier_hull hs,
    ← closure_eq_interior_union_frontier]
  exact (Set.Finite.isCompact_convexHull (𝕜 := ℝ) (Set.finite_range p)).isClosed.closure_eq

/-- **Clipping an ear off the region.**  For a simple polygon with an ear at `0`, the region is the
region of the clipped polygon `q.right 2` together with the triangle on the vertices `0, 1, 2`, and
the two pieces meet exactly in the closed diagonal from vertex `0` to vertex `2`. -/
theorem region_ear_split {n : ℕ} [NeZero n] {q : Polygon n} (hs : q.IsSimple) (h4 : 4 ≤ n)
    (hear : q.Ear 0) :
    region q = region (q.right 2) ∪ convexHull ℝ {q.cyc 0, q.cyc 1, q.cyc 2} ∧
      region (q.right 2) ∩ convexHull ℝ {q.cyc 0, q.cyc 1, q.cyc 2} =
        segment ℝ (q.cyc 0) (q.cyc 2) := by
  have hn2 : 2 ≤ n := by omega
  have hD : openSegment ℝ (q.cyc 0) (q.cyc 2) ⊆ q.inside := by
    simpa [Polygon.Ear] using hear
  have hopen : ∀ x ∈ openSegment ℝ (q.cyc 0) (q.cyc 2), x ∉ q.carrier := fun x hx hxc =>
    (hD hx).1 hxc
  obtain ⟨hdis, hspl⟩ := Polygon.inside_split hs (b := 2) le_rfl (by omega) hD
  have hsR := Polygon.isSimple_right hs (b := 2) le_rfl (by omega) hopen
  have hsL := Polygon.isSimple_left hs (b := 2) le_rfl (by omega) hopen
  have hrange : range (q.left 2) = {q.cyc 0, q.cyc 1, q.cyc 2} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [Polygon.left]
    · intro hx
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hLreg : region (q.left 2) = convexHull ℝ {q.cyc 0, q.cyc 1, q.cyc 2} := by
    rw [← hrange]; exact region_triangle hsL
  rw [← hLreg]
  have hcar := fun x => Polygon.mem_carrier_left_or_right (p := q) hn2 (b := 2) (by omega)
    (by omega) (x := x)
  have hdiagL : segment ℝ (q.cyc 0) (q.cyc 2) ⊆ (q.left 2).carrier := by
    intro x hx
    rw [Polygon.mem_carrier_left_iff (by omega)]
    exact Or.inr (by rwa [segment_symm])
  have hdiagR : segment ℝ (q.cyc 0) (q.cyc 2) ⊆ (q.right 2).carrier := by
    intro x hx
    rw [Polygon.mem_carrier_right_iff (by omega)]
    exact Or.inr hx
  have hLc : ∀ x, x ∈ (q.left 2).carrier → x ∈ q.carrier ∨ x ∈ segment ℝ (q.cyc 0) (q.cyc 2) :=
    fun x hx => (hcar x).1 (Or.inl hx)
  have hRc : ∀ x, x ∈ (q.right 2).carrier → x ∈ q.carrier ∨ x ∈ segment ℝ (q.cyc 0) (q.cyc 2) :=
    fun x hx => (hcar x).1 (Or.inr hx)
  have hLi : (q.left 2).inside ⊆ q.inside := by
    rw [hspl]; exact Set.subset_union_left.trans Set.subset_union_left
  have hRi : (q.right 2).inside ⊆ q.inside := by
    rw [hspl]; exact Set.subset_union_right.trans Set.subset_union_left
  have hqc : ∀ x, x ∈ q.inside → x ∉ q.carrier := fun x hx => hx.1
  -- the closed diagonal lies in the region of `q`
  have hseg : segment ℝ (q.cyc 0) (q.cyc 2) ⊆ region q := by
    intro x hx
    rw [← insert_endpoints_openSegment] at hx
    rcases hx with rfl | rfl | hx
    · exact Or.inr (Polygon.cyc_mem_carrier hn2 (by omega))
    · exact Or.inr (Polygon.cyc_mem_carrier hn2 (by omega))
    · exact Or.inl (hD hx)
  constructor
  · apply Subset.antisymm
    · rintro x (hx | hx)
      · rw [hspl] at hx
        rcases hx with (hx | hx) | hx
        · exact Or.inr (Or.inl hx)
        · exact Or.inl (Or.inl hx)
        · exact Or.inr (Or.inr (hdiagL (openSegment_subset_segment ℝ _ _ hx)))
      · rcases (hcar x).2 (Or.inl hx) with h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inl (Or.inr h)
    · rintro x ((hx | hx) | (hx | hx))
      · exact Or.inl (hRi hx)
      · rcases hRc x hx with h | h
        · exact Or.inr h
        · exact hseg h
      · exact Or.inl (hLi hx)
      · rcases hLc x hx with h | h
        · exact Or.inr h
        · exact hseg h
  · apply Subset.antisymm
    · rintro x ⟨hx1, hx2⟩
      rcases hx1 with hx1 | hx1 <;> rcases hx2 with hx2 | hx2
      · exact (Set.disjoint_left.1 hdis hx2 hx1).elim
      · rcases hLc x hx2 with h | h
        · exact absurd h (hqc x (hRi hx1))
        · exact h
      · rcases hRc x hx1 with h | h
        · exact absurd h (hqc x (hLi hx2))
        · exact h
      · exact Polygon.carrier_left_inter_right hs (b := 2) le_rfl (by omega) hx2 hx1
    · intro x hx
      exact ⟨Or.inr (hdiagR hx), Or.inr (hdiagL hx)⟩

end Lightlike.PL.Schoenflies
