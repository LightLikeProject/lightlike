import Lightlike.PL.Schoenflies.InsideBox

/-!
# The boundary polygon lies in the closed inflated squares

Row G3-188, milestone PL5 (third pass), item 5b, route A.  Every boundary edge of `sqSet F` is an edge of a
unit square of `sqSet F`, hence lies in the closed inflated square of some `q ∈ F`.

* `closedBoxU q`: the closed inflated grid square, in units of `δ / 4`.
* `bdEdge_mem_closedBox`: a point of a boundary edge lies in some `closedBoxU q`, `q ∈ F`.
* `carrier_subset_closedBox`: the carrier of the boundary polygon lies in `⋃ q ∈ F, closedBoxU q`.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL

/-- The closed inflated grid square `q`, in units of `δ / 4`. -/
def closedBoxU (q : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {z | 4 * (q.1 : ℝ) - 1 ≤ z.1 ∧ z.1 ≤ 4 * q.1 + 5 ∧ 4 * (q.2 : ℝ) - 1 ≤ z.2 ∧ z.2 ≤ 4 * q.2 + 5}

lemma openBoxU_subset_closedBoxU (q : ℤ × ℤ) : openBoxU q ⊆ closedBoxU q :=
  fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1.le, h2.le, h3.le, h4.le⟩

/-- **A point of a boundary edge of `sqSet F` lies in a closed inflated square of `F`.** -/
theorem bdEdge_mem_closedBox {F : Finset (ℤ × ℤ)} {a b : ℤ × ℤ} (hab : BdAdj (sqSet F) a b)
    {z : ℝ × ℝ} (hz : z ∈ segment ℝ (pt a) (pt b)) : ∃ q ∈ F, z ∈ closedBoxU q := by
  obtain ⟨x, y, ⟨he, hy, hx1, hx2⟩ | ⟨he, hx, hy1, hy2⟩⟩ := seg_unit hab.unitStep hz
  · have hB := bdAdj_horiz hab he
    unfold HB at hB
    obtain ⟨s, hs, hsy⟩ : ∃ s ∈ sqSet F, s = (x, y) ∨ s = (x, y - 1) := by
      rcases hB with ⟨h, -⟩ | ⟨h, -⟩
      · exact ⟨_, h, Or.inl rfl⟩
      · exact ⟨_, h, Or.inr rfl⟩
    obtain ⟨q, hq, hsq⟩ := mem_sqSet.1 hs
    obtain ⟨a1, a2, a3, a4⟩ := mem_boxSq.1 hsq
    refine ⟨q, hq, ?_⟩
    have b1 : (4 * q.1 - 1 : ℝ) ≤ s.1 := by exact_mod_cast a1
    have b2 : (s.1 : ℝ) ≤ 4 * q.1 + 4 := by exact_mod_cast a2
    have b3 : (4 * q.2 - 1 : ℝ) ≤ s.2 := by exact_mod_cast a3
    have b4 : (s.2 : ℝ) ≤ 4 * q.2 + 4 := by exact_mod_cast a4
    rcases hsy with rfl | rfl
    · simp only at b1 b2 b3 b4
      exact ⟨by linarith, by linarith, by rw [hy]; linarith, by rw [hy]; linarith⟩
    · simp only at b1 b2 b3 b4
      push_cast at b3 b4
      exact ⟨by linarith, by linarith, by rw [hy]; linarith, by rw [hy]; linarith⟩
  · have hB := bdAdj_vert hab he
    unfold VB at hB
    obtain ⟨s, hs, hsy⟩ : ∃ s ∈ sqSet F, s = (x, y) ∨ s = (x - 1, y) := by
      rcases hB with ⟨h, -⟩ | ⟨h, -⟩
      · exact ⟨_, h, Or.inl rfl⟩
      · exact ⟨_, h, Or.inr rfl⟩
    obtain ⟨q, hq, hsq⟩ := mem_sqSet.1 hs
    obtain ⟨a1, a2, a3, a4⟩ := mem_boxSq.1 hsq
    refine ⟨q, hq, ?_⟩
    have b1 : (4 * q.1 - 1 : ℝ) ≤ s.1 := by exact_mod_cast a1
    have b2 : (s.1 : ℝ) ≤ 4 * q.1 + 4 := by exact_mod_cast a2
    have b3 : (4 * q.2 - 1 : ℝ) ≤ s.2 := by exact_mod_cast a3
    have b4 : (s.2 : ℝ) ≤ 4 * q.2 + 4 := by exact_mod_cast a4
    rcases hsy with rfl | rfl
    · simp only at b1 b2 b3 b4
      exact ⟨by rw [hx]; linarith, by rw [hx]; linarith, by linarith, by linarith⟩
    · simp only at b1 b2 b3 b4
      push_cast at b1 b2
      exact ⟨by rw [hx]; linarith, by rw [hx]; linarith, by linarith, by linarith⟩

/-- **The carrier of the boundary polygon lies in the closed inflated squares of `F`.** -/
theorem carrier_subset_closedBox {F : Finset (ℤ × ℤ)} {n : ℕ} {v : Fin n → ℤ × ℤ}
    (hadj : ∀ i, BdAdj (sqSet F) (v i) (v (finRotate n i))) :
    (latticePoly v).carrier ⊆ ⋃ q ∈ F, closedBoxU q := by
  intro z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
  obtain ⟨q, hq, hzq⟩ := bdEdge_mem_closedBox (hadj i) hi
  exact Set.mem_iUnion₂.2 ⟨q, hq, hzq⟩

end Lightlike.PL.Schoenflies
