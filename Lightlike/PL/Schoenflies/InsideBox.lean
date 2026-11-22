import Lightlike.PL.Schoenflies.LeftmostInside

/-!
# An open inflated square of the leftmost component lies inside the boundary polygon

Row G3-188, milestone PL5 (third pass), item 5b, route A, step R4b.  For a nonempty finite family `F`
of grid squares there is a simple boundary polygon `latticePoly v` (all edges boundary edges of `sqSet F`)
and a square `q0 ∈ F` whose whole open inflated square lies off the polygon with parity `1` (inside).

* `openBoxU_eq`: the open inflated square is a product of open intervals, hence convex.
* `exists_leftmost`: a nonempty finite set of unit squares has a square of minimal first coordinate.
* `exists_polygon_inside_box`: the polygon and the square `q0`.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL

/-- The open inflated square is a product of open intervals. -/
lemma openBoxU_eq (q : ℤ × ℤ) :
    openBoxU q = Ioo (4 * (q.1 : ℝ) - 1) (4 * q.1 + 5) ×ˢ Ioo (4 * (q.2 : ℝ) - 1) (4 * q.2 + 5) := by
  ext z
  simp only [openBoxU, mem_ofPred_eq, mem_prod, mem_Ioo]
  tauto

lemma convex_openBoxU (q : ℤ × ℤ) : Convex ℝ (openBoxU q) := by
  rw [openBoxU_eq]; exact (convex_Ioo _ _).prod (convex_Ioo _ _)

/-- A nonempty finite set of unit squares has a square of minimal first coordinate. -/
lemma exists_leftmost {S : Set (ℤ × ℤ)} (hf : S.Finite) (hne : S.Nonempty) :
    ∃ s ∈ S, ∀ t ∈ S, s.1 ≤ t.1 := by
  obtain ⟨s, hs, h⟩ := Set.exists_min_image S Prod.fst hf hne
  exact ⟨s, hs, h⟩

/-- **The boundary polygon of a nonempty family contains one whole open inflated square.** -/
theorem exists_polygon_inside_box (F : Finset (ℤ × ℤ)) (hF : F.Nonempty) :
    ∃ (n : ℕ) (v : Fin n → ℤ × ℤ), 3 ≤ n ∧ Function.Injective v ∧
      (∀ i, BdAdj (sqSet F) (v i) (v (finRotate n i))) ∧ (latticePoly v).IsSimple ∧
      ∃ q0 ∈ F, ∀ z ∈ openBoxU q0, z ∉ (latticePoly v).carrier ∧ (latticePoly v).parity z = 1 := by
  obtain ⟨q1, hq1⟩ := hF
  have hne : (sqSet F).Nonempty :=
    ⟨(4 * q1.1, 4 * q1.2), mem_sqSet.2 ⟨q1, hq1, mem_boxSq.2 ⟨by omega, by omega, by omega, by omega⟩⟩⟩
  obtain ⟨s, hs, hmin⟩ := exists_leftmost (sqSet_finite F) hne
  have hVB : VB (sqSet F) s.1 s.2 := by
    left
    refine ⟨hs, fun h => ?_⟩
    have := hmin _ h
    simp only at this
    omega
  have hab : (bdGraph (sqSet F)).Adj (s.1, s.2) (s.1, s.2 + 1) := by
    show BdAdj (sqSet F) _ _
    rw [bdAdj_iff]
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hVB⟩))
  obtain ⟨n, v, hn, hv, hadj, hsimp, i, hi⟩ := exists_boundary_polygon F hab
  refine ⟨n, v, hn, hv, hadj, hsimp, ?_⟩
  have hedge : ∃ i, ({v i, v (finRotate n i)} : Set (ℤ × ℤ)) = {(s.1, s.2), (s.1, s.2 + 1)} := by
    refine ⟨i, ?_⟩
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Set.pair_comm]
  obtain ⟨hnot, hpar⟩ := parity_leftmost hadj hsimp hmin hedge
  obtain ⟨q0, hq0, hsq⟩ := mem_sqSet.1 hs
  refine ⟨q0, hq0, fun z hz => ?_⟩
  have hdis := carrier_not_mem_openBox hadj hq0
  have hz' : z ∉ (latticePoly v).carrier := fun h => Set.disjoint_left.1 hdis h hz
  refine ⟨hz', ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := mem_boxSq.1 hsq
  have hc : ((s.1 : ℝ) + 1 / 2, (s.2 : ℝ) + 1 / 2) ∈ openBoxU q0 := by
    have b1 : (4 * q0.1 - 1 : ℝ) ≤ s.1 := by exact_mod_cast a1
    have b2 : (s.1 : ℝ) ≤ 4 * q0.1 + 4 := by exact_mod_cast a2
    have b3 : (4 * q0.2 - 1 : ℝ) ≤ s.2 := by exact_mod_cast a3
    have b4 : (s.2 : ℝ) ≤ 4 * q0.2 + 4 := by exact_mod_cast a4
    exact ⟨by simp only; linarith, by simp only; linarith, by simp only; linarith,
      by simp only; linarith⟩
  have hpre : IsPreconnected (openBoxU q0) := (convex_openBoxU q0).isPreconnected
  have hsub : openBoxU q0 ⊆ (latticePoly v).carrierᶜ := fun w hw h =>
    Set.disjoint_left.1 hdis h hw
  rw [constOn_of_isPreconnected (Polygon.isClosed_carrier _)
    (fun x hx => Polygon.eventually_parity_eq _ hx) hpre hsub hz hc]
  exact hpar

end Lightlike.PL.Schoenflies
