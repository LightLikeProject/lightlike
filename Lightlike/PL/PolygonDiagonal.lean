import Lightlike.PL.PolygonInside

/-!
# The extreme vertex of a simple polygon

The first step towards a diagonal in the inside of a simple polygon: the vertex that is smallest
for the lexicographic order (leftmost, ties broken by lowest) is a corner of the convex hull, and
its two edges are not collinear.

## Main results

* `Lightlike.PL.Polygon.exists_extreme`: a vertex lexicographically below all vertices
* `Lightlike.PL.Polygon.corner_cross_ne`: at such a vertex the two edges are not parallel
-/

open Set

namespace Lightlike.PL
namespace Polygon

variable {n : ℕ} {p : Polygon n}

/-- `a` is **lexicographically positive**: to the right of the vertical line through the origin,
or on it and above the origin. -/
def LexPos (a : ℝ × ℝ) : Prop := 0 < a.1 ∨ (a.1 = 0 ∧ 0 < a.2)

/-- The point `x` is lexicographically at most `y`. -/
def LexLE (x y : ℝ × ℝ) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)

/-- The lexicographic order is total. -/
lemma lexLE_total (x y : ℝ × ℝ) : LexLE x y ∨ LexLE y x := by
  unfold LexLE
  rcases lt_trichotomy x.1 y.1 with h | h | h
  · exact .inl (.inl h)
  · rcases le_total x.2 y.2 with h2 | h2
    · exact .inl (.inr ⟨h, h2⟩)
    · exact .inr (.inr ⟨h.symm, h2⟩)
  · exact .inr (.inl h)

lemma lexLE_trans {x y z : ℝ × ℝ} (h1 : LexLE x y) (h2 : LexLE y z) : LexLE x z := by
  unfold LexLE at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact .inl (h1.trans h2)
  · exact .inl (h2 ▸ h1)
  · exact .inl (h1 ▸ h2)
  · exact .inr ⟨h1.trans h2, h1'.trans h2'⟩

/-- **A polygon has a lexicographically smallest vertex.** -/
theorem exists_extreme [NeZero n] (p : Polygon n) : ∃ j, ∀ i, LexLE (p j) (p i) := by
  classical
  have key : ∀ (s : Finset (Fin n)), s.Nonempty → ∃ j ∈ s, ∀ i ∈ s, LexLE (p j) (p i) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => exact absurd hs (by simp)
    | insert a s ha ih =>
      rcases s.eq_empty_or_nonempty with rfl | hne
      · exact ⟨a, by simp, fun i hi => by
          obtain rfl : i = a := by simpa using hi
          exact .inr ⟨rfl, le_rfl⟩⟩
      · obtain ⟨j, hj, hjmin⟩ := ih hne
        rcases lexLE_total (p a) (p j) with h | h
        · refine ⟨a, by simp, fun i hi => ?_⟩
          rcases Finset.mem_insert.1 hi with rfl | hi
          · exact .inr ⟨rfl, le_rfl⟩
          · exact lexLE_trans h (hjmin i hi)
        · refine ⟨j, Finset.mem_insert_of_mem hj, fun i hi => ?_⟩
          rcases Finset.mem_insert.1 hi with rfl | hi
          · exact h
          · exact hjmin i hi
  obtain ⟨j, -, hj⟩ := key Finset.univ ⟨⟨0, NeZero.pos n⟩, Finset.mem_univ _⟩
  exact ⟨j, fun i => hj i (Finset.mem_univ i)⟩

/-- Two nonzero lexicographically positive vectors with vanishing cross product are positive
multiples of each other. -/
lemma exists_pos_smul {a b : ℝ × ℝ} (ha : LexPos a) (hb : LexPos b)
    (hc : a.1 * b.2 - a.2 * b.1 = 0) : ∃ c : ℝ, 0 < c ∧ b = c • a := by
  rcases ha with ha | ⟨ha1, ha2⟩
  · have hb1 : 0 < b.1 := by
      rcases hb with hb | ⟨hb1, hb2⟩
      · exact hb
      · exfalso
        rw [hb1] at hc
        nlinarith
    refine ⟨b.1 / a.1, div_pos hb1 ha, ?_⟩
    ext
    · simp only [Prod.smul_fst, smul_eq_mul]; field_simp
    · simp only [Prod.smul_snd, smul_eq_mul]
      field_simp
      linarith
  · have hb1 : b.1 = 0 := by
      rw [ha1] at hc
      nlinarith
    have hb2 : 0 < b.2 := by
      rcases hb with hb | ⟨-, hb2⟩
      · linarith
      · exact hb2
    refine ⟨b.2 / a.2, div_pos hb2 ha2, ?_⟩
    ext
    · simp only [Prod.smul_fst, smul_eq_mul, hb1, ha1]; simp
    · simp only [Prod.smul_snd, smul_eq_mul]; field_simp

/-- A point at parameter `c ∈ [0,1]` from `v` towards `u` lies on the segment. -/
lemma mem_segment_of_sub_eq {v u z : ℝ × ℝ} {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1)
    (hz : z - v = c • (u - v)) : z ∈ segment ℝ v u := by
  have hz' : z = (1 - c) • v + c • u := by
    have : z = v + c • (u - v) := by rw [← hz]; abel
    rw [this]; ext <;> simp <;> ring
  exact ⟨1 - c, c, by linarith, h0, by ring, hz'.symm⟩

/-- **The corner at the extreme vertex is not degenerate.** At a lexicographically smallest vertex
`p j` of a simple polygon, the edge vectors to the neighbouring vertices are not parallel. -/
theorem corner_cross_ne (hs : p.IsSimple) {j : Fin n} (hext : ∀ i, LexLE (p j) (p i)) :
    ((p ((finRotate n).symm j)).1 - (p j).1) * ((p (finRotate n j)).2 - (p j).2) -
      ((p ((finRotate n).symm j)).2 - (p j).2) * ((p (finRotate n j)).1 - (p j).1) ≠ 0 := by
  intro hc
  set k := (finRotate n).symm j with hk
  have hkj : finRotate n k = j := by rw [hk]; exact Equiv.apply_symm_apply _ _
  set v := p j with hv
  set u := p k with hu
  set w := p (finRotate n j) with hw
  have huv : u ≠ v := by have := hs.1 k; rwa [hkj] at this
  have hvw : v ≠ w := hs.1 j
  have hpos : ∀ z : ℝ × ℝ, LexLE v z → z ≠ v → LexPos (z - v) := by
    intro z hz hne
    unfold LexLE at hz
    unfold LexPos
    rcases hz with h | ⟨h1, h2⟩
    · left; simp only [Prod.fst_sub]; linarith
    · right
      refine ⟨by simp only [Prod.fst_sub]; linarith, ?_⟩
      simp only [Prod.snd_sub]
      rcases h2.lt_or_eq with h2 | h2
      · linarith
      · exact absurd (Prod.ext h1.symm h2.symm) hne
  obtain ⟨c, hc0, hbc⟩ := exists_pos_smul (hpos u (hext k) huv) (hpos w (hext _) hvw.symm) hc
  have hinter := hs.2.2 k
  rw [hkj] at hinter
  have e1 : p.edge k = segment ℝ u v := by simp only [edge, hkj, hu, hv]
  have e2 : p.edge j = segment ℝ v w := rfl
  rw [e1, e2] at hinter
  rcases le_or_gt c 1 with h1 | h1
  · have hwm : w ∈ segment ℝ v u := mem_segment_of_sub_eq hc0.le h1 hbc
    have : w ∈ segment ℝ u v ∩ segment ℝ v w :=
      ⟨by rwa [segment_symm], right_mem_segment ℝ v w⟩
    rw [hinter] at this
    exact hvw (Set.mem_singleton_iff.1 this).symm
  · have hum : u ∈ segment ℝ v w := by
      refine mem_segment_of_sub_eq (inv_nonneg.2 hc0.le) (inv_le_one_of_one_le₀ h1.le) ?_
      rw [hbc, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
    have : u ∈ segment ℝ u v ∩ segment ℝ v w := ⟨left_mem_segment ℝ u v, hum⟩
    rw [hinter] at this
    exact huv (Set.mem_singleton_iff.1 this)

end Polygon
end Lightlike.PL
