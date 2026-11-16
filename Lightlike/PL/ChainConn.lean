import Lightlike.PL.SimpleChain

/-!
# A simple chain minus its endpoints is connected

For a simple polygonal chain the set of its points other than the two ends is preconnected: it is
a union of segments, each meeting the next, with the end points removed, which does not disconnect
a simple chain.

## Main results

* `Lightlike.PL.isPreconnected_chainSet_diff_ends`
-/

open Set

namespace Lightlike.PL

lemma isPreconnected_segment_diff_right {a b : ℝ × ℝ} (h : a ≠ b) :
    IsPreconnected (segment ℝ a b \ {b}) := by
  have : segment ℝ a b \ {b} = AffineMap.lineMap a b '' Set.Ico (0 : ℝ) 1 := by
    ext y
    rw [segment_eq_image_lineMap]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hy⟩
      refine ⟨t, ⟨ht.1, lt_of_le_of_ne ht.2 fun h1 => hy ?_⟩, rfl⟩
      rw [h1]; simp
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩, fun hy => ?_⟩
      have h2 : AffineMap.lineMap a b t = AffineMap.lineMap a b (1 : ℝ) := by simpa using hy
      exact ht.2.ne ((AffineMap.lineMap_injective ℝ h) h2)
  rw [this]
  exact isPreconnected_Ico.image _ (AffineMap.lineMap_continuous.continuousOn)

lemma isPreconnected_segment_diff_left {a b : ℝ × ℝ} (h : a ≠ b) :
    IsPreconnected (segment ℝ a b \ {a}) := by
  rw [segment_symm]; exact isPreconnected_segment_diff_right h.symm

lemma isPreconnected_segment_diff_ends {a b : ℝ × ℝ} (h : a ≠ b) :
    IsPreconnected (segment ℝ a b \ {a, b}) := by
  have : segment ℝ a b \ {a, b} = AffineMap.lineMap a b '' Set.Ioo (0 : ℝ) 1 := by
    ext y
    rw [segment_eq_image_lineMap]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hy⟩
      refine ⟨t, ⟨lt_of_le_of_ne ht.1 fun h0 => hy (Or.inl ?_),
        lt_of_le_of_ne ht.2 fun h1 => hy (Or.inr ?_)⟩, rfl⟩
      · rw [← h0]; simp
      · rw [h1]; simp
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩, fun hy => ?_⟩
      rcases hy with hy | hy
      · have h2 : AffineMap.lineMap a b t = AffineMap.lineMap a b (0 : ℝ) := by simpa using hy
        exact ht.1.ne ((AffineMap.lineMap_injective ℝ h) h2).symm
      · have h2 : AffineMap.lineMap a b t = AffineMap.lineMap a b (1 : ℝ) := by simpa using hy
        exact ht.2.ne ((AffineMap.lineMap_injective ℝ h) h2)
  rw [this]
  exact isPreconnected_Ioo.image _ (AffineMap.lineMap_continuous.continuousOn)

lemma head_notMem_tail {a b : ℝ × ℝ} {l : List (ℝ × ℝ)} (h : IsSimpleChain (a :: b :: l)) :
    a ∉ chainSet (b :: l) := by
  intro ha
  have : a ∈ segment ℝ a b ∩ chainSet (b :: l) := ⟨left_mem_segment ℝ a b, ha⟩
  rw [h.2.1] at this
  exact h.1 (by simpa using this)

lemma last_mem_chainSet : ∀ (c : List (ℝ × ℝ)) (hc : c ≠ []), c.getLast hc ∈ chainSet c
  | [], hc => absurd rfl hc
  | [x], _ => by simp [chainSet]
  | a :: b :: l, _ => by
    rw [List.getLast_cons (by simp)]
    exact Or.inr (last_mem_chainSet (b :: l) (by simp))

/-- The last point of a simple chain of at least two points differs from the first. -/
lemma getLast_ne_head {a b : ℝ × ℝ} {l : List (ℝ × ℝ)} (h : IsSimpleChain (a :: b :: l)) :
    (a :: b :: l).getLast (by simp) ≠ a := by
  intro he
  have hl : (a :: b :: l).getLast (by simp) ∈ chainSet (b :: l) := by
    rw [List.getLast_cons (by simp)]
    exact last_mem_chainSet _ _
  rw [he] at hl
  exact head_notMem_tail h hl

/-- A simple chain without its last point is preconnected. -/
theorem isPreconnected_chainSet_diff_last :
    ∀ (c : List (ℝ × ℝ)) (hc : c ≠ []), IsSimpleChain c →
      IsPreconnected (chainSet c \ {c.getLast hc})
  | [], hc, _ => absurd rfl hc
  | [x], _, _ => by simp [chainSet]; exact isPreconnected_empty
  | a :: b :: l, hc, hs => by
    by_cases hl : l = []
    · subst hl
      have : chainSet [a, b] \ {[a, b].getLast hc} = segment ℝ a b \ {b} := by
        rw [chainSet_pair]; simp
      rw [this]
      exact isPreconnected_segment_diff_right hs.1
    · set z := (b :: l).getLast (by simp) with hz
      have hzc : z ∈ chainSet (b :: l) := last_mem_chainSet _ _
      have hzb : z ≠ b := by
        obtain ⟨c', l', rfl⟩ := List.exists_cons_of_ne_nil hl
        exact getLast_ne_head hs.2.2
      have hzs : z ∉ segment ℝ a b := fun hzs => by
        have : z ∈ segment ℝ a b ∩ chainSet (b :: l) := ⟨hzs, hzc⟩
        rw [hs.2.1] at this
        exact hzb (by simpa using this)
      have e : chainSet (a :: b :: l) \ {(a :: b :: l).getLast hc} =
          segment ℝ a b ∪ (chainSet (b :: l) \ {z}) := by
        rw [List.getLast_cons (by simp)]
        ext y
        simp only [chainSet, mem_sdiff, mem_union, mem_singleton_iff]
        constructor
        · rintro ⟨h | h, hy⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, hy⟩
        · rintro (h | ⟨h, hy⟩)
          · exact ⟨Or.inl h, fun hyz => hzs (by have hyz' : y = z := hyz; rw [← hyz']; exact h)⟩
          · exact ⟨Or.inr h, hy⟩
      rw [e]
      refine IsPreconnected.union b (right_mem_segment ℝ a b) ⟨mem_chainSet_head b l, hzb.symm⟩
        (convex_segment a b).isPreconnected (isPreconnected_chainSet_diff_last (b :: l) (by simp) hs.2.2)

/-- **A simple chain minus its two ends is preconnected.** -/
theorem isPreconnected_chainSet_diff_ends {a b : ℝ × ℝ} {l : List (ℝ × ℝ)}
    (hs : IsSimpleChain (a :: b :: l)) :
    IsPreconnected (chainSet (a :: b :: l) \ {a, (a :: b :: l).getLast (by simp)}) := by
  by_cases hl : l = []
  · subst hl
    have : chainSet [a, b] \ {a, [a, b].getLast (by simp)} = segment ℝ a b \ {a, b} := by
      rw [chainSet_pair]; simp
    rw [this]
    exact isPreconnected_segment_diff_ends hs.1
  · set z := (b :: l).getLast (by simp) with hz
    have hzc : z ∈ chainSet (b :: l) := last_mem_chainSet _ _
    have hzb : z ≠ b := by
      obtain ⟨c', l', rfl⟩ := List.exists_cons_of_ne_nil hl
      exact getLast_ne_head hs.2.2
    have hzs : z ∉ segment ℝ a b := fun hzs => by
      have : z ∈ segment ℝ a b ∩ chainSet (b :: l) := ⟨hzs, hzc⟩
      rw [hs.2.1] at this
      exact hzb (by simpa using this)
    have has : a ∉ chainSet (b :: l) := head_notMem_tail hs
    have e : chainSet (a :: b :: l) \ {a, (a :: b :: l).getLast (by simp)} =
        (segment ℝ a b \ {a}) ∪ (chainSet (b :: l) \ {z}) := by
      rw [List.getLast_cons (by simp)]
      ext y
      simp only [chainSet, mem_sdiff, mem_union, mem_singleton_iff, mem_insert_iff]
      constructor
      · rintro ⟨h | h, hy⟩
        · exact Or.inl ⟨h, fun hya => hy (Or.inl hya)⟩
        · exact Or.inr ⟨h, fun hyz => hy (Or.inr hyz)⟩
      · rintro (⟨h, hya⟩ | ⟨h, hy⟩)
        · exact ⟨Or.inl h, fun hh => hh.elim hya fun hyz => hzs (by have hyz' : y = z := hyz; rw [← hyz']; exact h)⟩
        · exact ⟨Or.inr h, fun hh => hh.elim (fun hya => has (by rw [← hya]; exact h)) hy⟩
    rw [e]
    refine IsPreconnected.union b ⟨right_mem_segment ℝ a b, fun h => hs.1 h.symm⟩
      ⟨mem_chainSet_head b l, hzb.symm⟩ (isPreconnected_segment_diff_left hs.1)
      (isPreconnected_chainSet_diff_last (b :: l) (by simp) hs.2.2)

end Lightlike.PL
