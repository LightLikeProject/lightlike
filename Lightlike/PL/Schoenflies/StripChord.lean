import Mathlib
import Lightlike.PL.Schoenflies.QuadBoundary

/-!
# The short chord of a cell

Row G3-188 (PL5), nested ring.  For a good cell with inner chain `α` (from `w` to `w'`) and outer chain `β` (from `v` to `v'`),
the chord `v' → (α reversed, from w' to w) → v` is a simple chain, whose set is `[w', v'] ∪ α ∪ [w, v]`
(`GoodQuad.chord_simple`).  It is the chord that cuts the cell off the polygon of the outer chain.
-/

open Set

namespace Lightlike.PL.Schoenflies

open Lightlike.PL

theorem GoodQuad.chord_simple {w w' v v' : ℝ × ℝ} {α β : List (ℝ × ℝ)} (h : GoodQuad w w' v v' α β) :
    IsSimpleChain (v' :: α.reverse ++ [v]) ∧
      chainSet (v' :: α.reverse ++ [v]) = segment ℝ w' v' ∪ chainSet α ∪ segment ℝ w v := by
  have wα : w ∈ chainSet α := mem_chainSet_of_head h.headα
  have w'α : w' ∈ chainSet α := mem_chainSet_of_getLast h.lastα
  have vβ : v ∈ chainSet β := mem_chainSet_of_head h.headβ
  have v'β : v' ∈ chainSet β := mem_chainSet_of_getLast h.lastβ
  have hv'α : v' ∉ chainSet α := fun hh => by
    have : v' ∈ chainSet α ∩ chainSet β := ⟨hh, v'β⟩
    rw [h.disj] at this; exact this
  have hvα : v ∉ chainSet α := fun hh => by
    have : v ∈ chainSet α ∩ chainSet β := ⟨hh, vβ⟩
    rw [h.disj] at this; exact this
  have hrev : α.reverse.head? = some w' := by rw [List.head?_reverse]; exact h.lastα
  have hrevl : α.reverse.getLast? = some w := by rw [List.getLast?_reverse]; exact h.headα
  -- the first step: `[v'] ++ α.reverse`
  have s1 := simple_append_spoke (α := [v']) (β := α.reverse) (w := v') (v := w') trivial
    (isSimpleChain_reverse h.simpα) rfl hrev
    (by
      simp only [chainSet]
      apply Set.eq_singleton_iff_unique_mem.2
      exact ⟨⟨left_mem_segment ℝ _ _, rfl⟩, fun z hz => hz.2⟩)
    (by rw [chainSet_reverse, segment_symm]; exact h.sw')
    (by simp only [chainSet, singleton_inter_eq_empty]; rw [chainSet_reverse]; exact hv'α)
  obtain ⟨hs1, hset1⟩ := s1
  -- the second step: `([v'] ++ α.reverse) ++ [v]`
  have hne : α.reverse ≠ [] := by
    intro e
    have hh := h.headα
    have e' : α = [] := by simpa using e
    rw [e'] at hh; simp at hh
  have hlast1 : ([v'] ++ α.reverse).getLast? = some w := by
    rw [List.getLast?_append_of_ne_nil _ hne]
    exact hrevl
  have hset1' : chainSet ([v'] ++ α.reverse) = {v'} ∪ segment ℝ v' w' ∪ chainSet α := by
    rw [hset1]; simp only [chainSet]; rw [chainSet_reverse]
  have s2 := simple_append_spoke (α := [v'] ++ α.reverse) (β := [v]) (w := w) (v := v) hs1 trivial hlast1 rfl
    (by
      rw [hset1']
      apply Set.eq_singleton_iff_unique_mem.2
      refine ⟨⟨left_mem_segment ℝ _ _, Or.inr wα⟩, fun z hz => ?_⟩
      obtain ⟨hzs, (hz1 | hz1) | hz1⟩ := hz
      · exfalso
        have : v' = z := hz1.symm
        subst this
        exact Set.disjoint_left.1 h.ss hzs (right_mem_segment ℝ _ _) |>.elim
      · exfalso
        exact Set.disjoint_left.1 h.ss hzs (by rw [segment_symm] at hz1; exact hz1)
      · have : z ∈ segment ℝ w v ∩ chainSet α := ⟨hzs, hz1⟩
        rw [h.sw] at this; exact this)
    (by
      simp only [chainSet]
      apply Set.eq_singleton_iff_unique_mem.2
      exact ⟨⟨right_mem_segment ℝ _ _, rfl⟩, fun z hz => hz.2⟩)
    (by
      rw [hset1']
      apply Set.eq_empty_of_forall_notMem
      rintro z ⟨hz1, hz2⟩
      have hzv : z = v := hz2
      subst hzv
      rcases hz1 with (hz | hz) | hz
      · have : z = v' := hz
        subst this
        exact Set.disjoint_left.1 h.ss (right_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
      · exact Set.disjoint_left.1 h.ss (right_mem_segment ℝ _ _) (by rw [segment_symm] at hz; exact hz)
      · exact hvα hz)
  obtain ⟨hs2, hset2⟩ := s2
  have e : v' :: α.reverse ++ [v] = ([v'] ++ α.reverse) ++ [v] := by simp
  rw [e]
  refine ⟨hs2, ?_⟩
  rw [hset2, hset1']
  have hv'seg : v' ∈ segment ℝ w' v' := right_mem_segment ℝ _ _
  have hvseg : v ∈ segment ℝ w v := right_mem_segment ℝ _ _
  ext z
  simp only [mem_union, mem_singleton_iff, segment_symm ℝ v' w', chainSet]
  constructor
  · rintro ((((hz | hz) | hz) | hz) | hz)
    · exact Or.inl (Or.inl (hz ▸ hv'seg))
    · exact Or.inl (Or.inl hz)
    · exact Or.inl (Or.inr hz)
    · exact Or.inr hz
    · exact Or.inr (hz ▸ hvseg)
  · rintro ((hz | hz) | hz)
    · exact Or.inl (Or.inl (Or.inl (Or.inr hz)))
    · exact Or.inl (Or.inl (Or.inr hz))
    · exact Or.inl (Or.inr hz)

/-- The chord along the outer chain: `w → β → w'` is a simple chain with set `[w, v] ∪ β ∪ [w', v']`. -/
theorem GoodQuad.outer_chord_simple {w w' v v' : ℝ × ℝ} {α β : List (ℝ × ℝ)} (h : GoodQuad w w' v v' α β) :
    IsSimpleChain (w :: β ++ [w']) ∧
      chainSet (w :: β ++ [w']) = segment ℝ w v ∪ chainSet β ∪ segment ℝ w' v' := by
  have wα : w ∈ chainSet α := mem_chainSet_of_head h.headα
  have w'α : w' ∈ chainSet α := mem_chainSet_of_getLast h.lastα
  have hwβ : w ∉ chainSet β := fun hh => by
    have : w ∈ chainSet α ∩ chainSet β := ⟨wα, hh⟩
    rw [h.disj] at this; exact this
  have hw'β : w' ∉ chainSet β := fun hh => by
    have : w' ∈ chainSet α ∩ chainSet β := ⟨w'α, hh⟩
    rw [h.disj] at this; exact this
  have hwS : w ∈ segment ℝ w v := left_mem_segment ℝ _ _
  have hw'S : w' ∈ segment ℝ w' v' := left_mem_segment ℝ _ _
  have hvS : v ∈ segment ℝ w v := right_mem_segment ℝ _ _
  have hv'S : v' ∈ segment ℝ w' v' := right_mem_segment ℝ _ _
  have s1 := simple_append_spoke (α := [w]) (β := β) (w := w) (v := v) trivial h.simpβ rfl h.headβ
    (by
      simp only [chainSet]
      apply Set.eq_singleton_iff_unique_mem.2
      exact ⟨⟨hwS, rfl⟩, fun z hz => hz.2⟩)
    h.sv
    (by simp only [chainSet, singleton_inter_eq_empty]; exact hwβ)
  obtain ⟨hs1, hset1⟩ := s1
  have hset1' : chainSet ([w] ++ β) = {w} ∪ segment ℝ w v ∪ chainSet β := by
    rw [hset1]; simp only [chainSet]
  have hlast1 : ([w] ++ β).getLast? = some v' := by
    have hβne : β ≠ [] := by intro e; have := h.headβ; rw [e] at this; simp at this
    rw [List.getLast?_append_of_ne_nil _ hβne]; exact h.lastβ
  have s2 := simple_append_spoke (α := [w] ++ β) (β := [w']) (w := v') (v := w') hs1 trivial hlast1 rfl
    (by
      rw [hset1', segment_symm]
      apply Set.eq_singleton_iff_unique_mem.2
      refine ⟨⟨hv'S, Or.inr (mem_chainSet_of_getLast h.lastβ)⟩, fun z hz => ?_⟩
      obtain ⟨hzs, (hz1 | hz1) | hz1⟩ := hz
      · exfalso
        have : z = w := hz1
        subst this
        exact Set.disjoint_left.1 h.ss hwS hzs
      · exact (Set.disjoint_left.1 h.ss hz1 hzs).elim
      · have : z ∈ segment ℝ w' v' ∩ chainSet β := ⟨hzs, hz1⟩
        rw [h.sv'] at this; exact this)
    (by
      simp only [chainSet]
      rw [segment_symm]
      apply Set.eq_singleton_iff_unique_mem.2
      exact ⟨⟨hw'S, rfl⟩, fun z hz => hz.2⟩)
    (by
      rw [hset1']
      apply Set.eq_empty_of_forall_notMem
      rintro z ⟨hz1, hz2⟩
      have hzw : z = w' := hz2
      subst hzw
      rcases hz1 with (hz | hz) | hz
      · have : z = w := hz
        subst this
        exact Set.disjoint_left.1 h.ss hwS hw'S
      · exact Set.disjoint_left.1 h.ss hz hw'S
      · exact hw'β hz)
  obtain ⟨hs2, hset2⟩ := s2
  have e : w :: β ++ [w'] = ([w] ++ β) ++ [w'] := by simp
  rw [e]
  refine ⟨hs2, ?_⟩
  rw [hset2, hset1']
  ext z
  simp only [mem_union, mem_singleton_iff, segment_symm ℝ v' w', chainSet]
  constructor
  · rintro ((((hz | hz) | hz) | hz) | hz)
    · exact Or.inl (Or.inl (hz ▸ hwS))
    · exact Or.inl (Or.inl hz)
    · exact Or.inl (Or.inr hz)
    · exact Or.inr hz
    · exact Or.inr (hz ▸ hw'S)
  · rintro ((hz | hz) | hz)
    · exact Or.inl (Or.inl (Or.inl (Or.inr hz)))
    · exact Or.inl (Or.inl (Or.inr hz))
    · exact Or.inl (Or.inr hz)

end Lightlike.PL.Schoenflies
