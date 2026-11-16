import Lightlike.PL.ChainConn

/-!
# A polygon made of two simple arcs

Two simple polygonal arcs from `a` to `b` and from `b` to `a` that meet only in `a` and `b` form a
simple polygon. Chain lemmas used for this: the prefix of a simple chain is simple, and a simple
chain is contained in the chain obtained by appending a point.
-/

open Set

namespace Lightlike.PL

lemma chainSet_subset_append : ∀ (l : List (ℝ × ℝ)) (x : ℝ × ℝ), l ≠ [] →
    chainSet l ⊆ chainSet (l ++ [x])
  | [], _, h => absurd rfl h
  | [b], x, _ => by
    intro y hy
    simp only [chainSet, mem_singleton_iff] at hy
    subst hy
    simp [chainSet, left_mem_segment]
  | a :: b :: l, x, _ => by
    intro y hy
    simp only [List.cons_append, chainSet] at hy ⊢
    rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr (chainSet_subset_append (b :: l) x (by simp) hy)

/-- **A prefix of a simple chain is simple.** -/
theorem isSimpleChain_prefix : ∀ {l : List (ℝ × ℝ)} {x : ℝ × ℝ},
    IsSimpleChain (l ++ [x]) → IsSimpleChain l
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: b :: l, x, h => by
    simp only [List.cons_append] at h
    obtain ⟨hab, hseg, hrest⟩ := h
    have ih := isSimpleChain_prefix (l := b :: l) (x := x) hrest
    refine ⟨hab, ?_, ih⟩
    apply Set.eq_singleton_iff_unique_mem.2
    refine ⟨⟨right_mem_segment ℝ a b, mem_chainSet_head b l⟩, fun y ⟨hy1, hy2⟩ => ?_⟩
    have : y ∈ segment ℝ a b ∩ chainSet (b :: (l ++ [x])) :=
      ⟨hy1, chainSet_subset_append (b :: l) x (by simp) hy2⟩
    rw [hseg] at this
    exact this

/-- The last segment of a simple chain meets the rest of the chain only at its start. -/
lemma seg_last_inter {c : List (ℝ × ℝ)} {z a : ℝ × ℝ} (h : IsSimpleChain (c ++ [z, a])) :
    segment ℝ z a ∩ chainSet (c ++ [z]) = {z} := by
  have h1 := isSimpleChain_reverse h
  have e : (c ++ [z, a]).reverse = a :: z :: c.reverse := by simp
  rw [e] at h1
  have h2 := h1.2.1
  have e2 : z :: c.reverse = (c ++ [z]).reverse := by simp
  rw [e2, chainSet_reverse, segment_symm] at h2
  exact h2

/-- **A polygon made of two simple arcs.** Two simple polygonal arcs, from `a` to `b` and from `b`
back to `a`, that meet only in their two ends form a simple polygon. -/
theorem isSimple_two_arcs {a b : ℝ × ℝ} {m₁ m₂ : List (ℝ × ℝ)}
    (hP : IsSimpleChain (a :: m₁ ++ [b])) (hQ : IsSimpleChain (b :: m₂ ++ [a]))
    (hPQ : chainSet (a :: m₁ ++ [b]) ∩ chainSet (b :: m₂ ++ [a]) = {a, b}) (hab : a ≠ b) :
    (Polygon.ofList (a :: m₁ ++ b :: m₂)).IsSimple := by
  rcases List.eq_nil_or_concat m₂ with rfl | ⟨m₂', z, rfl⟩
  · -- the second arc is a single segment
    have hm₁ : m₁ ≠ [] := by
      rintro rfl
      have hmid : midpoint ℝ a b ∈ chainSet ([a, b] : List (ℝ × ℝ)) ∩ chainSet [b, a] := by
        rw [chainSet_pair, chainSet_pair, segment_symm ℝ b a]
        exact ⟨midpoint_mem_segment a b, midpoint_mem_segment a b⟩
      have hPQ' : chainSet ([a, b] : List (ℝ × ℝ)) ∩ chainSet [b, a] = {a, b} := hPQ
      rw [hPQ'] at hmid
      rcases hmid with h | h
      · exact hab ((midpoint_eq_left_iff ℝ).1 h)
      · exact hab ((midpoint_eq_right_iff ℝ).1 h)
    have hcl : segment ℝ b a ∩ chainSet (a :: m₁ ++ [b]) = {a, b} := by
      have e : chainSet (b :: [] ++ [a]) = segment ℝ b a := chainSet_pair b a
      rw [e] at hPQ
      rw [Set.inter_comm]; exact hPQ
    exact isSimple_ofList (l := m₁) (by
      have : 0 < m₁.length := List.length_pos_of_ne_nil hm₁
      simp; omega) hP hab hcl
  · -- the second arc has at least two segments
    simp only [List.concat_eq_append] at hQ hPQ ⊢
    have hQ1 : IsSimpleChain ((b :: m₂') ++ [z, a]) := by simpa using hQ
    have hQ2 : IsSimpleChain ((b :: m₂' ++ [z]) ++ [a]) := by simpa using hQ
    have hQpre : IsSimpleChain (b :: m₂' ++ [z]) := isSimpleChain_prefix hQ2
    have hseg : segment ℝ z a ∩ chainSet (b :: m₂' ++ [z]) = {z} := seg_last_inter hQ1
    have hza : z ≠ a := fun h => by
      have := (isSimpleChain_reverse hQ1)
      have e : ((b :: m₂') ++ [z, a]).reverse = a :: z :: (b :: m₂').reverse := by simp
      rw [e] at this
      exact this.1 h.symm
    have hbz : b ≠ z := by
      rcases m₂' with _ | ⟨c, m⟩
      · exact hQpre.1
      · intro h
        have := getLast_ne_head (a := b) (b := c) (l := m ++ [z])
          (show IsSimpleChain (b :: c :: (m ++ [z])) by simpa using hQpre)
        exact this (by simp [h])
    have hbQ : b ∈ chainSet (b :: m₂' ++ [z]) := mem_chainSet_head b (m₂' ++ [z])
    have hzR : z ∈ chainSet (b :: m₂' ++ [z]) := by
      have := mem_chainSet_last (b :: m₂') z
      simpa using this
    have ha_not : a ∉ chainSet (b :: m₂' ++ [z]) := fun h => by
      have : a ∈ segment ℝ z a ∩ chainSet (b :: m₂' ++ [z]) := ⟨right_mem_segment ℝ z a, h⟩
      rw [hseg] at this
      have h' : a = z := by simpa using this
      exact hza h'.symm
    have hb_not : b ∉ segment ℝ z a := fun h => by
      have : b ∈ segment ℝ z a ∩ chainSet (b :: m₂' ++ [z]) := ⟨h, hbQ⟩
      rw [hseg] at this
      exact hbz (by simpa using this)
    have hsegQ : segment ℝ z a ⊆ chainSet (b :: m₂' ++ [z, a]) := by
      have := chainSet_append (b :: m₂') z [a]
      rw [show (b :: m₂') ++ z :: [a] = b :: m₂' ++ [z, a] from by simp] at this
      rw [this]
      intro y hy
      right
      rw [chainSet_pair]
      exact hy
    have hQsub : chainSet (b :: m₂' ++ [z]) ⊆ chainSet (b :: (m₂' ++ [z]) ++ [a]) :=
      chainSet_subset_append _ a (by simp)
    have e1 : a :: m₁ ++ b :: (m₂' ++ [z]) = (a :: m₁) ++ b :: (m₂' ++ [z]) := by simp
    have e2 : a :: m₁ ++ b :: (m₂' ++ [z]) = a :: (m₁ ++ b :: m₂') ++ [z] := by simp
    have hd : chainSet ((a :: m₁) ++ [b]) ∩ chainSet (b :: (m₂' ++ [z])) = {b} := by
      apply Set.eq_singleton_iff_unique_mem.2
      refine ⟨⟨mem_chainSet_last (a :: m₁) b, hbQ⟩, fun y ⟨hy1, hy2⟩ => ?_⟩
      have hy3 : y ∈ chainSet (a :: m₁ ++ [b]) ∩ chainSet (b :: (m₂' ++ [z]) ++ [a]) :=
        ⟨hy1, hQsub hy2⟩
      rw [hPQ] at hy3
      rcases hy3 with rfl | rfl
      · exact absurd hy2 ha_not
      · rfl
    have hc : IsSimpleChain (a :: m₁ ++ b :: (m₂' ++ [z])) := by
      rw [e1]; exact isSimpleChain_append hP hQpre hd
    rw [e2] at hc
    suffices H : ∀ L : List (ℝ × ℝ), L = a :: (m₁ ++ b :: m₂') ++ [z] →
        (Polygon.ofList L).IsSimple from H _ (by simp)
    intro L hL
    subst hL
    refine isSimple_ofList (by simp; omega) hc hza.symm ?_
    have hwhole : chainSet (a :: (m₁ ++ b :: m₂') ++ [z]) =
        chainSet (a :: m₁ ++ [b]) ∪ chainSet (b :: m₂' ++ [z]) := by
      rw [← e2, e1, chainSet_append]
      simp
    rw [hwhole]
    ext y
    simp only [mem_inter_iff, mem_union, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hy1, hy2 | hy2⟩
      · have hyQ : y ∈ chainSet (b :: (m₂' ++ [z]) ++ [a]) := by
          have := hsegQ hy1
          simpa using this
        have hy3 : y ∈ chainSet (a :: m₁ ++ [b]) ∩ chainSet (b :: (m₂' ++ [z]) ++ [a]) :=
          ⟨hy2, hyQ⟩
        rw [hPQ] at hy3
        rcases hy3 with h | h
        · exact Or.inl h
        · exact absurd (h ▸ hy1) hb_not
      · have : y ∈ segment ℝ z a ∩ chainSet (b :: m₂' ++ [z]) := ⟨hy1, hy2⟩
        rw [hseg] at this
        exact Or.inr (by simpa using this)
    · rintro (h | h)
      · rw [h]
        exact ⟨right_mem_segment ℝ z a, Or.inl (mem_chainSet_head a (m₁ ++ [b]))⟩
      · rw [h]
        exact ⟨left_mem_segment ℝ z a, Or.inr hzR⟩

end Lightlike.PL
