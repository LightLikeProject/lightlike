import Lightlike.PL.Theta

/-!
# Loop erasure of a polygonal chain

A polygonal chain from `a` to `b` contains a simple polygonal chain from `a` to `b` inside its
set: the loops are cut out by going, at each step, to the point of the next segment's tail that is
nearest to the current point.

## Main results

* `exists_simple_sub`: a chain with first point `a` and last point `b` contains a simple chain from
  `a` to `b` in its set.
-/

open Set

namespace Lightlike.PL

/-- A point of a simple chain is the start of a simple chain, inside it, with the same last point. -/
lemma exists_simple_tail : ∀ (s : List (ℝ × ℝ)), IsSimpleChain s → ∀ x ∈ chainSet s,
    ∃ t, IsSimpleChain t ∧ t.head? = some x ∧ t.getLast? = s.getLast? ∧ chainSet t ⊆ chainSet s
  | [], _, x, hx => by simp [chainSet] at hx
  | [p], _, x, hx => by
    simp only [chainSet, mem_singleton_iff] at hx
    subst hx
    exact ⟨[x], trivial, rfl, rfl, subset_rfl⟩
  | a :: b :: r, hs, x, hx => by
    obtain ⟨hab, hinter, hrest⟩ := hs
    simp only [chainSet, mem_union] at hx
    rcases hx with hx | hx
    · by_cases hxb : x = b
      · refine ⟨b :: r, hrest, by simp [hxb], ?_, ?_⟩
        · simp [List.getLast?_cons_cons]
        · intro y hy; simp only [chainSet]; exact Or.inr hy
      · refine ⟨x :: b :: r, ⟨hxb, ?_, hrest⟩, rfl, by simp [List.getLast?_cons_cons], ?_⟩
        · apply Set.eq_singleton_iff_unique_mem.2
          refine ⟨⟨right_mem_segment ℝ x b, mem_chainSet_head b r⟩, fun y ⟨h1, h2⟩ => ?_⟩
          have : y ∈ segment ℝ a b ∩ chainSet (b :: r) :=
            ⟨(convex_segment a b).segment_subset hx (right_mem_segment ℝ a b) h1, h2⟩
          rw [hinter] at this
          exact this
        · intro y hy
          simp only [chainSet, mem_union] at hy ⊢
          rcases hy with hy | hy
          · exact Or.inl ((convex_segment a b).segment_subset hx (right_mem_segment ℝ a b) hy)
          · exact Or.inr hy
    · obtain ⟨t, ht, h1, h2, h3⟩ := exists_simple_tail (b :: r) hrest x hx
      refine ⟨t, ht, h1, by simpa [List.getLast?_cons_cons] using h2, ?_⟩
      intro y hy; simp only [chainSet]; exact Or.inr (h3 hy)

/-- On a segment from `a` to `x`, a point at the same distance from `a` as `x` is `x`. -/
lemma eq_of_dist_eq {a x y : ℝ × ℝ} (hy : y ∈ segment ℝ a x) (hd : dist y a = dist x a) : y = x := by
  by_cases hax : x = a
  · rw [hax, segment_same] at hy
    rw [hax]; exact hy
  · obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hy
    have hyx : p • a + q • x - a = q • (x - a) := by
      obtain rfl : p = 1 - q := by linarith
      module
    rw [dist_eq_norm, dist_eq_norm, hyx, norm_smul, Real.norm_of_nonneg hq] at hd
    have hn : 0 < ‖x - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hax)
    have : q = 1 := by
      have := mul_right_cancel₀ hn.ne' (by linarith : q * ‖x - a‖ = 1 * ‖x - a‖)
      exact this
    subst this
    obtain rfl : p = 0 := by linarith
    simp

/-- **Loop erasure.** A chain from `a` to `b` contains a simple chain from `a` to `b` in its set. -/
theorem exists_simple_sub : ∀ (l : List (ℝ × ℝ)) (a b : ℝ × ℝ), l.head? = some a →
    l.getLast? = some b → ∃ s, IsSimpleChain s ∧ s.head? = some a ∧ s.getLast? = some b ∧
      chainSet s ⊆ chainSet l
  | [], a, b, h, _ => by simp at h
  | [x], a, b, h1, h2 => by
    simp only [List.head?_cons, Option.some.injEq] at h1
    simp only [List.getLast?_singleton, Option.some.injEq] at h2
    subst h1; subst h2
    exact ⟨[x], trivial, rfl, rfl, subset_rfl⟩
  | a' :: c :: rest, a, b, h1, h2 => by
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    have h2' : (c :: rest).getLast? = some b := by simpa [List.getLast?_cons_cons] using h2
    obtain ⟨s, hs, hs1, hs2, hs3⟩ := exists_simple_sub (c :: rest) c b rfl h2'
    set S : Set (ℝ × ℝ) := segment ℝ a' c ∩ chainSet s with hS
    have hSc : IsCompact S :=
      (isCompact_segment' ..).inter_right (isClosed_chainSet s)
    have hcS : c ∈ S := by
      refine ⟨right_mem_segment ℝ a' c, ?_⟩
      obtain ⟨t', rfl⟩ : ∃ t', s = c :: t' := by
        rcases s with _ | ⟨y, t'⟩
        · simp at hs1
        · simp only [List.head?_cons, Option.some.injEq] at hs1; subst hs1; exact ⟨t', rfl⟩
      exact mem_chainSet_head c t'
    obtain ⟨x, hxS, hxmin⟩ := hSc.exists_isMinOn ⟨c, hcS⟩
      (by fun_prop : Continuous fun y : ℝ × ℝ => dist y a').continuousOn
    obtain ⟨t, ht, ht1, ht2, ht3⟩ := exists_simple_tail s hs x hxS.2
    have hsub : chainSet s ⊆ chainSet (a' :: c :: rest) := by
      intro y hy; simp only [chainSet]; exact Or.inr (hs3 hy)
    obtain ⟨t', rfl⟩ : ∃ t', t = x :: t' := by
      rcases t with _ | ⟨y, t'⟩
      · simp at ht1
      · simp only [List.head?_cons, Option.some.injEq] at ht1; subst ht1; exact ⟨t', rfl⟩
    by_cases hxa : x = a'
    · refine ⟨x :: t', ht, by simp [hxa], by simpa [hs2] using ht2, ?_⟩
      exact ht3.trans hsub
    · refine ⟨a' :: x :: t', ⟨fun h => hxa h.symm, ?_, ht⟩, rfl, ?_, ?_⟩
      · apply Set.eq_singleton_iff_unique_mem.2
        refine ⟨⟨right_mem_segment ℝ a' x, mem_chainSet_head x t'⟩, fun y ⟨hy1, hy2⟩ => ?_⟩
        have hyS : y ∈ S := ⟨(convex_segment a' c).segment_subset (left_mem_segment ℝ a' c) hxS.1 hy1,
          ht3 hy2⟩
        have hle : dist x a' ≤ dist y a' := hxmin hyS
        have hge : dist y a' ≤ dist x a' := by
          obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hy1
          have : p • a' + q • x - a' = q • (x - a') := by
            obtain rfl : p = 1 - q := by linarith
            module
          rw [dist_eq_norm, dist_eq_norm, this, norm_smul, Real.norm_of_nonneg hq]
          exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
        exact eq_of_dist_eq hy1 (le_antisymm hge hle)
      · simpa [List.getLast?_cons_cons, hs2] using ht2
      · intro y hy
        simp only [chainSet, mem_union] at hy ⊢
        rcases hy with hy | hy
        · exact Or.inl ((convex_segment a' c).segment_subset (left_mem_segment ℝ a' c) hxS.1 hy)
        · exact Or.inr (hs3 (ht3 hy))

end Lightlike.PL
