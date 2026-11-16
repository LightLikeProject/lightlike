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

end Lightlike.PL
