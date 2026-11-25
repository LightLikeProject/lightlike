import Mathlib
import Lightlike.PL.SimpleChain

/-!
# Cutting a simple chain at a vertex

Row G3-188 (PL5), ring cells.  `isSimpleChain_split`: a simple chain `pa ++ x :: qa` is cut at the vertex `x`
into two simple chains `pa ++ [x]` and `x :: qa` that meet only in `x`.
-/

open Set

namespace Lightlike.PL.Schoenflies

open Lightlike.PL

theorem isSimpleChain_split : ∀ (pa : List (ℝ × ℝ)) (x : ℝ × ℝ) (qa : List (ℝ × ℝ)),
    IsSimpleChain (pa ++ x :: qa) →
      IsSimpleChain (pa ++ [x]) ∧ IsSimpleChain (x :: qa) ∧
        chainSet (pa ++ [x]) ∩ chainSet (x :: qa) = {x}
  | [], x, qa, h => by
    refine ⟨trivial, by simpa using h, ?_⟩
    simp only [List.nil_append, chainSet]
    exact Set.inter_eq_left.2 (singleton_subset_iff.2 (mem_chainSet_head x qa))
  | [a], x, qa, h => by
    simp only [List.singleton_append] at h
    obtain ⟨hax, hseg, hrest⟩ := h
    refine ⟨⟨hax, ?_, trivial⟩, hrest, ?_⟩
    · simp only [chainSet]
      exact Set.inter_eq_right.2 (singleton_subset_iff.2 (right_mem_segment ℝ a x))
    simp only [List.singleton_append, chainSet_pair]
    exact hseg
  | a :: b :: pa, x, qa, h => by
    have h' : IsSimpleChain (a :: b :: (pa ++ x :: qa)) := by simpa using h
    obtain ⟨hab, hseg, hrest⟩ := h'
    have hrest' : IsSimpleChain (b :: pa ++ x :: qa) := by simpa using hrest
    obtain ⟨ih1, ih2, ih3⟩ := isSimpleChain_split (b :: pa) x qa hrest'
    have hset : chainSet (a :: b :: pa ++ [x]) = segment ℝ a b ∪ chainSet (b :: pa ++ [x]) := by
      simp [chainSet]
    refine ⟨?_, ih2, ?_⟩
    · -- simple: the first segment meets the later ones only in `b`
      have : IsSimpleChain (a :: (b :: pa ++ [x])) := by
        refine ⟨hab, ?_, ih1⟩
        have hsub : chainSet (b :: pa ++ [x]) ⊆ chainSet (b :: (pa ++ x :: qa)) := by
          intro y hy
          have := chainSet_append (b :: pa) x qa
          have h2 : chainSet (b :: pa ++ x :: qa) = chainSet (b :: pa ++ [x]) ∪ chainSet (x :: qa) := this
          simp only [List.cons_append] at h2 ⊢
          rw [h2]; exact Or.inl hy
        apply Set.eq_singleton_iff_unique_mem.2
        refine ⟨⟨right_mem_segment ℝ a b, mem_chainSet_head b _⟩, fun y hy => ?_⟩
        have : y ∈ segment ℝ a b ∩ chainSet (b :: (pa ++ x :: qa)) := ⟨hy.1, hsub hy.2⟩
        rw [hseg] at this; exact this
      simpa using this
    · rw [hset, union_inter_distrib_right, ih3]
      have hseg2 : segment ℝ a b ∩ chainSet (x :: qa) ⊆ {x} := by
        intro y hy
        have hy2 : y ∈ chainSet (b :: (pa ++ x :: qa)) := by
          have := chainSet_append (b :: pa) x qa
          simp only [List.cons_append] at this ⊢
          rw [this]; exact Or.inr hy.2
        have : y ∈ segment ℝ a b ∩ chainSet (b :: (pa ++ x :: qa)) := ⟨hy.1, hy2⟩
        rw [hseg] at this
        have hyb : y = b := this
        have hb1 : b ∈ chainSet (b :: pa ++ [x]) ∩ chainSet (x :: qa) := ⟨mem_chainSet_head b _, hyb ▸ hy.2⟩
        rw [ih3] at hb1
        exact hyb.trans hb1
      apply Set.Subset.antisymm
      · rintro y (hy | hy)
        · exact hseg2 hy
        · exact hy
      · rintro y rfl
        exact Or.inr rfl

end Lightlike.PL.Schoenflies
