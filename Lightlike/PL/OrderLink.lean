import Lightlike.PL.OrderComplex

/-!
# Links in an order complex

The link of a vertex `c` in the order complex of a finite poset `S` is the join of the order
complex of the elements below `c` and the order complex of the elements above `c`.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {P : Type*} [PartialOrder P] [DecidableEq P]

open Classical in
/-- **The link of a vertex of an order complex** is the join of the order complexes of the strictly
smaller and the strictly larger elements. -/
theorem link_orderComplex {S : Finset P} {c : P} (hc : c ∈ S) :
    (orderComplex S).link {c} =
      (orderComplex (S.filter (· < c))).join (orderComplex (S.filter (c < ·))) := by
  classical
  refine ext_mem fun C => ?_
  rw [mem_link', mem_join]
  constructor
  · rintro ⟨hd, hC⟩
    obtain ⟨hCS', hch'⟩ := mem_orderComplex.1 hC
    have hCS : C ⊆ S := subset_union_right.trans hCS'
    have hch : ∀ a ∈ C, ∀ b ∈ C, a ≤ b ∨ b ≤ a := fun a ha b hb =>
      hch' a (Finset.mem_union_right _ ha) b (Finset.mem_union_right _ hb)
    have hcC : c ∉ C := fun h => Finset.disjoint_singleton_left.1 hd h
    have hcmp : ∀ a ∈ C, a < c ∨ c < a := fun a ha => by
      have hac : a ≠ c := fun h => hcC (h ▸ ha)
      have := hch' a (Finset.mem_union_right _ ha) c (Finset.mem_union_left _ (Finset.mem_singleton_self c))
      exact this.elim (fun h => .inl (lt_of_le_of_ne h hac)) fun h => .inr (lt_of_le_of_ne h hac.symm)
    refine ⟨C.filter (· < c), mem_orderComplex.2 ⟨?_, ?_⟩, C.filter (c < ·),
      mem_orderComplex.2 ⟨?_, ?_⟩, ?_⟩
    · intro a ha
      obtain ⟨haC, hlt⟩ := Finset.mem_filter.1 ha
      exact Finset.mem_filter.2 ⟨hCS haC, hlt⟩
    · intro a ha b hb
      exact hch a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb).1
    · intro a ha
      obtain ⟨haC, hlt⟩ := Finset.mem_filter.1 ha
      exact Finset.mem_filter.2 ⟨hCS haC, hlt⟩
    · intro a ha b hb
      exact hch a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb).1
    · ext a
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro ha
        exact (hcmp a ha).elim (fun h => .inl ⟨ha, h⟩) fun h => .inr ⟨ha, h⟩
  · rintro ⟨t, ht, u, hu, rfl⟩
    obtain ⟨htS, htch⟩ := mem_orderComplex.1 ht
    obtain ⟨huS, huch⟩ := mem_orderComplex.1 hu
    have htl : ∀ a ∈ t, a < c := fun a ha => (Finset.mem_filter.1 (htS ha)).2
    have hul : ∀ a ∈ u, c < a := fun a ha => (Finset.mem_filter.1 (huS ha)).2
    have hch : ∀ a ∈ t ∪ u, ∀ b ∈ t ∪ u, a ≤ b ∨ b ≤ a := by
      intro a ha b hb
      rcases Finset.mem_union.1 ha with ha | ha <;> rcases Finset.mem_union.1 hb with hb | hb
      · exact htch a ha b hb
      · exact .inl ((htl a ha).trans (hul b hb)).le
      · exact .inr ((htl b hb).trans (hul a ha)).le
      · exact huch a ha b hb
    have hsub : t ∪ u ⊆ S := Finset.union_subset (htS.trans (Finset.filter_subset _ _))
      (huS.trans (Finset.filter_subset _ _))
    have hcn : c ∉ t ∪ u := by
      intro h
      rcases Finset.mem_union.1 h with h | h
      · exact lt_irrefl c (htl c h)
      · exact lt_irrefl c (hul c h)
    refine ⟨Finset.disjoint_singleton_left.2 hcn, mem_orderComplex.2 ⟨?_, ?_⟩⟩
    · intro a ha
      rcases Finset.mem_union.1 ha with ha | ha
      · rw [Finset.mem_singleton.1 ha]; exact hc
      · exact hsub ha
    · intro a ha b hb
      simp only [Finset.mem_union, Finset.mem_singleton] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      all_goals try subst ha
      all_goals try subst hb
      · exact .inl le_rfl
      · exact (hb.elim (fun h => .inr (htl _ h).le) fun h => .inl (hul _ h).le)
      · exact (ha.elim (fun h => .inl (htl _ h).le) fun h => .inr (hul _ h).le)
      · exact hch a (Finset.mem_union.2 ha) b (Finset.mem_union.2 hb)

end SComplex
end Lightlike.PL
