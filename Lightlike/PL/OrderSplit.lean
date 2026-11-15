import Lightlike.PL.OrderLink
import Lightlike.PL.Ball

/-!
# Order complexes with a distinguished block

If `W` is a set of elements of a finite poset whose comparable neighbours are a lower part `L` and
an upper part `Up`, with `L` and `W` below `Up`, then the order complex of `N ∪ W` is the order
complex of `N` together with the join of the order complex of `L ∪ W` and that of `Up`. Replacing
the block `W` by another block with the same neighbours changes only the middle factor of the join.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {P : Type*} [PartialOrder P] [DecidableEq P]

/-- **Decomposition of an order complex along a block.** -/
theorem orderComplex_union_block {N W L Up : Finset P} (hL : L ⊆ N) (hUp : Up ⊆ N)
    (hLU : ∀ l ∈ L, ∀ u ∈ Up, l ≤ u) (hWU : ∀ w ∈ W, ∀ u ∈ Up, w ≤ u)
    (hcomp : ∀ n ∈ N, ∀ w ∈ W, (n ≤ w ∨ w ≤ n) → n ∈ L ∨ n ∈ Up) :
    orderComplex (N ∪ W) =
      (orderComplex N).union ((orderComplex (L ∪ W)).join (orderComplex Up)) := by
  classical
  refine ext_mem fun C => ?_
  rw [mem_union_iff, mem_join, mem_orderComplex]
  constructor
  · rintro ⟨hCS, hch⟩
    by_cases hCN : C ⊆ N
    · exact .inl (mem_orderComplex.2 ⟨hCN, hch⟩)
    · right
      obtain ⟨w, hwC, hwN⟩ := not_subset.1 hCN
      have hwW : w ∈ W := by
        rcases mem_union.1 (hCS hwC) with h | h
        · exact absurd h hwN
        · exact h
      have hside : ∀ x ∈ C, x ∈ L ∪ W ∨ x ∈ Up := by
        intro x hx
        rcases mem_union.1 (hCS hx) with h | h
        · exact (hcomp x h w hwW (hch x hx w hwC)).elim (fun h' => .inl (mem_union_left _ h'))
            .inr
        · exact .inl (mem_union_right _ h)
      refine ⟨C.filter (· ∈ L ∪ W), ?_, C.filter (· ∈ Up), ?_, ?_⟩
      · refine mem_orderComplex.2 ⟨fun x hx => (mem_filter.1 hx).2, fun a ha b hb => ?_⟩
        exact hch a (mem_filter.1 ha).1 b (mem_filter.1 hb).1
      · refine mem_orderComplex.2 ⟨fun x hx => (mem_filter.1 hx).2, fun a ha b hb => ?_⟩
        exact hch a (mem_filter.1 ha).1 b (mem_filter.1 hb).1
      · ext x
        simp only [mem_union, mem_filter]
        constructor
        · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
        · intro hx
          rcases hside x hx with h | h
          · exact .inl ⟨hx, mem_union.1 h⟩
          · exact .inr ⟨hx, h⟩
  · rintro (hC | ⟨t, ht, u, hu, rfl⟩)
    · obtain ⟨hCN, hch⟩ := mem_orderComplex.1 hC
      exact ⟨hCN.trans subset_union_left, hch⟩
    · obtain ⟨ht1, ht2⟩ := mem_orderComplex.1 ht
      obtain ⟨hu1, hu2⟩ := mem_orderComplex.1 hu
      have hLWU : ∀ x ∈ L ∪ W, ∀ y ∈ Up, x ≤ y := by
        intro x hx y hy
        rcases mem_union.1 hx with h | h
        · exact hLU x h y hy
        · exact hWU x h y hy
      refine ⟨union_subset ((ht1.trans (union_subset_union_left hL)))
        (hu1.trans (hUp.trans subset_union_left)), ?_⟩
      intro a ha b hb
      rcases mem_union.1 ha with ha | ha <;> rcases mem_union.1 hb with hb | hb
      · exact ht2 a ha b hb
      · exact .inl (hLWU a (ht1 ha) b (hu1 hb))
      · exact .inr (hLWU b (ht1 hb) a (hu1 ha))
      · exact hu2 a ha b hb

end SComplex
end Lightlike.PL
