import Lightlike.PL.OrderSplit
import Lightlike.PL.Starring
import Lightlike.PL.OrderLink
import Lightlike.PL.CutStep

/-!
# Order complexes with a top element, and with two incomparable top elements

If `a` lies above every element of a finite set `L` of a poset, the order complex of `L` together
with `a` is the cone on the order complex of `L`. If two incomparable elements `u` and `v` each lie
above part of `N` and every element of `N` lies below one of them, the order complex of `N` together
with `u` and `v` is the union of the cones on the order complexes of the two lower parts.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {P : Type*} [PartialOrder P] [DecidableEq P]

/-- **A top element makes a cone.** If `a` lies above every element of `L`, the order complex of
`insert a L` is the cone on that of `L`. -/
theorem orderComplex_insert_top {L : Finset P} {a : P} (hle : ∀ l ∈ L, l ≤ a) :
    orderComplex (insert a L) = cone a (orderComplex L) := by
  classical
  refine ext_mem fun C => ?_
  rw [mem_cone, mem_orderComplex]
  constructor
  · rintro ⟨hCS, hch⟩
    refine ⟨C.erase a, mem_orderComplex.2 ⟨?_, fun x hx y hy =>
      hch x (mem_of_mem_erase hx) y (mem_of_mem_erase hy)⟩, ?_⟩
    · intro x hx
      obtain ⟨hxa, hxC⟩ := mem_erase.1 hx
      rcases mem_insert.1 (hCS hxC) with h | h
      · exact absurd h hxa
      · exact h
    · by_cases haC : a ∈ C
      · exact .inr (insert_erase haC).symm
      · exact .inl (erase_eq_of_notMem haC).symm
  · rintro ⟨t, ht, rfl | rfl⟩
    · obtain ⟨hts, htc⟩ := mem_orderComplex.1 ht
      exact ⟨hts.trans (subset_insert _ _), htc⟩
    · obtain ⟨hts, htc⟩ := mem_orderComplex.1 ht
      refine ⟨insert_subset_insert _ hts, fun x hx y hy => ?_⟩
      rcases mem_insert.1 hx with hxa | hxt <;> rcases mem_insert.1 hy with hya | hyt
      · exact .inl (hxa.trans hya.symm).le
      · exact .inr (hxa ▸ hle y (hts hyt))
      · exact .inl (hya ▸ hle x (hts hxt))
      · exact htc x hxt y hyt

open Classical in
/-- **Two incomparable top elements make a union of two cones.** Every element of `N` lies below
`u` or below `v`, and `u`, `v` are incomparable. -/
theorem orderComplex_insert_two {N : Finset P} {u v : P}
    (huv : ¬ u ≤ v) (hvu : ¬ v ≤ u) (hN : ∀ x ∈ N, x < u ∨ x < v) :
    orderComplex (insert u (insert v N)) =
      (cone u (orderComplex (N.filter (· < u)))).union
        (cone v (orderComplex (N.filter (· < v)))) := by
  classical
  have hNu : ∀ x ∈ N, ¬ u ≤ x := fun x hx h => by
    rcases hN x hx with h' | h'
    · exact absurd (lt_of_le_of_lt h h') (lt_irrefl _)
    · exact huv (h.trans h'.le)
  have hNv : ∀ x ∈ N, ¬ v ≤ x := fun x hx h => by
    rcases hN x hx with h' | h'
    · exact hvu (h.trans h'.le)
    · exact absurd (lt_of_le_of_lt h h') (lt_irrefl _)
  have hsub : ∀ x ∈ N, x ∈ insert u (insert v N) := fun x hx =>
    mem_insert_of_mem (mem_insert_of_mem hx)
  refine ext_mem fun C => ?_
  rw [mem_union_iff, mem_cone, mem_cone, mem_orderComplex]
  constructor
  · rintro ⟨hCS, hch⟩
    by_cases huC : u ∈ C
    · have hvC : v ∉ C := fun hvC => by
        rcases hch u huC v hvC with h | h
        · exact huv h
        · exact hvu h
      have hCN : ∀ x ∈ C.erase u, x ∈ N := by
        intro x hx
        obtain ⟨hxu, hxC⟩ := mem_erase.1 hx
        rcases mem_insert.1 (hCS hxC) with h | h
        · exact absurd h hxu
        rcases mem_insert.1 h with h | h
        · exact absurd (h ▸ hxC) hvC
        · exact h
      refine .inl ⟨C.erase u, mem_orderComplex.2 ⟨fun x hx => ?_, fun x hx y hy =>
        hch x (mem_of_mem_erase hx) y (mem_of_mem_erase hy)⟩, .inr (insert_erase huC).symm⟩
      refine mem_filter.2 ⟨hCN x hx, ?_⟩
      rcases hch x (mem_of_mem_erase hx) u huC with h | h
      · exact lt_of_le_of_ne h (mem_erase.1 hx).1
      · exact absurd h (hNu x (hCN x hx))
    by_cases hvC : v ∈ C
    · have hCN : ∀ x ∈ C.erase v, x ∈ N := by
        intro x hx
        obtain ⟨hxv, hxC⟩ := mem_erase.1 hx
        rcases mem_insert.1 (hCS hxC) with h | h
        · exact absurd (h ▸ hxC) huC
        rcases mem_insert.1 h with h | h
        · exact absurd h hxv
        · exact h
      refine .inr ⟨C.erase v, mem_orderComplex.2 ⟨fun x hx => ?_, fun x hx y hy =>
        hch x (mem_of_mem_erase hx) y (mem_of_mem_erase hy)⟩, .inr (insert_erase hvC).symm⟩
      refine mem_filter.2 ⟨hCN x hx, ?_⟩
      rcases hch x (mem_of_mem_erase hx) v hvC with h | h
      · exact lt_of_le_of_ne h (mem_erase.1 hx).1
      · exact absurd h (hNv x (hCN x hx))
    · have hCN : C ⊆ N := by
        intro x hx
        rcases mem_insert.1 (hCS hx) with h | h
        · exact absurd (h ▸ hx) huC
        rcases mem_insert.1 h with h | h
        · exact absurd (h ▸ hx) hvC
        · exact h
      rcases C.eq_empty_or_nonempty with rfl | hne
      · exact .inl ⟨∅, mem_orderComplex.2 ⟨empty_subset _, by simp⟩, .inl rfl⟩
      · obtain ⟨m, hM⟩ := C.exists_maximal hne
        have hm : m ∈ C := hM.1
        have hle : ∀ x ∈ C, x ≤ m := fun x hx => by
          rcases hch x hx m hm with h | h
          · exact h
          · exact hM.2 hx h
        rcases hN m (hCN hm) with h | h
        · exact .inl ⟨C, mem_orderComplex.2 ⟨fun x hx => mem_filter.2 ⟨hCN hx,
            lt_of_le_of_lt (hle x hx) h⟩, hch⟩, .inl rfl⟩
        · exact .inr ⟨C, mem_orderComplex.2 ⟨fun x hx => mem_filter.2 ⟨hCN hx,
            lt_of_le_of_lt (hle x hx) h⟩, hch⟩, .inl rfl⟩
  · rintro (⟨t, ht, rfl | rfl⟩ | ⟨t, ht, rfl | rfl⟩)
    · obtain ⟨hts, htc⟩ := mem_orderComplex.1 ht
      exact ⟨fun x hx => hsub x (mem_filter.1 (hts hx)).1, htc⟩
    · obtain ⟨hts, htc⟩ := mem_orderComplex.1 ht
      refine ⟨insert_subset (mem_insert_self _ _) fun x hx =>
        hsub x (mem_filter.1 (hts hx)).1, fun x hx y hy => ?_⟩
      rcases mem_insert.1 hx with hxa | hxt <;> rcases mem_insert.1 hy with hya | hyt
      · exact .inl (hxa.trans hya.symm).le
      · exact .inr (hxa ▸ (mem_filter.1 (hts hyt)).2.le)
      · exact .inl (hya ▸ (mem_filter.1 (hts hxt)).2.le)
      · exact htc x hxt y hyt
    · obtain ⟨hts, htc⟩ := mem_orderComplex.1 ht
      exact ⟨fun x hx => hsub x (mem_filter.1 (hts hx)).1, htc⟩
    · obtain ⟨hts, htc⟩ := mem_orderComplex.1 ht
      refine ⟨insert_subset (mem_insert_of_mem (mem_insert_self _ _)) fun x hx =>
        hsub x (mem_filter.1 (hts hx)).1, fun x hx y hy => ?_⟩
      rcases mem_insert.1 hx with hxa | hxt <;> rcases mem_insert.1 hy with hya | hyt
      · exact .inl (hxa.trans hya.symm).le
      · exact .inr (hxa ▸ (mem_filter.1 (hts hyt)).2.le)
      · exact .inl (hya ▸ (mem_filter.1 (hts hxt)).2.le)
      · exact htc x hxt y hyt

/-- A vertex of an order complex is an element of the underlying set. -/
lemma mem_of_mem_verts_orderComplex {S : Finset P} {x : P} (hx : x ∈ (orderComplex S).verts) :
    x ∈ S := by
  have := (mem_orderComplex.1 (mem_verts.1 hx)).1
  exact this (mem_singleton_self x)

/-- Deleting the top vertex `z` from the order complex of `insert z S` leaves that of `S`. -/
lemma del_orderComplex_insert {S : Finset P} {z : P} (hz : z ∉ S) :
    (orderComplex (insert z S)).del {z} = orderComplex S := by
  refine ext_mem fun C => ?_
  rw [mem_del, mem_orderComplex, mem_orderComplex, singleton_subset_iff]
  constructor
  · rintro ⟨⟨hCS, hch⟩, hzC⟩
    refine ⟨fun x hx => ?_, hch⟩
    rcases mem_insert.1 (hCS hx) with h | h
    · exact absurd (h ▸ hx) hzC
    · exact h
  · rintro ⟨hCS, hch⟩
    exact ⟨⟨hCS.trans (subset_insert _ _), hch⟩, fun h => hz (hCS h)⟩

open Classical in
/-- If every element of `N` lies below `u` or below `v`, every chain of `N` lies below one of them. -/
lemma orderComplex_eq_union_of_cover {N : Finset P} {u v : P} (hN : ∀ x ∈ N, x < u ∨ x < v) :
    orderComplex N = (orderComplex (N.filter (· < u))).union (orderComplex (N.filter (· < v))) := by
  refine ext_mem fun C => ?_
  rw [mem_union_iff, mem_orderComplex, mem_orderComplex, mem_orderComplex]
  constructor
  · rintro ⟨hCS, hch⟩
    rcases C.eq_empty_or_nonempty with rfl | hne
    · exact .inl ⟨empty_subset _, by simp⟩
    · obtain ⟨m, hM⟩ := C.exists_maximal hne
      have hle : ∀ x ∈ C, x ≤ m := fun x hx => by
        rcases hch x hx m hM.1 with h | h
        · exact h
        · exact hM.2 hx h
      rcases hN m (hCS hM.1) with h | h
      · exact .inl ⟨fun x hx => mem_filter.2 ⟨hCS hx, lt_of_le_of_lt (hle x hx) h⟩, hch⟩
      · exact .inr ⟨fun x hx => mem_filter.2 ⟨hCS hx, lt_of_le_of_lt (hle x hx) h⟩, hch⟩
  · rintro (⟨hCS, hch⟩ | ⟨hCS, hch⟩)
    · exact ⟨fun x hx => (mem_filter.1 (hCS hx)).1, hch⟩
    · exact ⟨fun x hx => (mem_filter.1 (hCS hx)).1, hch⟩

open Classical in
/-- **The cut swap for order complexes.** Let `z` be adjoined to a finite set `L` of a poset, below
two incomparable elements `u` and `v` that lie above all of `L` between them, and let the elements of
`L` below both `u` and `v` lie below `z`. If the order complexes of the elements below `u` and `v`
(with `z`) are spheres, then replacing a top element `a` over `L` by the three elements `u`, `z`, `v`
is a stellar equivalence inside any surrounding order complex that meets the block only along the
shared neighbours `Up` above and `Rest` beside it. -/
theorem stellarEquivIn_order_cut [Infinite P] {n : ℕ} {L Up Rest : Finset P} {a u v z : P}
    (hLa : ∀ l ∈ L, l ≤ a) (hzL : z ∉ L) (hzu : z < u) (hzv : z < v)
    (huv : ¬ u ≤ v) (hvu : ¬ v ≤ u) (hLuv : ∀ x ∈ L, x < u ∨ x < v)
    (hcomm : ∀ x ∈ L, x < u → x < v → x < z) (hzx : ∀ x ∈ L, ¬ z < x)
    (hSp : IsSB false (n + 1) (orderComplex (insert z (L.filter (· < u)))))
    (hSm : IsSB false (n + 1) (orderComplex (insert z (L.filter (· < v)))))
    (haN : a ∉ insert z L) (huN : u ∉ insert z L) (hvN : v ∉ insert z L)
    (hUp : Disjoint (insert z L) Up) (haUp : a ∉ Up) (huUp : u ∉ Up) (hvUp : v ∉ Up)
    (hzR : z ∉ Rest) (haR : a ∉ Rest) (huR : u ∉ Rest) (hvR : v ∉ Rest) :
    StellarEquivIn ((orderComplex Rest).union ((orderComplex (insert a L)).join (orderComplex Up)))
      ((orderComplex Rest).union
        ((orderComplex (insert u (insert v (insert z L)))).join (orderComplex Up))) := by
  have hzu' : ∀ x ∈ L, x < z → x < u := fun x _ h => h.trans hzu
  have hzv' : ∀ x ∈ L, x < z → x < v := fun x _ h => h.trans hzv
  have hN : ∀ x ∈ insert z L, x < u ∨ x < v := fun x hx => by
    rcases mem_insert.1 hx with rfl | hx
    · exact .inl hzu
    · exact hLuv x hx
  have hfu : (insert z L).filter (· < u) = insert z (L.filter (· < u)) := by
    rw [filter_insert]; simp [hzu]
  have hfv : (insert z L).filter (· < v) = insert z (L.filter (· < v)) := by
    rw [filter_insert]; simp [hzv]
  have hnu : u ∉ L := fun h => huN (mem_insert_of_mem h)
  have hnv : v ∉ L := fun h => hvN (mem_insert_of_mem h)
  have hL : orderComplex L =
      ((orderComplex (insert z (L.filter (· < u)))).del {z}).union
        ((orderComplex (insert z (L.filter (· < v)))).del {z}) := by
    rw [del_orderComplex_insert (fun h => hzL (mem_filter.1 h).1),
      del_orderComplex_insert (fun h => hzL (mem_filter.1 h).1)]
    exact orderComplex_eq_union_of_cover hLuv
  have hbefore : orderComplex (insert a L) = cone a (orderComplex L) :=
    orderComplex_insert_top hLa
  have hafter : orderComplex (insert u (insert v (insert z L))) =
      (cone u (orderComplex (insert z (L.filter (· < u))))).union
        (cone v (orderComplex (insert z (L.filter (· < v))))) := by
    have := orderComplex_insert_two (N := insert z L) huv hvu hN
    rwa [hfu, hfv] at this
  have hzSp : {z} ∈ orderComplex (insert z (L.filter (· < u))) :=
    mem_orderComplex.2 ⟨by simp, by simp⟩
  have hzSm : {z} ∈ orderComplex (insert z (L.filter (· < v))) :=
    mem_orderComplex.2 ⟨by simp, by simp⟩
  have hlink : ∀ w, z < w → (orderComplex (insert z (L.filter (· < w)))).link {z} =
      (orderComplex (L.filter (· < z))).join (orderComplex (∅ : Finset P)) := by
    intro w hzw
    rw [link_orderComplex (mem_insert_self _ _)]
    have h1 : (insert z (L.filter (· < w))).filter (· < z) = L.filter (· < z) := by
      rw [filter_insert]; simp only [lt_irrefl, ite_false]
      ext x
      simp only [mem_filter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hzw⟩, h.2⟩⟩
    have h2 : (insert z (L.filter (· < w))).filter (z < ·) = ∅ := by
      rw [filter_insert]; simp only [lt_irrefl, ite_false]
      ext x
      simp only [mem_filter, notMem_empty, iff_false, not_and]
      exact fun h => hzx x h.1 |> fun hh h' => hh h'
    rw [h1, h2]
  have hG : (orderComplex (insert z (L.filter (· < u)))).link {z} =
      (orderComplex (insert z (L.filter (· < v)))).link {z} := by
    rw [hlink u hzu, hlink v hzv]
  have hint : ∀ s, s ∈ (orderComplex (insert z (L.filter (· < u)))).del {z} →
      s ∈ (orderComplex (insert z (L.filter (· < v)))).del {z} →
      s ∈ (orderComplex (insert z (L.filter (· < u)))).link {z} := by
    intro s hs1 hs2
    rw [del_orderComplex_insert (fun h => hzL (mem_filter.1 h).1)] at hs1 hs2
    obtain ⟨hs1', hch⟩ := mem_orderComplex.1 hs1
    obtain ⟨hs2', -⟩ := mem_orderComplex.1 hs2
    rw [mem_link', singleton_union]
    have hzs : z ∉ s := fun h => hzL (mem_filter.1 (hs1' h)).1
    refine ⟨disjoint_singleton_left.2 hzs, mem_orderComplex.2 ⟨?_, fun x hx y hy => ?_⟩⟩
    · intro x hx
      rcases mem_insert.1 hx with rfl | hx
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (hs1' hx)
    · have key : ∀ x ∈ s, x < z := fun x hx =>
        hcomm x (mem_filter.1 (hs1' hx)).1 (mem_filter.1 (hs1' hx)).2 (mem_filter.1 (hs2' hx)).2
      rcases mem_insert.1 hx with hxz | hxs <;> rcases mem_insert.1 hy with hyz | hys
      · exact .inl (hxz.trans hyz.symm).le
      · exact .inr (hxz ▸ (key y hys).le)
      · exact .inl (hyz ▸ (key x hxs).le)
      · exact hch x hxs y hys
  have hSpv : (orderComplex (insert z (L.filter (· < u)))).verts ⊆ insert z L := fun x hx =>
    insert_subset_insert _ (filter_subset _ _) (mem_of_mem_verts_orderComplex hx)
  have hSmv : (orderComplex (insert z (L.filter (· < v)))).verts ⊆ insert z L := fun x hx =>
    insert_subset_insert _ (filter_subset _ _) (mem_of_mem_verts_orderComplex hx)
  have hUv : ∀ {w : P}, w ∉ Up → w ∉ (orderComplex Up).verts := fun h h' =>
    h (mem_of_mem_verts_orderComplex h')
  have hRv : ∀ {w : P}, w ∉ Rest → w ∉ (orderComplex Rest).verts := fun h h' =>
    h (mem_of_mem_verts_orderComplex h')
  have hZ : ∅ ∈ orderComplex Up := mem_orderComplex.2 ⟨empty_subset _, by simp⟩
  have key := stellarEquivIn_cut_swap (n := n) (Z := orderComplex Up) (R := orderComplex Rest)
    hSp hSm hzSp hzSm hG hint hZ
    (Finset.disjoint_left.2 fun x hx hx' =>
      Finset.disjoint_left.1 hUp (hSpv hx) (mem_of_mem_verts_orderComplex hx'))
    (Finset.disjoint_left.2 fun x hx hx' =>
      Finset.disjoint_left.1 hUp (hSmv hx) (mem_of_mem_verts_orderComplex hx'))
    (hUv haUp) (hUv huUp) (hUv hvUp)
    (fun h => haN (hSpv h)) (fun h => haN (hSmv h))
    (fun h => huN (hSpv h)) (fun h => huN (hSmv h))
    (fun h => hvN (hSpv h)) (fun h => hvN (hSmv h))
    (fun h => huv (h ▸ le_rfl)) (hRv hzR) (hRv haR) (hRv huR) (hRv hvR)
  rw [hbefore, hL, hafter, union_comm (orderComplex Rest), union_comm (orderComplex Rest)]
  exact key

end SComplex
end Lightlike.PL
