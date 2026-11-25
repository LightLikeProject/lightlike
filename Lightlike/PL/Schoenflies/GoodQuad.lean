import Mathlib
import Lightlike.PL.SimpleChain
import Lightlike.PL.TwoArcs
import Lightlike.PL.Schoenflies.ChainSplitSet
import Lightlike.PL.Schoenflies.ChainHit

/-!
# Good cells of a ring

Row G3-188 (PL5), ring cells.  `simple_append_spoke`: two simple chains joined by a segment between the end of
the first and the start of the second form a simple chain when the segment and the chains meet only at the
expected points.
-/

open Set

namespace Lightlike.PL.Schoenflies

open Lightlike.PL

theorem simple_append_spoke {α β : List (ℝ × ℝ)} {w v : ℝ × ℝ} (hα : IsSimpleChain α)
    (hβ : IsSimpleChain β) (hαl : α.getLast? = some w) (hβh : β.head? = some v)
    (h1 : segment ℝ w v ∩ chainSet α = {w}) (h2 : segment ℝ w v ∩ chainSet β = {v})
    (h3 : chainSet α ∩ chainSet β = ∅) :
    IsSimpleChain (α ++ β) ∧ chainSet (α ++ β) = chainSet α ∪ segment ℝ w v ∪ chainSet β := by
  obtain ⟨rest, hrest⟩ : ∃ rest, β = v :: rest := by
    cases β with
    | nil => simp at hβh
    | cons x t => simp at hβh; subst hβh; exact ⟨t, rfl⟩
  obtain ⟨l₁, hl₁⟩ : ∃ l₁, α = l₁ ++ [w] := by
    rcases List.eq_nil_or_concat α with rfl | ⟨m, z, rfl⟩
    · simp at hαl
    · refine ⟨m, ?_⟩
      simp only [List.concat_eq_append] at hαl ⊢
      have : (m ++ [z]).getLast? = some z := by simp
      rw [this] at hαl; rw [Option.some.inj hαl]
  subst hrest; subst hl₁
  have hwα : w ∈ chainSet (l₁ ++ [w]) := mem_chainSet_of_getLast hαl
  have hvβ : v ∈ chainSet (v :: rest) := mem_chainSet_head v rest
  have hwv : w ≠ v := by
    intro e
    have : w ∈ chainSet (l₁ ++ [w]) ∩ chainSet (v :: rest) := ⟨hwα, e ▸ hvβ⟩
    rw [h3] at this; exact this
  have hmid : IsSimpleChain (w :: v :: rest) := ⟨hwv, h2, hβ⟩
  have hmidset : chainSet (w :: v :: rest) = segment ℝ w v ∪ chainSet (v :: rest) := by simp [chainSet]
  have hd : chainSet (l₁ ++ [w]) ∩ chainSet (w :: v :: rest) = {w} := by
    apply Set.eq_singleton_iff_unique_mem.2
    refine ⟨⟨hwα, mem_chainSet_head w _⟩, fun y hy => ?_⟩
    rw [hmidset] at hy
    rcases hy.2 with hy2 | hy2
    · have : y ∈ segment ℝ w v ∩ chainSet (l₁ ++ [w]) := ⟨hy2, hy.1⟩
      rw [h1] at this; exact this
    · have : y ∈ chainSet (l₁ ++ [w]) ∩ chainSet (v :: rest) := ⟨hy.1, hy2⟩
      rw [h3] at this; exact this.elim
  have e : l₁ ++ [w] ++ (v :: rest) = l₁ ++ w :: v :: rest := by simp
  rw [e]
  refine ⟨isSimpleChain_append (l₁ := l₁) (l₂ := v :: rest) (b := w) hα hmid hd, ?_⟩
  rw [chainSet_append (l₁ := l₁) (b := w) (l₂ := v :: rest), hmidset]
  ext y; simp only [mem_union]; tauto

/-- **A good cell of a ring**: an inner chain `α` (from `w` to `w'`) and an outer chain `β` (from `v` to `v'`),
both simple and disjoint, joined by the spokes `[w, v]` and `[w', v']`, which are disjoint, meet `α` only in
`w`, `w'` and `β` only in `v`, `v'`. -/
structure GoodQuad (w w' v v' : ℝ × ℝ) (α β : List (ℝ × ℝ)) : Prop where
  simpα : IsSimpleChain α
  simpβ : IsSimpleChain β
  headα : α.head? = some w
  lastα : α.getLast? = some w'
  headβ : β.head? = some v
  lastβ : β.getLast? = some v'
  disj : chainSet α ∩ chainSet β = ∅
  sw : segment ℝ w v ∩ chainSet α = {w}
  sv : segment ℝ w v ∩ chainSet β = {v}
  sw' : segment ℝ w' v' ∩ chainSet α = {w'}
  sv' : segment ℝ w' v' ∩ chainSet β = {v'}
  ss : Disjoint (segment ℝ w v) (segment ℝ w' v')

lemma head?_cons_append_of {pa qa : List (ℝ × ℝ)} {x w : ℝ × ℝ} (h : (pa ++ x :: qa).head? = some w) :
    (pa ++ [x]).head? = some w := by
  cases pa with
  | nil => simpa using h
  | cons a t => simpa using h

lemma getLast?_of_append_cons {pa qa : List (ℝ × ℝ)} {x w' : ℝ × ℝ}
    (h : (pa ++ x :: qa).getLast? = some w') : (x :: qa).getLast? = some w' := by
  rcases List.eq_nil_or_concat qa with rfl | ⟨m, z, rfl⟩
  · simpa using h
  · simp only [List.concat_eq_append] at h ⊢
    have h2 : (x :: (m ++ [z])).getLast? = some z := by
      rw [List.getLast?_cons, List.getLast?_append_of_ne_nil]
      all_goals simp
    have h1 : (pa ++ x :: (m ++ [z])).getLast? = some z := by
      rw [List.getLast?_append_of_ne_nil _ (by simp)]; exact h2
    rw [h1] at h; rw [h2]; exact h

/-- **Cutting a good cell along a spoke** gives two good cells. -/
theorem GoodQuad.split {w w' v v' x y : ℝ × ℝ} {pa qa pb qb : List (ℝ × ℝ)}
    (h : GoodQuad w w' v v' (pa ++ x :: qa) (pb ++ y :: qb))
    (hs1 : segment ℝ x y ∩ chainSet (pa ++ x :: qa) = {x})
    (hs2 : segment ℝ x y ∩ chainSet (pb ++ y :: qb) = {y})
    (hs3 : Disjoint (segment ℝ x y) (segment ℝ w v))
    (hs4 : Disjoint (segment ℝ x y) (segment ℝ w' v')) :
    GoodQuad x w' y v' (x :: qa) (y :: qb) ∧ GoodQuad w x v y (pa ++ [x]) (pb ++ [y]) := by
  obtain ⟨hαs1, hαs2, hαint⟩ := isSimpleChain_split pa x qa h.simpα
  obtain ⟨hβs1, hβs2, hβint⟩ := isSimpleChain_split pb y qb h.simpβ
  have hαset : chainSet (pa ++ x :: qa) = chainSet (pa ++ [x]) ∪ chainSet (x :: qa) := chainSet_append pa x qa
  have hβset : chainSet (pb ++ y :: qb) = chainSet (pb ++ [y]) ∪ chainSet (y :: qb) := chainSet_append pb y qb
  have xa1 : x ∈ chainSet (pa ++ [x]) := mem_chainSet_last pa x
  have xa2 : x ∈ chainSet (x :: qa) := mem_chainSet_head x qa
  have yb1 : y ∈ chainSet (pb ++ [y]) := mem_chainSet_last pb y
  have yb2 : y ∈ chainSet (y :: qb) := mem_chainSet_head y qb
  have hsub1 : chainSet (pa ++ [x]) ⊆ chainSet (pa ++ x :: qa) := by rw [hαset]; exact subset_union_left
  have hsub2 : chainSet (x :: qa) ⊆ chainSet (pa ++ x :: qa) := by rw [hαset]; exact subset_union_right
  have hsub3 : chainSet (pb ++ [y]) ⊆ chainSet (pb ++ y :: qb) := by rw [hβset]; exact subset_union_left
  have hsub4 : chainSet (y :: qb) ⊆ chainSet (pb ++ y :: qb) := by rw [hβset]; exact subset_union_right
  -- the end points are on the chains
  have hw : w ∈ chainSet (pa ++ [x]) := mem_chainSet_of_head (head?_cons_append_of h.headα)
  have hv : v ∈ chainSet (pb ++ [y]) := mem_chainSet_of_head (head?_cons_append_of h.headβ)
  have hw' : w' ∈ chainSet (x :: qa) := mem_chainSet_of_getLast (getLast?_of_append_cons h.lastα)
  have hv' : v' ∈ chainSet (y :: qb) := mem_chainSet_of_getLast (getLast?_of_append_cons h.lastβ)
  have hsegx : x ∈ segment ℝ x y := left_mem_segment ℝ x y
  have hsegy : y ∈ segment ℝ x y := right_mem_segment ℝ x y
  have hxw : x ∉ segment ℝ w v := fun hh => Set.disjoint_left.1 hs3 hsegx hh
  have hxw' : x ∉ segment ℝ w' v' := fun hh => Set.disjoint_left.1 hs4 hsegx hh
  have hyw : y ∉ segment ℝ w v := fun hh => Set.disjoint_left.1 hs3 hsegy hh
  have hyw' : y ∉ segment ℝ w' v' := fun hh => Set.disjoint_left.1 hs4 hsegy hh
  have key : ∀ {A B B' : Set (ℝ × ℝ)} {p : ℝ × ℝ}, A ∩ B = {p} → B' ⊆ B → p ∈ A → p ∈ B' → A ∩ B' = {p} := by
    intro A B B' p hAB hB hpA hpB
    apply Set.eq_singleton_iff_unique_mem.2
    exact ⟨⟨hpA, hpB⟩, fun z hz => by
      have : z ∈ A ∩ B := ⟨hz.1, hB hz.2⟩
      rw [hAB] at this; exact this⟩
  have hwseg : w ∈ segment ℝ w v := left_mem_segment ℝ w v
  have hvseg : v ∈ segment ℝ w v := right_mem_segment ℝ w v
  have hw'seg : w' ∈ segment ℝ w' v' := left_mem_segment ℝ w' v'
  have hv'seg : v' ∈ segment ℝ w' v' := right_mem_segment ℝ w' v'
  constructor
  · refine ⟨hαs2, hβs2, rfl, getLast?_of_append_cons h.lastα, rfl, getLast?_of_append_cons h.lastβ, ?_,
      key hs1 hsub2 hsegx xa2, key hs2 hsub4 hsegy yb2, key h.sw' hsub2 hw'seg hw', key h.sv' hsub4 hv'seg hv', hs4⟩
    exact Set.eq_empty_of_subset_empty (h.disj ▸ inter_subset_inter hsub2 hsub4)
  · refine ⟨hαs1, hβs1, head?_cons_append_of h.headα, by simp, head?_cons_append_of h.headβ, by simp, ?_,
      key h.sw hsub1 hwseg hw, key h.sv hsub3 hvseg hv, key hs1 hsub1 hsegx xa1, key hs2 hsub3 hsegy yb1, hs3.symm⟩
    exact Set.eq_empty_of_subset_empty (h.disj ▸ inter_subset_inter hsub1 hsub3)

/-- **The hypotheses of `quad_split_region` from a good cell**: the two chains of the split. -/
theorem GoodQuad.split_hyps {w w' v v' x y : ℝ × ℝ} {pa qa pb qb : List (ℝ × ℝ)}
    (h : GoodQuad w w' v v' (pa ++ x :: qa) (pb ++ y :: qb))
    (hs1 : segment ℝ x y ∩ chainSet (pa ++ x :: qa) = {x})
    (hs2 : segment ℝ x y ∩ chainSet (pb ++ y :: qb) = {y})
    (hs3 : Disjoint (segment ℝ x y) (segment ℝ w v))
    (hs4 : Disjoint (segment ℝ x y) (segment ℝ w' v')) (hxy : x ≠ y) :
    IsSimpleChain (x :: (qa ++ qb.reverse) ++ [y]) ∧ IsSimpleChain (y :: (pb.reverse ++ pa) ++ [x]) ∧
    chainSet (x :: (qa ++ qb.reverse) ++ [y]) ∩ chainSet (y :: (pb.reverse ++ pa) ++ [x]) = {x, y} ∧
    chainSet (x :: (qa ++ qb.reverse) ++ [y]) ∩ segment ℝ x y = {x, y} ∧
    chainSet (y :: (pb.reverse ++ pa) ++ [x]) ∩ segment ℝ x y = {x, y} := by
  obtain ⟨L, R⟩ := h.split hs1 hs2 hs3 hs4
  obtain ⟨hαs1, hαs2, hαint⟩ := isSimpleChain_split pa x qa h.simpα
  obtain ⟨hβs1, hβs2, hβint⟩ := isSimpleChain_split pb y qb h.simpβ
  have hαset : chainSet (pa ++ x :: qa) = chainSet (pa ++ [x]) ∪ chainSet (x :: qa) := chainSet_append pa x qa
  have hβset : chainSet (pb ++ y :: qb) = chainSet (pb ++ [y]) ∪ chainSet (y :: qb) := chainSet_append pb y qb
  have xa1 : x ∈ chainSet (pa ++ [x]) := mem_chainSet_last pa x
  have xa2 : x ∈ chainSet (x :: qa) := mem_chainSet_head x qa
  have yb1 : y ∈ chainSet (pb ++ [y]) := mem_chainSet_last pb y
  have yb2 : y ∈ chainSet (y :: qb) := mem_chainSet_head y qb
  have hsegx : x ∈ segment ℝ x y := left_mem_segment ℝ x y
  have hsegy : y ∈ segment ℝ x y := right_mem_segment ℝ x y
  have hxw : x ∉ segment ℝ w v := fun hh => Set.disjoint_left.1 hs3 hsegx hh
  have hxw' : x ∉ segment ℝ w' v' := fun hh => Set.disjoint_left.1 hs4 hsegx hh
  have hyw : y ∉ segment ℝ w v := fun hh => Set.disjoint_left.1 hs3 hsegy hh
  have hyw' : y ∉ segment ℝ w' v' := fun hh => Set.disjoint_left.1 hs4 hsegy hh
  have hw : w ∈ chainSet (pa ++ [x]) := mem_chainSet_of_head (head?_cons_append_of h.headα)
  have hv : v ∈ chainSet (pb ++ [y]) := mem_chainSet_of_head (head?_cons_append_of h.headβ)
  have hw' : w' ∈ chainSet (x :: qa) := mem_chainSet_of_getLast (getLast?_of_append_cons h.lastα)
  have hv' : v' ∈ chainSet (y :: qb) := mem_chainSet_of_getLast (getLast?_of_append_cons h.lastβ)
  -- the two chains
  have eA1 : x :: (qa ++ qb.reverse) ++ [y] = (x :: qa) ++ (y :: qb).reverse := by simp
  have eA2 : y :: (pb.reverse ++ pa) ++ [x] = (pb ++ [y]).reverse ++ (pa ++ [x]) := by simp
  have hrev1 : ((y :: qb).reverse).head? = some v' := by
    rw [List.head?_reverse]; exact L.lastβ
  have hA1 := simple_append_spoke (w := w') (v := v') L.simpα (isSimpleChain_reverse L.simpβ) L.lastα hrev1
    L.sw' (by rw [chainSet_reverse]; exact L.sv') (by rw [chainSet_reverse]; exact L.disj)
  have hrev2 : ((pb ++ [y]).reverse).getLast? = some v := by
    rw [List.getLast?_reverse]; exact R.headβ
  have hA2 := simple_append_spoke (w := v) (v := w) (isSimpleChain_reverse R.simpβ) R.simpα hrev2 R.headα
    (by rw [chainSet_reverse, segment_symm]; exact R.sv) (by rw [segment_symm]; exact R.sw)
    (by rw [chainSet_reverse, Set.inter_comm]; exact R.disj)
  rw [eA1, eA2]
  rw [chainSet_reverse] at hA1 hA2
  rw [segment_symm ℝ v w] at hA2
  obtain ⟨hs_A1, hset1⟩ := hA1
  obtain ⟨hs_A2, hset2⟩ := hA2
  have hsub1 : chainSet (pa ++ [x]) ⊆ chainSet (pa ++ x :: qa) := by rw [hαset]; exact subset_union_left
  have hsub2 : chainSet (x :: qa) ⊆ chainSet (pa ++ x :: qa) := by rw [hαset]; exact subset_union_right
  have hsub3 : chainSet (pb ++ [y]) ⊆ chainSet (pb ++ y :: qb) := by rw [hβset]; exact subset_union_left
  have hsub4 : chainSet (y :: qb) ⊆ chainSet (pb ++ y :: qb) := by rw [hβset]; exact subset_union_right
  have Fdisj : ∀ {z}, z ∈ chainSet (pa ++ x :: qa) → z ∈ chainSet (pb ++ y :: qb) → False := fun {z} h1 h2 => by
    have : z ∈ chainSet (pa ++ x :: qa) ∩ chainSet (pb ++ y :: qb) := ⟨h1, h2⟩
    rw [h.disj] at this; exact this
  have Fa2a1 : ∀ {z}, z ∈ chainSet (x :: qa) → z ∈ chainSet (pa ++ [x]) → z = x := fun {z} h1 h2 => by
    have : z ∈ chainSet (pa ++ [x]) ∩ chainSet (x :: qa) := ⟨h2, h1⟩
    rw [hαint] at this; exact this
  have Fb2b1 : ∀ {z}, z ∈ chainSet (y :: qb) → z ∈ chainSet (pb ++ [y]) → z = y := fun {z} h1 h2 => by
    have : z ∈ chainSet (pb ++ [y]) ∩ chainSet (y :: qb) := ⟨h2, h1⟩
    rw [hβint] at this; exact this
  have Fa2σ : ∀ {z}, z ∈ chainSet (x :: qa) → z ∈ segment ℝ w v → False := fun {z} h1 h2 => by
    have : z ∈ segment ℝ w v ∩ chainSet (pa ++ x :: qa) := ⟨h2, hsub2 h1⟩
    rw [h.sw] at this
    have hzw : z = w := this
    subst hzw
    exact hxw (Fa2a1 h1 hw ▸ h2)
  have Fb2σ : ∀ {z}, z ∈ chainSet (y :: qb) → z ∈ segment ℝ w v → False := fun {z} h1 h2 => by
    have : z ∈ segment ℝ w v ∩ chainSet (pb ++ y :: qb) := ⟨h2, hsub4 h1⟩
    rw [h.sv] at this
    have hzv : z = v := this
    subst hzv
    exact hyw (Fb2b1 h1 hv ▸ h2)
  have Fa1σ' : ∀ {z}, z ∈ chainSet (pa ++ [x]) → z ∈ segment ℝ w' v' → False := fun {z} h1 h2 => by
    have : z ∈ segment ℝ w' v' ∩ chainSet (pa ++ x :: qa) := ⟨h2, hsub1 h1⟩
    rw [h.sw'] at this
    have hzw : z = w' := this
    subst hzw
    exact hxw' (Fa2a1 hw' h1 ▸ h2)
  have Fb1σ' : ∀ {z}, z ∈ chainSet (pb ++ [y]) → z ∈ segment ℝ w' v' → False := fun {z} h1 h2 => by
    have : z ∈ segment ℝ w' v' ∩ chainSet (pb ++ y :: qb) := ⟨h2, hsub3 h1⟩
    rw [h.sv'] at this
    have hzv : z = v' := this
    subst hzv
    exact hyw' (Fb2b1 hv' h1 ▸ h2)
  refine ⟨hs_A1, hs_A2, ?_, ?_, ?_⟩
  · rw [hset1, hset2]
    ext z
    constructor
    · rintro ⟨(h1 | h1) | h1, (h2 | h2) | h2⟩
      · exact absurd h1 (fun _ => Fdisj (hsub2 h1) (hsub3 h2))
      · exact (Fa2σ h1 h2).elim
      · exact Or.inl (Fa2a1 h1 h2)
      · exact (Fb1σ' h2 h1).elim
      · exact (Set.disjoint_left.1 h.ss h2 h1).elim
      · exact (Fa1σ' h2 h1).elim
      · exact Or.inr (Fb2b1 h1 h2)
      · exact (Fb2σ h1 h2).elim
      · exact (Fdisj (hsub1 h2) (hsub4 h1)).elim
    · rintro (rfl | rfl)
      · exact ⟨Or.inl (Or.inl xa2), Or.inr xa1⟩
      · exact ⟨Or.inr yb2, Or.inl (Or.inl yb1)⟩
  · rw [hset1]
    apply Set.Subset.antisymm
    · rintro z ⟨(h1 | h1) | h1, h2⟩
      · have : z ∈ segment ℝ x y ∩ chainSet (x :: qa) := ⟨h2, h1⟩
        rw [L.sw] at this; exact Or.inl this
      · exact (Set.disjoint_left.1 hs4 h2 h1).elim
      · have : z ∈ segment ℝ x y ∩ chainSet (y :: qb) := ⟨h2, h1⟩
        rw [L.sv] at this; exact Or.inr this
    · rintro z (rfl | rfl)
      · exact ⟨Or.inl (Or.inl xa2), hsegx⟩
      · exact ⟨Or.inr yb2, hsegy⟩
  · rw [hset2]
    apply Set.Subset.antisymm
    · rintro z ⟨(h1 | h1) | h1, h2⟩
      · have : z ∈ segment ℝ x y ∩ chainSet (pb ++ [y]) := ⟨h2, h1⟩
        rw [R.sv'] at this; exact Or.inr this
      · exact (Set.disjoint_left.1 hs3 h2 h1).elim
      · have : z ∈ segment ℝ x y ∩ chainSet (pa ++ [x]) := ⟨h2, h1⟩
        rw [R.sw'] at this; exact Or.inl this
    · rintro z (rfl | rfl)
      · exact ⟨Or.inr xa1, hsegx⟩
      · exact ⟨Or.inl (Or.inl yb1), hsegy⟩

end Lightlike.PL.Schoenflies
