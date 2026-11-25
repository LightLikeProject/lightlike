import Mathlib
import Lightlike.PL.LoopErase

/-!
# The last hit of a simple chain with a closed set

Row G3-188 (PL5), step 4a of the pass-4 plan.  `exists_last_hit`: a simple chain `R` meeting a closed set `A`
has a point `h` of `A` such that the tail of `R` from `h` is a simple chain meeting `A` only in `h`.
-/

open Set Metric

namespace Lightlike.PL.Schoenflies

open Lightlike.PL

theorem exists_last_hit : ∀ (R : List (ℝ × ℝ)), IsSimpleChain R → ∀ A : Set (ℝ × ℝ), IsClosed A →
    (chainSet R ∩ A).Nonempty → ∃ h ∈ chainSet R ∩ A, ∃ t : List (ℝ × ℝ), IsSimpleChain t ∧
      t.head? = some h ∧ t.getLast? = R.getLast? ∧ chainSet t ⊆ chainSet R ∧ chainSet t ∩ A ⊆ {h}
  | [], _, A, _, ⟨x, hx, _⟩ => by simp [chainSet] at hx
  | [a], _, A, _, ⟨x, hx, hxA⟩ => by
    simp only [chainSet, mem_singleton_iff] at hx
    subst hx
    exact ⟨x, ⟨by simp [chainSet], hxA⟩, [x], trivial, rfl, rfl, subset_rfl, fun y hy => hy.1⟩
  | a :: b :: r, hs, A, hA, hne => by
    obtain ⟨hab, hinter, hrest⟩ := hs
    by_cases h1 : (chainSet (b :: r) ∩ A).Nonempty
    · obtain ⟨h, hh, t, ht, ht1, ht2, ht3, ht4⟩ := exists_last_hit (b :: r) hrest A hA h1
      refine ⟨h, ⟨?_, hh.2⟩, t, ht, ht1, ?_, ?_, ht4⟩
      · simp only [chainSet]; exact Or.inr hh.1
      · simpa using ht2
      · intro y hy; simp only [chainSet]; exact Or.inr (ht3 hy)
    · have h2 : chainSet (b :: r) ∩ A = ∅ := not_nonempty_iff_eq_empty.1 h1
      obtain ⟨x, hx⟩ := hne
      have hxseg : x ∈ segment ℝ a b := by
        have hx1 := hx.1
        simp only [chainSet, mem_union] at hx1
        rcases hx1 with h | h
        · exact h
        · exact absurd ⟨x, h, hx.2⟩ h1
      have hseg : IsCompact (segment ℝ a b) := by
        rw [segment_eq_image]; exact isCompact_Icc.image (by fun_prop)
      have hK : IsCompact (segment ℝ a b ∩ A) := hseg.inter_right hA
      obtain ⟨h, hh, hmin⟩ := hK.exists_isMinOn ⟨x, hxseg, hx.2⟩
        (f := fun y => dist y b) (by fun_prop)
      have hbA : b ∉ A := fun hb => by
        have : b ∈ chainSet (b :: r) ∩ A := ⟨mem_chainSet_head b r, hb⟩
        rw [h2] at this; exact this
      have hhb : h ≠ b := fun e => hbA (e ▸ hh.2)
      have hsub : segment ℝ h b ⊆ segment ℝ a b :=
        (convex_segment a b).segment_subset hh.1 (right_mem_segment ℝ a b)
      refine ⟨h, ⟨?_, hh.2⟩, h :: b :: r, ⟨hhb, ?_, hrest⟩, rfl, ?_, ?_, ?_⟩
      · simp only [chainSet]; exact Or.inl hh.1
      · apply Set.eq_singleton_iff_unique_mem.2
        refine ⟨⟨right_mem_segment ℝ _ _, mem_chainSet_head b r⟩, fun y hy => ?_⟩
        have : y ∈ segment ℝ a b ∩ chainSet (b :: r) := ⟨hsub hy.1, hy.2⟩
        rw [hinter] at this; exact this
      · simp
      · intro y hy
        simp only [chainSet, mem_union] at hy ⊢
        rcases hy with hy | hy
        · exact Or.inl (hsub hy)
        · exact Or.inr hy
      · rintro y ⟨hy, hyA⟩
        simp only [chainSet, mem_union] at hy
        rcases hy with hy | hy
        · have hyseg : y ∈ segment ℝ a b ∩ A := ⟨hsub hy, hyA⟩
          have h3 := hmin hyseg
          have h4 : dist y b ≤ dist h b := by
            have := (convex_closedBall b (dist h b)).segment_subset
              (mem_closedBall_self dist_nonneg) (by simp : h ∈ closedBall b (dist h b))
            rw [segment_symm] at hy
            exact mem_closedBall.1 (this hy)
          have h5 : dist y b = dist h b := le_antisymm h4 h3
          rw [segment_symm] at hy
          exact eq_of_dist_eq hy h5
        · have : y ∈ chainSet (b :: r) ∩ A := ⟨hy, hyA⟩
          rw [h2] at this; exact this.elim

lemma isCompact_segment' (a b : ℝ × ℝ) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image]; exact isCompact_Icc.image (by fun_prop)

/-- The set of a chain is closed. -/
lemma isClosed_chainSet : ∀ l : List (ℝ × ℝ), IsClosed (chainSet l)
  | [] => by simp [chainSet]
  | [a] => by simp [chainSet]
  | a :: b :: l => by
    simp only [chainSet]
    exact (isCompact_segment' a b).isClosed.union (isClosed_chainSet (b :: l))

lemma mem_chainSet_of_head {l : List (ℝ × ℝ)} {a : ℝ × ℝ} (h : l.head? = some a) : a ∈ chainSet l := by
  cases l with
  | nil => simp at h
  | cons x l' =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h; exact mem_chainSet_head _ _

lemma mem_chainSet_of_getLast {l : List (ℝ × ℝ)} {b : ℝ × ℝ} (h : l.getLast? = some b) : b ∈ chainSet l := by
  have : l.reverse.head? = some b := by rw [List.head?_reverse]; exact h
  have := mem_chainSet_of_head this
  rwa [chainSet_reverse] at this

/-- **Fixing a junction.** Two simple chains `L` (ending at `e`) and `R` (starting at `e`) are replaced by an
initial part `L'` of `L` and a tail `R'` of `R` that meet exactly in the common point `h` where `L'` ends and
`R'` starts. The start of `L` and the end of `R` are kept. -/
theorem fix_junction {L R : List (ℝ × ℝ)} (hL : IsSimpleChain L) (hR : IsSimpleChain R) {e : ℝ × ℝ}
    (hLe : L.getLast? = some e) (hRe : R.head? = some e) :
    ∃ (L' R' : List (ℝ × ℝ)) (h : ℝ × ℝ), IsSimpleChain L' ∧ IsSimpleChain R' ∧ L'.head? = L.head? ∧
      L'.getLast? = some h ∧ R'.head? = some h ∧ R'.getLast? = R.getLast? ∧ chainSet L' ⊆ chainSet L ∧
      chainSet R' ⊆ chainSet R ∧ chainSet L' ∩ chainSet R' = {h} := by
  obtain ⟨h, hh, t, ht, ht1, ht2, ht3, ht4⟩ := exists_last_hit R hR (chainSet L) (isClosed_chainSet L)
    ⟨e, mem_chainSet_of_head hRe, mem_chainSet_of_getLast hLe⟩
  have hLr : IsSimpleChain L.reverse := isSimpleChain_reverse hL
  have hh' : h ∈ chainSet L.reverse := by rw [chainSet_reverse]; exact hh.2
  obtain ⟨s, hs, hs1, hs2, hs3⟩ := exists_simple_tail L.reverse hLr h hh'
  have hs' : IsSimpleChain s.reverse := isSimpleChain_reverse hs
  have hs1' : s.reverse.getLast? = some h := by rw [List.getLast?_reverse]; exact hs1
  have hs2' : s.reverse.head? = L.head? := by
    rw [List.head?_reverse, hs2, List.getLast?_reverse]
  have hsub : chainSet s.reverse ⊆ chainSet L := by
    rw [chainSet_reverse]; intro y hy; have := hs3 hy; rwa [chainSet_reverse] at this
  refine ⟨s.reverse, t, h, hs', ht, hs2', hs1', ht1, ht2, hsub, ht3, ?_⟩
  apply Set.eq_singleton_iff_unique_mem.2
  exact ⟨⟨mem_chainSet_of_getLast hs1', mem_chainSet_of_head ht1⟩,
    fun y hy => ht4 ⟨hy.2, hsub hy.1⟩⟩

end Lightlike.PL.Schoenflies
