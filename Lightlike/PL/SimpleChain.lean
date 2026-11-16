import Lightlike.PL.Chain

/-!
# Simple polygonal chains and the polygons they close up

Statements only for now (`sorry`; not imported). A polygonal chain is a list of points. It is
**simple** when each segment meets the union of the following segments only at its endpoint
shared with the next segment. This recursive description makes gluing and reversing chains
manageable; a closed simple chain is a simple polygon in the sense of `Polygon.IsSimple`.

## Plan

* `chainSet`, `IsSimpleChain`: recursive definitions.
* `isSimpleChain_append`: chains that meet only at the shared endpoint glue to a simple chain.
* `isSimpleChain_reverse`.
* `isSimple_ofList`: the polygon on a list of at least three points whose chain is simple and whose
  closing segment meets the chain only at its two ends is simple.
-/

open Set

namespace Lightlike.PL

/-- The union of the segments of a chain; the single point of a one-point chain. -/
def chainSet : List (ℝ × ℝ) → Set (ℝ × ℝ)
  | [] => ∅
  | [a] => {a}
  | a :: b :: l => segment ℝ a b ∪ chainSet (b :: l)

/-- A chain is **simple**: consecutive points differ, and each segment meets the union of the
later segments only at the endpoint it shares with the next segment. -/
def IsSimpleChain : List (ℝ × ℝ) → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => a ≠ b ∧ segment ℝ a b ∩ chainSet (b :: l) = {b} ∧ IsSimpleChain (b :: l)

lemma mem_chainSet_head (a : ℝ × ℝ) (l : List (ℝ × ℝ)) : a ∈ chainSet (a :: l) := by
  cases l with
  | nil => simp [chainSet]
  | cons b l => simp [chainSet, left_mem_segment]

lemma mem_chainSet_last (l : List (ℝ × ℝ)) (b : ℝ × ℝ) : b ∈ chainSet (l ++ [b]) := by
  induction l with
  | nil => simp [chainSet]
  | cons a l ih =>
    cases l with
    | nil => simp [chainSet, right_mem_segment]
    | cons c l' =>
      simp only [List.cons_append] at ih ⊢
      simp only [chainSet]
      exact Or.inr ih

lemma chainSet_append (l₁ : List (ℝ × ℝ)) (b : ℝ × ℝ) (l₂ : List (ℝ × ℝ)) :
    chainSet (l₁ ++ b :: l₂) = chainSet (l₁ ++ [b]) ∪ chainSet (b :: l₂) := by
  induction l₁ with
  | nil =>
    simp only [List.nil_append, chainSet]
    ext y; simp only [mem_union, mem_singleton_iff]
    constructor
    · intro h; exact Or.inr h
    · rintro (rfl | h)
      · exact mem_chainSet_head _ _
      · exact h
  | cons a l ih =>
    cases l with
    | nil =>
      simp only [List.nil_append, List.cons_append, chainSet]
      ext y; simp only [mem_union, mem_singleton_iff]
      constructor
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rintro ((h | rfl) | h)
        · exact Or.inl h
        · exact Or.inl (right_mem_segment ℝ _ _)
        · exact Or.inr h
    | cons c l' =>
      simp only [List.cons_append] at ih ⊢
      simp only [chainSet]
      rw [ih]
      ext y; simp only [mem_union]; tauto

/-- **Gluing simple chains at a shared endpoint.** -/
theorem isSimpleChain_append {l₁ l₂ : List (ℝ × ℝ)} {b : ℝ × ℝ}
    (h₁ : IsSimpleChain (l₁ ++ [b])) (h₂ : IsSimpleChain (b :: l₂))
    (hd : chainSet (l₁ ++ [b]) ∩ chainSet (b :: l₂) = {b}) :
    IsSimpleChain (l₁ ++ b :: l₂) := by
  induction l₁ with
  | nil => simpa using h₂
  | cons a l ih =>
    cases l with
    | nil =>
      simp only [List.nil_append, List.cons_append] at h₁ hd ⊢
      refine ⟨h₁.1, ?_, h₂⟩
      apply Set.eq_singleton_iff_unique_mem.2
      refine ⟨⟨right_mem_segment ℝ _ _, mem_chainSet_head _ _⟩, fun y hy => ?_⟩
      have : y ∈ chainSet [a, b] ∩ chainSet (b :: l₂) :=
        ⟨Or.inl hy.1, hy.2⟩
      rw [hd] at this; exact this
    | cons x l'' =>
      simp only [List.cons_append] at h₁ hd ih ⊢
      obtain ⟨hax, hseg, hrest⟩ := h₁
      have hd' : chainSet (x :: (l'' ++ [b])) ∩ chainSet (b :: l₂) = {b} := by
        apply Set.eq_singleton_iff_unique_mem.2
        refine ⟨⟨mem_chainSet_last (x :: l'') b, mem_chainSet_head _ _⟩, fun y hy => ?_⟩
        have : y ∈ chainSet (a :: x :: (l'' ++ [b])) ∩ chainSet (b :: l₂) :=
          ⟨by simp only [chainSet]; exact Or.inr hy.1, hy.2⟩
        rw [hd] at this; exact this
      have ih' := ih hrest hd'
      refine ⟨hax, ?_, ih'⟩
      rw [show x :: (l'' ++ b :: l₂) = (x :: l'') ++ b :: l₂ from rfl, chainSet_append]
      apply Set.eq_singleton_iff_unique_mem.2
      refine ⟨⟨right_mem_segment ℝ a x, Or.inl (mem_chainSet_head _ _)⟩,
        fun y ⟨hy1, hy2⟩ => ?_⟩
      rcases hy2 with hy2 | hy2
      · have : y ∈ segment ℝ a x ∩ chainSet (x :: (l'' ++ [b])) := ⟨hy1, hy2⟩
        rw [hseg] at this; exact this
      · have hyc : y ∈ chainSet (a :: x :: (l'' ++ [b])) ∩ chainSet (b :: l₂) :=
          ⟨by simp only [chainSet]; exact Or.inl hy1, hy2⟩
        rw [hd] at hyc
        have hyb : y = b := hyc
        have : y ∈ segment ℝ a x ∩ chainSet (x :: (l'' ++ [b])) := by
          refine ⟨hy1, ?_⟩
          rw [hyb]; exact mem_chainSet_last (x :: l'') b
        rw [hseg] at this; exact this

lemma chainSet_pair (a b : ℝ × ℝ) : chainSet [a, b] = segment ℝ a b := by
  simp only [chainSet]
  ext y; simp only [mem_union, mem_singleton_iff]
  constructor
  · rintro (h | rfl)
    · exact h
    · exact right_mem_segment ℝ _ _
  · exact Or.inl

lemma chainSet_reverse (l : List (ℝ × ℝ)) : chainSet l.reverse = chainSet l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l'' =>
      have e : (a :: b :: l'').reverse = l''.reverse ++ b :: [a] := by simp
      have e2 : l''.reverse ++ [b] = (b :: l'').reverse := by simp
      rw [e, chainSet_append, e2, ih, chainSet_pair, segment_symm]
      simp only [chainSet]
      exact Set.union_comm _ _

/-- **A reversed simple chain is simple.** -/
theorem isSimpleChain_reverse {l : List (ℝ × ℝ)} (h : IsSimpleChain l) :
    IsSimpleChain l.reverse := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    cases l with
    | nil => trivial
    | cons b l'' =>
      obtain ⟨hab, hseg, hrest⟩ := h
      have e : (a :: b :: l'').reverse = l''.reverse ++ b :: [a] := by simp
      have e2 : l''.reverse ++ [b] = (b :: l'').reverse := by simp
      have hb : IsSimpleChain ([b, a] : List (ℝ × ℝ)) :=
        ⟨hab.symm, Set.inter_eq_right.2 (Set.singleton_subset_iff.2 (right_mem_segment ℝ b a)),
          trivial⟩
      rw [e]
      refine isSimpleChain_append (by rw [e2]; exact ih hrest) hb ?_
      rw [e2, chainSet_reverse, chainSet_pair, segment_symm]
      rw [Set.inter_comm]
      exact hseg

/-- The `i`-th segment of a chain. -/
def cseg (c : List (ℝ × ℝ)) (i : ℕ) : Set (ℝ × ℝ) := segment ℝ (c.getD i 0) (c.getD (i + 1) 0)

lemma cseg_cons_succ (a : ℝ × ℝ) (c : List (ℝ × ℝ)) (i : ℕ) : cseg (a :: c) (i + 1) = cseg c i := by
  simp [cseg]

lemma cseg_subset_chainSet : ∀ (c : List (ℝ × ℝ)) (i : ℕ), i + 1 < c.length → cseg c i ⊆ chainSet c
  | [], i, h => by simp at h
  | [_], i, h => by simp at h
  | a :: b :: l, 0, _ => by simp [cseg, chainSet]
  | a :: b :: l, i + 1, h => by
    rw [cseg_cons_succ]
    simp only [chainSet]
    exact (cseg_subset_chainSet (b :: l) i (by simpa using h)).trans subset_union_right

/-- Consecutive points of a simple chain differ. -/
lemma IsSimpleChain.getD_ne : ∀ {c : List (ℝ × ℝ)}, IsSimpleChain c → ∀ i, i + 1 < c.length →
    c.getD i 0 ≠ c.getD (i + 1) 0
  | [], _, i, h => by simp at h
  | [_], _, i, h => by simp at h
  | a :: b :: l, hc, 0, _ => by simpa using hc.1
  | a :: b :: l, hc, i + 1, h => by
    simpa using hc.2.2.getD_ne i (by simpa using h)


lemma left_mem_cseg (c : List (ℝ × ℝ)) (i : ℕ) : c.getD i 0 ∈ cseg c i := left_mem_segment ℝ _ _
lemma right_mem_cseg (c : List (ℝ × ℝ)) (i : ℕ) : c.getD (i + 1) 0 ∈ cseg c i :=
  right_mem_segment ℝ _ _

/-- **Neighbouring segments of a simple chain meet only at their common vertex.** -/
lemma IsSimpleChain.cseg_inter : ∀ {c : List (ℝ × ℝ)}, IsSimpleChain c → ∀ i j, i + 1 = j →
    j + 1 < c.length → cseg c i ∩ cseg c j = {c.getD j 0}
  | [], _, i, j, _, h => by simp at h
  | [_], _, i, j, _, h => by simp at h
  | a :: b :: l, hc, 0, j, hij, hj => by
    subst hij
    apply Set.eq_singleton_iff_unique_mem.2
    refine ⟨⟨?_, ?_⟩, fun y ⟨hy1, hy2⟩ => ?_⟩
    · simpa [cseg] using right_mem_segment ℝ a b
    · simpa [cseg] using left_mem_segment ℝ b ((b :: l).getD 1 0)
    · have h2 : y ∈ chainSet (b :: l) := by
        rw [show cseg (a :: b :: l) 1 = cseg (b :: l) 0 from cseg_cons_succ _ _ _] at hy2
        exact cseg_subset_chainSet (b :: l) 0 (by simpa using hj) hy2
      have h1 : y ∈ segment ℝ a b ∩ chainSet (b :: l) := ⟨by simpa [cseg] using hy1, h2⟩
      rw [hc.2.1] at h1
      simpa using h1
  | a :: b :: l, hc, i + 1, j, hij, hj => by
    subst hij
    rw [cseg_cons_succ, cseg_cons_succ]
    simpa using hc.2.2.cseg_inter i (i + 1) rfl (by simpa using hj)

/-- **Non-neighbouring segments of a simple chain are disjoint.** -/
lemma IsSimpleChain.cseg_disjoint : ∀ {c : List (ℝ × ℝ)}, IsSimpleChain c → ∀ i j, i + 2 ≤ j →
    j + 1 < c.length → Disjoint (cseg c i) (cseg c j)
  | [], _, i, j, _, h => by simp at h
  | [_], _, i, j, _, h => by simp at h
  | a :: b :: l, hc, 0, j + 1, hij, hj => by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    have hj' : 1 ≤ j := by omega
    rw [cseg_cons_succ] at hy2
    have hlen : j + 1 < (b :: l).length := by simpa using hj
    have h2 : y ∈ chainSet (b :: l) := cseg_subset_chainSet (b :: l) j hlen hy2
    have h1 : y ∈ segment ℝ a b ∩ chainSet (b :: l) := ⟨by simpa [cseg] using hy1, h2⟩
    rw [hc.2.1] at h1
    have hyb : y = b := by simpa using h1
    subst hyb
    have hb0 : y ∈ cseg (y :: l) 0 := by simpa [cseg] using left_mem_segment ℝ y ((y :: l).getD 1 0)
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have hj1 : j = 1 := by omega
      subst hj1
      have := hc.2.2.cseg_inter 0 1 rfl hlen
      have hmem : y ∈ cseg (y :: l) 0 ∩ cseg (y :: l) 1 := ⟨hb0, hy2⟩
      rw [this] at hmem
      exact hc.2.2.getD_ne 0 (by have := hlen; simp only [List.length_cons] at this ⊢; omega) (by simpa using hmem)
    · exact Set.disjoint_left.1 (hc.2.2.cseg_disjoint 0 j (by omega) hlen) hb0 hy2
  | a :: b :: l, hc, i + 1, j + 1, hij, hj => by
    rw [cseg_cons_succ, cseg_cons_succ]
    exact hc.2.2.cseg_disjoint i j (by omega) (by simpa using hj)

/-- **A closed simple chain is a simple polygon.** -/
theorem isSimple_ofList {l : List (ℝ × ℝ)} {a b : ℝ × ℝ} (h3 : 3 ≤ (a :: l ++ [b]).length)
    (hc : IsSimpleChain (a :: l ++ [b])) (hab : a ≠ b)
    (hcl : segment ℝ b a ∩ chainSet (a :: l ++ [b]) = {a, b}) :
    (Polygon.ofList (a :: l ++ [b])).IsSimple := by
  sorry

end Lightlike.PL
