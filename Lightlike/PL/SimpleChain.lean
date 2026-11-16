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

/-- **A reversed simple chain is simple.** -/
theorem isSimpleChain_reverse {l : List (ℝ × ℝ)} (h : IsSimpleChain l) :
    IsSimpleChain l.reverse := by
  sorry

/-- **A closed simple chain is a simple polygon.** -/
theorem isSimple_ofList {l : List (ℝ × ℝ)} {a b : ℝ × ℝ} (h3 : 3 ≤ (a :: l ++ [b]).length)
    (hc : IsSimpleChain (a :: l ++ [b])) (hab : a ≠ b)
    (hcl : segment ℝ b a ∩ chainSet (a :: l ++ [b]) = {a, b}) :
    (Polygon.ofList (a :: l ++ [b])).IsSimple := by
  sorry

end Lightlike.PL
