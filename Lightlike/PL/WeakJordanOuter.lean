import Lightlike.PL.WeakJordanT

/-!
# The outer arc of the weak Jordan theorem

If `a` and `b` are the highest and lowest points of a compact set `K`, there is a simple chain from `a`
to `b` that meets `K` only at `a` and `b`, goes round `K` on the right, and has no point strictly
between the heights of `a` and `b` to the left of the vertical line through a bound of `K`.

## Main results

* `exists_outer`: the chain (Klazar, arXiv:2604.04296, Section 2, Claim 4: "f₂ starts with a vertical
  segment going up from `a`, then goes horizontally sufficiently far to the right, goes vertically
  down to a level below `b_y`, continues horizontally left just below `b`, and closes by going
  vertically up to `b`").
-/

open Set

namespace Lightlike.PL

lemma mem_seg_coords {a b z : ℝ × ℝ} (h : z ∈ segment ℝ a b) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z.1 = a.1 + s * (b.1 - a.1) ∧ z.2 = a.2 + s * (b.2 - a.2) := by
  rw [segment_eq_image'] at h
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := h
  exact ⟨s, hs0, hs1, by simp, by simp⟩

/-- **The outer arc.** -/
theorem exists_outer {K : Set (ℝ × ℝ)} {a b : ℝ × ℝ} {X : ℝ} (hab : b.2 < a.2)
    (hK2 : ∀ z ∈ K, b.2 ≤ z.2 ∧ z.2 ≤ a.2) (hKx : ∀ z ∈ K, z.1 < X) (ha : a ∈ K) (hb : b ∈ K) :
    ∃ l : List (ℝ × ℝ), IsSimpleChain l ∧ l.head? = some a ∧ l.getLast? = some b ∧
      chainSet l ∩ K ⊆ {a, b} ∧
      ∀ z ∈ chainSet l, ¬ (b.2 < z.2 ∧ z.2 < a.2 ∧ z.1 < X) := by
  have hXa : a.1 < X := hKx a ha
  have hXb : b.1 < X := hKx b hb
  set p₁ : ℝ × ℝ := (a.1, a.2 + 1)
  set p₂ : ℝ × ℝ := (X, a.2 + 1)
  set p₃ : ℝ × ℝ := (X, b.2 - 1)
  set p₄ : ℝ × ℝ := (b.1, b.2 - 1)
  obtain ⟨l, hl, h1, h2, h3⟩ := exists_simple_sub [a, p₁, p₂, p₃, p₄, b] a b rfl rfl
  have hset : chainSet [a, p₁, p₂, p₃, p₄, b] = segment ℝ a p₁ ∪ segment ℝ p₁ p₂ ∪ segment ℝ p₂ p₃ ∪
      segment ℝ p₃ p₄ ∪ segment ℝ p₄ b := by
    ext z
    simp only [chainSet, mem_union, mem_singleton_iff]
    constructor
    · rintro (h | h | h | h | h | rfl)
      · tauto
      · tauto
      · tauto
      · tauto
      · tauto
      · exact Or.inr (right_mem_segment ℝ _ _)
    · rintro (((( h | h) | h) | h) | h)
      · tauto
      · tauto
      · tauto
      · tauto
      · tauto
  -- the facts about each segment
  have hseg : ∀ z ∈ chainSet [a, p₁, p₂, p₃, p₄, b],
      (z.2 ≤ a.2 → z ∈ K → z = a ∨ z = b) ∧ ¬ (b.2 < z.2 ∧ z.2 < a.2 ∧ z.1 < X) := by
    intro z hz
    rw [hset] at hz
    rcases hz with (((h | h) | h) | h) | h
    · obtain ⟨t, ht0, ht1, e1, e2⟩ := mem_seg_coords h
      simp only [p₁] at e1 e2
      refine ⟨fun h1 _ => Or.inl (Prod.ext (by linarith) (by nlinarith)), fun hh => by nlinarith [hh.2.1]⟩
    · obtain ⟨t, ht0, ht1, e1, e2⟩ := mem_seg_coords h
      simp only [p₁, p₂] at e1 e2
      refine ⟨fun h1 _ => by linarith, fun hh => by linarith [hh.2.1]⟩
    · obtain ⟨t, ht0, ht1, e1, e2⟩ := mem_seg_coords h
      simp only [p₂, p₃] at e1 e2
      refine ⟨fun _ hzK => absurd (hKx z hzK) (by linarith), fun hh => by linarith [hh.2.2]⟩
    · obtain ⟨t, ht0, ht1, e1, e2⟩ := mem_seg_coords h
      simp only [p₃, p₄] at e1 e2
      refine ⟨fun _ hzK => absurd (hK2 z hzK).1 (by linarith), fun hh => by linarith [hh.1]⟩
    · obtain ⟨t, ht0, ht1, e1, e2⟩ := mem_seg_coords h
      simp only [p₄] at e1 e2
      refine ⟨fun _ hzK => Or.inr (Prod.ext (by linarith) (by nlinarith [(hK2 z hzK).1])),
        fun hh => by linarith [hh.1, ht1]⟩
  refine ⟨l, hl, h1, h2, fun z ⟨hz, hzK⟩ => ?_, fun z hz => (hseg z (h3 hz)).2⟩
  have hz' := h3 hz
  have := (hseg z hz').1 (hK2 z hzK).2 hzK
  simpa using this

end Lightlike.PL
