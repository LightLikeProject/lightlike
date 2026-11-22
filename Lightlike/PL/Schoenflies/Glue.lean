import Mathlib

/-!
# Gluing bijections on two pieces

A map that is bijective from `A` onto `A'` and from `B` onto `B'` is bijective from `A ∪ B` onto
`A' ∪ B'` provided the images overlap only over the overlap: `A' ∩ B' ⊆ f '' (A ∩ B)`.
Used for the ear induction of the polygonal Schoenflies theorem, where a polygon region is a
smaller region glued to a triangle along a diagonal.
-/

namespace Lightlike.PL.Schoenflies

open Set

/-- Gluing of two bijections: `f` bijective `A → A'` and `B → B'`, and `A' ∩ B'` is the image of
`A ∩ B`, give a bijection `A ∪ B → A' ∪ B'`. -/
lemma bijOn_union_glue {α β : Type*} {f : α → β} {A B : Set α} {A' B' : Set β}
    (hA : BijOn f A A') (hB : BijOn f B B') (hAB : A' ∩ B' ⊆ f '' (A ∩ B)) :
    BijOn f (A ∪ B) (A' ∪ B') := by
  refine ⟨hA.mapsTo.union_union hB.mapsTo, ?_, ?_⟩
  · rintro x (hx | hx) y (hy | hy) hxy
    · exact hA.injOn hx hy hxy
    · obtain ⟨z, ⟨hzA, hzB⟩, hz⟩ := hAB ⟨hA.mapsTo hx, hxy ▸ hB.mapsTo hy⟩
      have h1 : x = z := hA.injOn hx hzA (hz.symm)
      have h2 : y = z := hB.injOn hy hzB (hxy.symm.trans hz.symm)
      rw [h1, h2]
    · obtain ⟨z, ⟨hzA, hzB⟩, hz⟩ := hAB ⟨hxy ▸ hA.mapsTo hy, hB.mapsTo hx⟩
      have h1 : y = z := hA.injOn hy hzA (hxy.symm.trans hz.symm)
      have h2 : x = z := hB.injOn hx hzB hz.symm
      rw [h1, h2]
    · exact hB.injOn hx hy hxy
  · rintro y (hy | hy)
    · obtain ⟨x, hx, rfl⟩ := hA.surjOn hy
      exact ⟨x, Or.inl hx, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := hB.surjOn hy
      exact ⟨x, Or.inr hx, rfl⟩

/-- A different map on the second piece breaks the hypothesis: the overlap condition is needed.
Two maps `ℕ → ℕ` that are bijective on `{0}` and `{1}` onto `{0}` but overlap wrongly are not
glued bijectively (trust check: the conclusion fails without `hAB`). -/
example : ¬ BijOn (fun _ : ℕ => 0) ({0} ∪ {1}) ({0} ∪ {0}) := by
  intro h
  have := h.injOn (Or.inl rfl) (Or.inr rfl) rfl
  exact absurd this (by decide)

end Lightlike.PL.Schoenflies
