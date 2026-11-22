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

/-- Gluing of two different maps that agree on the overlap: the map equal to `g` on `B` and to `f`
elsewhere restricts to `f` on `A` and to `g` on `B`, and is bijective `A ∪ B → A' ∪ B'`. This is
the ear step: `f` is the map of the smaller region, `g` the triangle map of the ear. -/
lemma exists_bijOn_union_glue {α β : Type*} {f g : α → β} {A B : Set α} {A' B' : Set β}
    (hA : BijOn f A A') (hB : BijOn g B B') (hfg : EqOn f g (A ∩ B))
    (hAB : A' ∩ B' ⊆ g '' (A ∩ B)) :
    ∃ F : α → β, BijOn F (A ∪ B) (A' ∪ B') ∧ EqOn F f A ∧ EqOn F g B := by
  classical
  let F : α → β := fun x => if x ∈ B then g x else f x
  have hFB : EqOn F g B := fun x hx => by simp [F, hx]
  have hFA : EqOn F f A := fun x hx => by
    by_cases h : x ∈ B
    · simp [F, h, (hfg ⟨hx, h⟩).symm]
    · simp [F, h]
  refine ⟨F, ?_, hFA, hFB⟩
  have hA' : BijOn F A A' := hA.congr hFA.symm
  have hB' : BijOn F B B' := hB.congr hFB.symm
  refine bijOn_union_glue hA' hB' ?_
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hAB hy
  exact ⟨z, hz, hFB hz.2⟩

/-- A different map on the second piece breaks the hypothesis: the overlap condition is needed.
Two maps `ℕ → ℕ` that are bijective on `{0}` and `{1}` onto `{0}` but overlap wrongly are not
glued bijectively (trust check: the conclusion fails without `hAB`). -/
example : ¬ BijOn (fun _ : ℕ => 0) ({0} ∪ {1}) ({0} ∪ {0}) := by
  intro h
  have := h.injOn (Or.inl rfl) (Or.inr rfl) rfl
  exact absurd this (by decide)

end Lightlike.PL.Schoenflies
