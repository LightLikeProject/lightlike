import Mathlib
import Lightlike.PL.Schoenflies.ChordSplit
import Lightlike.PL.Schoenflies.GlueHomeo
import Lightlike.PL.Schoenflies.RegionCompact

/-!
# Gluing homeomorphisms of the two pieces of a chord split

For a simple polygon `C` cut along a polygonal chord into `L` and `R` (`region_split_chain`), two
homeomorphisms of the closed regions `region L`, `region R` that agree on the chord, and whose
images overlap only over the chord, glue to a homeomorphism of `region C`.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL

/-- **Gluing along a chord.**  With the hypotheses of `region_split_chain`, homeomorphisms
`e₁ : region L ≃ₜ A'`, `e₂ : region R ≃ₜ B'` that agree on the chord and whose images meet only in the
image of the chord, give a homeomorphism `region C ≃ₜ A' ∪ B'` restricting to `e₁` and `e₂`. -/
theorem region_split_homeo {a b : ℝ × ℝ} {m₁ m₂ mₑ : List (ℝ × ℝ)} (hab : a ≠ b)
    (h₁ : IsSimpleChain (a :: m₁ ++ [b])) (h₂ : IsSimpleChain (b :: m₂ ++ [a]))
    (hₑ : IsSimpleChain (a :: mₑ ++ [b]))
    (h₁₂ : chainSet (a :: m₁ ++ [b]) ∩ chainSet (b :: m₂ ++ [a]) = {a, b})
    (h₁ₑ : chainSet (a :: m₁ ++ [b]) ∩ chainSet (a :: mₑ ++ [b]) = {a, b})
    (h₂ₑ : chainSet (b :: m₂ ++ [a]) ∩ chainSet (a :: mₑ ++ [b]) = {a, b})
    (hD : chainSet (a :: mₑ ++ [b]) \ {a, b} ⊆ (Polygon.ofList (a :: m₁ ++ b :: m₂)).inside)
    {A' B' : Set (ℝ × ℝ)}
    (e₁ : region (Polygon.ofList (a :: m₁ ++ b :: mₑ.reverse)) ≃ₜ A')
    (e₂ : region (Polygon.ofList (b :: m₂ ++ a :: mₑ)) ≃ₜ B')
    (h : ∀ (x : ℝ × ℝ) (hxA : x ∈ region (Polygon.ofList (a :: m₁ ++ b :: mₑ.reverse)))
      (hxB : x ∈ region (Polygon.ofList (b :: m₂ ++ a :: mₑ))),
      (e₁ ⟨x, hxA⟩ : ℝ × ℝ) = e₂ ⟨x, hxB⟩)
    (hAB : ∀ y, y ∈ A' → y ∈ B' → ∃ (x : ℝ × ℝ)
      (_ : x ∈ region (Polygon.ofList (a :: m₁ ++ b :: mₑ.reverse)))
      (hxB : x ∈ region (Polygon.ofList (b :: m₂ ++ a :: mₑ))), (e₂ ⟨x, hxB⟩ : ℝ × ℝ) = y) :
    ∃ E : region (Polygon.ofList (a :: m₁ ++ b :: m₂)) ≃ₜ (A' ∪ B' : Set (ℝ × ℝ)),
      (∀ (x : ℝ × ℝ) (hx : x ∈ region (Polygon.ofList (a :: m₁ ++ b :: mₑ.reverse))),
        (E ⟨x, (region_split_chain hab h₁ h₂ hₑ h₁₂ h₁ₑ h₂ₑ hD).1 ▸ Or.inl hx⟩ : ℝ × ℝ)
          = e₁ ⟨x, hx⟩) ∧
      (∀ (x : ℝ × ℝ) (hx : x ∈ region (Polygon.ofList (b :: m₂ ++ a :: mₑ))),
        (E ⟨x, (region_split_chain hab h₁ h₂ hₑ h₁₂ h₁ₑ h₂ₑ hD).1 ▸ Or.inr hx⟩ : ℝ × ℝ)
          = e₂ ⟨x, hx⟩) := by
  classical
  obtain ⟨hU, -⟩ := region_split_chain hab h₁ h₂ hₑ h₁₂ h₁ₑ h₂ₑ hD
  have hrev : (a :: mₑ ++ [b]).reverse = b :: mₑ.reverse ++ [a] := by simp
  have hEr : IsSimpleChain (b :: mₑ.reverse ++ [a]) := hrev ▸ isSimpleChain_reverse hₑ
  have hEs : chainSet (b :: mₑ.reverse ++ [a]) = chainSet (a :: mₑ ++ [b]) := by
    rw [← hrev, chainSet_reverse]
  have iL : NeZero (a :: m₁ ++ b :: mₑ.reverse).length := ⟨by simp⟩
  have iR : NeZero (b :: m₂ ++ a :: mₑ).length := ⟨by simp⟩
  have sL := isSimple_two_arcs h₁ hEr (by rw [hEs]; exact h₁ₑ) hab
  have sR := isSimple_two_arcs (a := b) (b := a) h₂ hₑ (by rw [Set.pair_comm]; exact h₂ₑ) hab.symm
  obtain ⟨hU', hI⟩ := region_split_chain hab h₁ h₂ hₑ h₁₂ h₁ₑ h₂ₑ hD
  obtain ⟨E₀, hE₁, hE₂⟩ := exists_homeo_union_glue (isCompact_region sL) (isCompact_region sR) e₁ e₂
    h hAB
  exact ⟨(Homeomorph.setCongr hU').trans E₀, fun x hx => hE₁ x hx, fun x hx => hE₂ x hx⟩

end Lightlike.PL.Schoenflies
