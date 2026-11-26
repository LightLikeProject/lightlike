import Mathlib
import Lightlike.PL.Schoenflies.ChordSplit
import Lightlike.PL.Schoenflies.InsideBox2

/-!
# Which side of a chord a connected set lies on

Row G3-188 (PL5), ring cells.  `split_side_of_big`: in the splitting of a simple polygon along a chord
(`inside_split_chain`), a preconnected subset of the inside that misses the chord lies in the inside of one of the two
parts; if the first part has its carrier in a square and the set is not contained in the square, it lies in the second.
-/

open Set

namespace Lightlike.PL.Schoenflies

open Lightlike.PL

theorem split_side_of_big {a b : ℝ × ℝ} {m₁ m₂ mₑ : List (ℝ × ℝ)} (hab : a ≠ b)
    (h₁ : IsSimpleChain (a :: m₁ ++ [b])) (h₂ : IsSimpleChain (b :: m₂ ++ [a]))
    (hₑ : IsSimpleChain (a :: mₑ ++ [b]))
    (h₁₂ : chainSet (a :: m₁ ++ [b]) ∩ chainSet (b :: m₂ ++ [a]) = {a, b})
    (h₁ₑ : chainSet (a :: m₁ ++ [b]) ∩ chainSet (a :: mₑ ++ [b]) = {a, b})
    (h₂ₑ : chainSet (b :: m₂ ++ [a]) ∩ chainSet (a :: mₑ ++ [b]) = {a, b})
    (hD : chainSet (a :: mₑ ++ [b]) \ {a, b} ⊆ (Polygon.ofList (a :: m₁ ++ b :: m₂)).inside)
    {S : Set (ℝ × ℝ)} (hS : IsPreconnected S) (hSC : S ⊆ (Polygon.ofList (a :: m₁ ++ b :: m₂)).inside)
    (hSE : Disjoint S (chainSet (a :: mₑ ++ [b]))) {c : ℝ × ℝ} {R : ℝ}
    (hcar : (Polygon.ofList (a :: m₁ ++ b :: mₑ.reverse)).carrier ⊆ sqBox c R) (hbig : ¬ S ⊆ sqBox c R) :
    S ⊆ (Polygon.ofList (b :: m₂ ++ a :: mₑ)).inside := by
  obtain ⟨hdisj, hin⟩ := inside_split_chain hab h₁ h₂ hₑ h₁₂ h₁ₑ h₂ₑ hD
  have hcov : S ⊆ (Polygon.ofList (a :: m₁ ++ b :: mₑ.reverse)).inside ∪
      (Polygon.ofList (b :: m₂ ++ a :: mₑ)).inside := by
    intro z hz
    have hz' := hSC hz
    rw [hin] at hz'
    rcases hz' with (h | h) | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (h.1) (Set.disjoint_left.1 hSE hz)
  rcases hS.subset_or_subset (Polygon.isOpen_inside _) (Polygon.isOpen_inside _) hdisj hcov with hL | hR
  · exact absurd (hL.trans (inside_subset_sqBox _ hcar)) hbig
  · exact hR

/-- The same with the roles of the two parts exchanged: if the second part has its carrier in a square and the set
is not contained in the square, it lies in the inside of the first part. -/
theorem split_side_of_big' {a b : ℝ × ℝ} {m₁ m₂ mₑ : List (ℝ × ℝ)} (hab : a ≠ b)
    (h₁ : IsSimpleChain (a :: m₁ ++ [b])) (h₂ : IsSimpleChain (b :: m₂ ++ [a]))
    (hₑ : IsSimpleChain (a :: mₑ ++ [b]))
    (h₁₂ : chainSet (a :: m₁ ++ [b]) ∩ chainSet (b :: m₂ ++ [a]) = {a, b})
    (h₁ₑ : chainSet (a :: m₁ ++ [b]) ∩ chainSet (a :: mₑ ++ [b]) = {a, b})
    (h₂ₑ : chainSet (b :: m₂ ++ [a]) ∩ chainSet (a :: mₑ ++ [b]) = {a, b})
    (hD : chainSet (a :: mₑ ++ [b]) \ {a, b} ⊆ (Polygon.ofList (a :: m₁ ++ b :: m₂)).inside)
    {S : Set (ℝ × ℝ)} (hS : IsPreconnected S) (hSC : S ⊆ (Polygon.ofList (a :: m₁ ++ b :: m₂)).inside)
    (hSE : Disjoint S (chainSet (a :: mₑ ++ [b]))) {c : ℝ × ℝ} {R : ℝ}
    (hcar : (Polygon.ofList (b :: m₂ ++ a :: mₑ)).carrier ⊆ sqBox c R) (hbig : ¬ S ⊆ sqBox c R) :
    S ⊆ (Polygon.ofList (a :: m₁ ++ b :: mₑ.reverse)).inside := by
  obtain ⟨hdisj, hin⟩ := inside_split_chain hab h₁ h₂ hₑ h₁₂ h₁ₑ h₂ₑ hD
  have hcov : S ⊆ (Polygon.ofList (a :: m₁ ++ b :: mₑ.reverse)).inside ∪
      (Polygon.ofList (b :: m₂ ++ a :: mₑ)).inside := by
    intro z hz
    have hz' := hSC hz
    rw [hin] at hz'
    rcases hz' with (h | h) | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (h.1) (Set.disjoint_left.1 hSE hz)
  rcases hS.subset_or_subset (Polygon.isOpen_inside _) (Polygon.isOpen_inside _) hdisj hcov with hL | hR
  · exact hL
  · exact absurd (hR.trans (inside_subset_sqBox _ hcar)) hbig

end Lightlike.PL.Schoenflies
