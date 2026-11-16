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

/-- **Gluing simple chains at a shared endpoint.** -/
theorem isSimpleChain_append {l₁ l₂ : List (ℝ × ℝ)} {b : ℝ × ℝ}
    (h₁ : IsSimpleChain (l₁ ++ [b])) (h₂ : IsSimpleChain (b :: l₂))
    (hd : chainSet (l₁ ++ [b]) ∩ chainSet (b :: l₂) = {b}) :
    IsSimpleChain (l₁ ++ b :: l₂) := by
  sorry

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
