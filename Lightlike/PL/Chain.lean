import Lightlike.PL.PolygonSplit

/-!
# Parity of the crossings of a polygonal chain

A polygonal chain is a list of points; the parity of a chain at `x` counts, modulo two, the segments
between consecutive points that the horizontal ray to the right of `x` crosses. It is additive when
chains are glued end to end, and it does not change when a chain is reversed, because the
crossing test does not depend on the direction of a segment (`crossesRay_symm`). Consequently a
chain followed by its reverse has parity zero.

## Main results

* `Lightlike.PL.chainParity`
* `Lightlike.PL.chainParity_append`: gluing at a shared endpoint
* `Lightlike.PL.chainParity_reverse`
-/

namespace Lightlike.PL

/-- The parity of the number of segments of the chain crossed by the horizontal ray to the right
of `x`. -/
noncomputable def chainParity (x : ℝ × ℝ) : List (ℝ × ℝ) → ZMod 2
  | a :: b :: l => ind (CrossesRay a b x) + chainParity x (b :: l)
  | _ => 0

lemma chainParity_nil (x : ℝ × ℝ) : chainParity x [] = 0 := rfl
lemma chainParity_singleton (x a : ℝ × ℝ) : chainParity x [a] = 0 := rfl
lemma chainParity_cons_cons (x a b : ℝ × ℝ) (l : List (ℝ × ℝ)) :
    chainParity x (a :: b :: l) = ind (CrossesRay a b x) + chainParity x (b :: l) := rfl

/-- **Gluing chains at a shared endpoint adds their parities.** -/
lemma chainParity_append (x : ℝ × ℝ) (l₁ : List (ℝ × ℝ)) (b : ℝ × ℝ) (l₂ : List (ℝ × ℝ)) :
    chainParity x (l₁ ++ b :: l₂) = chainParity x (l₁ ++ [b]) + chainParity x (b :: l₂) := by
  induction l₁ with
  | nil => simp [chainParity_singleton]
  | cons a l ih =>
    cases l with
    | nil => simp [chainParity_cons_cons, chainParity_singleton]
    | cons c l' =>
      simp only [List.cons_append] at ih ⊢
      rw [chainParity_cons_cons, chainParity_cons_cons, ih, add_assoc]

/-- **A chain and its reverse have the same parity.** -/
lemma chainParity_reverse (x : ℝ × ℝ) (l : List (ℝ × ℝ)) :
    chainParity x l.reverse = chainParity x l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l' =>
      have e : (a :: b :: l').reverse = l'.reverse ++ b :: [a] := by simp
      have ih' : chainParity x (l'.reverse ++ [b]) = chainParity x (b :: l') := by
        simpa using ih
      rw [e, chainParity_append, ih', chainParity_cons_cons x b a [], chainParity_singleton,
        add_zero, chainParity_cons_cons x a b l', add_comm]
      congr 1
      exact Polygon.ind_congr (crossesRay_symm _ _ _)

/-- **A chain followed by its reverse has parity zero.** -/
lemma chainParity_append_reverse (x : ℝ × ℝ) (l : List (ℝ × ℝ)) (b : ℝ × ℝ) :
    chainParity x (l ++ b :: l.reverse) = 0 := by
  rw [chainParity_append]
  have : b :: l.reverse = (l ++ [b]).reverse := by simp
  rw [this, chainParity_reverse]
  exact CharTwo.add_self_eq_zero _

end Lightlike.PL
