import Mathlib

/-!
# The boundary graph of a pinch-free set of lattice squares

Row G3-188, milestone PL5 (third pass), item 5b, route A.  A set `S` of unit squares of the integer
lattice (the square indexed by `(x, y)` has lower-left corner `(x, y)`).  The *boundary graph* `bdGraph S`
has as vertices the lattice points and as edges the unit lattice edges that separate a square of `S`
from a square not in `S`.  If `S` has no *pinch* (a vertex where two diagonal squares are in `S` and the
other two are not), every vertex has degree `0` or `2`, so the graph is a disjoint union of cycles
(`bdGraph_isCycles`).

* `HB S x y`, `VB S x y`: the horizontal edge from `(x,y)` to `(x+1,y)`, resp. the vertical edge from
  `(x,y)` to `(x,y+1)`, is a boundary edge.
* `NoPinch S`: no pinch.
* `bdGraph S`: the boundary graph; `bdGraph_isCycles`: it consists of cycles.
-/

namespace Lightlike.PL.Schoenflies

open Set

variable (S : Set (ℤ × ℤ))

/-- The horizontal lattice edge from `(x,y)` to `(x+1,y)` separates exactly one square of `S`
(the squares are the one above, with corner `(x,y)`, and the one below, with corner `(x,y-1)`). -/
def HB (x y : ℤ) : Prop :=
  ((x, y) ∈ S ∧ (x, y - 1) ∉ S) ∨ ((x, y - 1) ∈ S ∧ (x, y) ∉ S)

/-- The vertical lattice edge from `(x,y)` to `(x,y+1)` separates exactly one square of `S`
(the squares are the one to the right, with corner `(x,y)`, and the one to the left, `(x-1,y)`). -/
def VB (x y : ℤ) : Prop :=
  ((x, y) ∈ S ∧ (x - 1, y) ∉ S) ∨ ((x - 1, y) ∈ S ∧ (x, y) ∉ S)

/-- `S` has **no pinch**: at no lattice vertex are two diagonal squares in `S` and the other two not. -/
def NoPinch : Prop :=
  ∀ x y : ℤ, ¬ ((x, y) ∈ S ∧ (x - 1, y - 1) ∈ S ∧ (x - 1, y) ∉ S ∧ (x, y - 1) ∉ S) ∧
    ¬ ((x, y) ∉ S ∧ (x - 1, y - 1) ∉ S ∧ (x - 1, y) ∈ S ∧ (x, y - 1) ∈ S)

/-- Adjacency in the boundary graph. -/
def BdAdj (v w : ℤ × ℤ) : Prop :=
  (w.1 = v.1 + 1 ∧ w.2 = v.2 ∧ HB S v.1 v.2) ∨ (v.1 = w.1 + 1 ∧ v.2 = w.2 ∧ HB S w.1 w.2) ∨
  (w.1 = v.1 ∧ w.2 = v.2 + 1 ∧ VB S v.1 v.2) ∨ (v.1 = w.1 ∧ v.2 = w.2 + 1 ∧ VB S w.1 w.2)

/-- The **boundary graph** of a set of lattice squares. -/
def bdGraph : SimpleGraph (ℤ × ℤ) where
  Adj := BdAdj S
  symm := ⟨fun v w h => by
    unfold BdAdj at h ⊢
    tauto⟩
  loopless := ⟨fun v h => by
    unfold BdAdj at h
    omega⟩

/-- The four possible neighbours of `(x,y)` in the boundary graph. -/
lemma bdAdj_iff (x y a b : ℤ) : BdAdj S (x, y) (a, b) ↔
    (a = x + 1 ∧ b = y ∧ HB S x y) ∨ (a = x - 1 ∧ b = y ∧ HB S (x - 1) y) ∨
    (a = x ∧ b = y + 1 ∧ VB S x y) ∨ (a = x ∧ b = y - 1 ∧ VB S x (y - 1)) := by
  unfold BdAdj
  simp only
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h1, h2, h3⟩
    · have e1 : a = x - 1 := by omega
      have e2 : b = y := by omega
      subst e1 e2
      exact Or.inr (Or.inl ⟨rfl, rfl, h3⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))
    · have e1 : a = x := by omega
      have e2 : b = y - 1 := by omega
      subst e1 e2
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h3⟩))
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h1, h2, h3⟩
    · subst h1 h2
      exact Or.inr (Or.inl ⟨by omega, rfl, h3⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))
    · subst h1 h2
      exact Or.inr (Or.inr (Or.inr ⟨rfl, by omega, h3⟩))

/-- **The boundary graph of a pinch-free set consists of cycles**: every vertex of positive degree has
degree exactly two. -/
theorem bdGraph_isCycles (hS : NoPinch S) : (bdGraph S).IsCycles := by
  rintro ⟨x, y⟩ ⟨⟨a, b⟩, hw⟩
  have hw' : BdAdj S (x, y) (a, b) := hw
  rw [bdAdj_iff] at hw'
  rw [Set.ncard_eq_two]
  have hset : (bdGraph S).neighborSet (x, y) = {w : ℤ × ℤ |
      (w.1 = x + 1 ∧ w.2 = y ∧ HB S x y) ∨ (w.1 = x - 1 ∧ w.2 = y ∧ HB S (x - 1) y) ∨
      (w.1 = x ∧ w.2 = y + 1 ∧ VB S x y) ∨ (w.1 = x ∧ w.2 = y - 1 ∧ VB S x (y - 1))} := by
    ext ⟨a', b'⟩
    exact bdAdj_iff S x y a' b'
  rw [hset]
  have hp := hS x y
  by_cases ha : (x, y) ∈ S <;> by_cases hb : (x - 1, y) ∈ S <;> by_cases hc : (x - 1, y - 1) ∈ S <;>
    by_cases hd : (x, y - 1) ∈ S <;>
    simp only [HB, VB, ha, hb, hc, hd, not_true_eq_false, not_false_eq_true, and_true,
      and_false, or_false, false_or] at hp hw' ⊢
  all_goals
    first
    | (refine ⟨(x + 1, y), (x - 1, y), by simp only [ne_eq, Prod.mk.injEq, not_and]; omega, ?_⟩
       ext ⟨a', b'⟩
       simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
       try omega
       done)
    | (refine ⟨(x + 1, y), (x, y + 1), by simp only [ne_eq, Prod.mk.injEq, not_and]; omega, ?_⟩
       ext ⟨a', b'⟩
       simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
       try omega
       done)
    | (refine ⟨(x + 1, y), (x, y - 1), by simp only [ne_eq, Prod.mk.injEq, not_and]; omega, ?_⟩
       ext ⟨a', b'⟩
       simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
       try omega
       done)
    | (refine ⟨(x - 1, y), (x, y + 1), by simp only [ne_eq, Prod.mk.injEq, not_and]; omega, ?_⟩
       ext ⟨a', b'⟩
       simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
       try omega
       done)
    | (refine ⟨(x - 1, y), (x, y - 1), by simp only [ne_eq, Prod.mk.injEq, not_and]; omega, ?_⟩
       ext ⟨a', b'⟩
       simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
       try omega
       done)
    | (refine ⟨(x, y + 1), (x, y - 1), by simp only [ne_eq, Prod.mk.injEq, not_and]; omega, ?_⟩
       ext ⟨a', b'⟩
       simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
       try omega
       done)

end Lightlike.PL.Schoenflies
