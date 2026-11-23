import Lightlike.PL.Schoenflies.LatticeGraph

/-!
# The unit squares of a union of inflated grid squares have no pinch

Row G3-188, milestone PL5 (third pass), item 5b, route A.  Measured in units of `δ / 4`, the grid square
`q` of mesh `δ` inflated by `δ / 4` (`Lightlike.PL.Schoenflies.box`) is the union of the unit squares
`(s₁, s₂)` with `4 q₁ - 1 ≤ s₁ ≤ 4 q₁ + 4` and `4 q₂ - 1 ≤ s₂ ≤ 4 q₂ + 4`.  For any finite family of grid
squares the set of unit squares in the union has no pinch (`noPinch_sqSet`), whatever the connectivity of
the family: two inflated squares either overlap in a `2 × 2` block of unit squares or are two units apart.

* `boxSq q`: the unit squares of the inflated square `q`.
* `sqSet F`: the unit squares of the union over a finite set `F` of grid squares.
* `sqSet_finite`, `noPinch_sqSet`.
-/

namespace Lightlike.PL.Schoenflies

open Set

/-- The unit squares (indexed by lower-left corner, in units of `δ / 4`) of the inflated grid square `q`. -/
def boxSq (q : ℤ × ℤ) : Set (ℤ × ℤ) :=
  Icc (4 * q.1 - 1) (4 * q.1 + 4) ×ˢ Icc (4 * q.2 - 1) (4 * q.2 + 4)

/-- The unit squares of the union of the inflated grid squares of `F`. -/
def sqSet (F : Finset (ℤ × ℤ)) : Set (ℤ × ℤ) := ⋃ q ∈ F, boxSq q

lemma mem_boxSq {q s : ℤ × ℤ} :
    s ∈ boxSq q ↔ 4 * q.1 - 1 ≤ s.1 ∧ s.1 ≤ 4 * q.1 + 4 ∧ 4 * q.2 - 1 ≤ s.2 ∧ s.2 ≤ 4 * q.2 + 4 := by
  simp only [boxSq, Set.mem_prod, Set.mem_Icc]
  tauto

lemma mem_sqSet {F : Finset (ℤ × ℤ)} {s : ℤ × ℤ} : s ∈ sqSet F ↔ ∃ q ∈ F, s ∈ boxSq q := by
  simp [sqSet]

/-- The unit squares of a finite union of inflated grid squares form a finite set. -/
lemma sqSet_finite (F : Finset (ℤ × ℤ)) : (sqSet F).Finite :=
  Set.Finite.biUnion F.finite_toSet (fun _ _ => (Set.finite_Icc _ _).prod (Set.finite_Icc _ _))

/-- **No pinch.** The unit squares of a finite union of inflated grid squares have no pinch. -/
theorem noPinch_sqSet (F : Finset (ℤ × ℤ)) : NoPinch (sqSet F) := by
  intro x y
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨q, hq, hqm⟩ := mem_sqSet.1 h1
    obtain ⟨q', hq', hqm'⟩ := mem_sqSet.1 h2
    have n1 : (x - 1, y) ∉ boxSq q := fun h => h3 (mem_sqSet.2 ⟨q, hq, h⟩)
    have n2 : (x - 1, y) ∉ boxSq q' := fun h => h3 (mem_sqSet.2 ⟨q', hq', h⟩)
    have n3 : (x, y - 1) ∉ boxSq q := fun h => h4 (mem_sqSet.2 ⟨q, hq, h⟩)
    have n4 : (x, y - 1) ∉ boxSq q' := fun h => h4 (mem_sqSet.2 ⟨q', hq', h⟩)
    simp only [mem_boxSq] at hqm hqm' n1 n2 n3 n4
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨q, hq, hqm⟩ := mem_sqSet.1 h3
    obtain ⟨q', hq', hqm'⟩ := mem_sqSet.1 h4
    have n1 : (x, y) ∉ boxSq q := fun h => h1 (mem_sqSet.2 ⟨q, hq, h⟩)
    have n2 : (x, y) ∉ boxSq q' := fun h => h1 (mem_sqSet.2 ⟨q', hq', h⟩)
    have n3 : (x - 1, y - 1) ∉ boxSq q := fun h => h2 (mem_sqSet.2 ⟨q, hq, h⟩)
    have n4 : (x - 1, y - 1) ∉ boxSq q' := fun h => h2 (mem_sqSet.2 ⟨q', hq', h⟩)
    simp only [mem_boxSq] at hqm hqm' n1 n2 n3 n4
    omega

end Lightlike.PL.Schoenflies
