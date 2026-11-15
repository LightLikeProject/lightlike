import Lightlike.PL.SliceSwap
import Lightlike.PL.Projective

/-!
# Checks for the slicing walk and the radial map

A cut edge has `0`-sphere boundaries on both sides, so the sphere hypotheses of the cut swap must
admit `n = 0`. The check below runs the order-complex cut swap on the face poset of the sets
`{0}, {1}, {0,1}` (an edge `a` with endpoints `p`, `q`) and `{2}, {0,2}, {1,2}` (the cut point `z`
and the two new edges `u`, `v`), where the sphere hypotheses hold with `n = 0`.

The radial map with centre `0` and scale `x ↦ x.1` of the plane sends the segment from `(1, 0)` to
`(2, 2)` onto the segment from `(1, 0)` to `(1, 1)`, and it does not preserve midpoints, so it is
projective and not affine (`projMap_not_affine`).
-/

open Finset

namespace Lightlike.PL
namespace SComplex

/-- The order complex of two incomparable elements is the boundary of the pair. -/
lemma orderComplex_pair_eq_boundary {P : Type*} [PartialOrder P] [DecidableEq P] {a b : P}
    (hab : ¬ a ≤ b) (hba : ¬ b ≤ a) : orderComplex ({a, b} : Finset P) = boundary {a, b} := by
  have hne : a ≠ b := fun h => hab (h ▸ le_rfl)
  refine ext_mem fun s => ?_
  rw [mem_orderComplex, mem_boundary]
  constructor
  · rintro ⟨hs, hch⟩
    refine ⟨hs, fun hsup => ?_⟩
    have ha : a ∈ s := hsup (by simp)
    have hb : b ∈ s := hsup (by simp)
    rcases hch a ha b hb with h | h
    · exact hab h
    · exact hba h
  · intro hs
    refine ⟨hs.1, fun x hx y hy => ?_⟩
    by_cases hxy : x = y
    · exact .inl hxy.le
    · exfalso
      have hx' := hs.1 hx
      have hy' := hs.1 hy
      simp only [mem_insert, mem_singleton] at hx' hy'
      apply hs.2
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
      · exact absurd rfl hxy
      · rcases hz with rfl | rfl <;> assumption
      · rcases hz with rfl | rfl <;> assumption
      · exact absurd rfl hxy

/-- The endpoints `p`, `q` of the edge `a`, the cut point `z` and the new edges `u`, `v`. -/
abbrev cutEdgeP : Finset ℕ := {0}
/-- See `cutEdgeP`. -/
abbrev cutEdgeQ : Finset ℕ := {1}
/-- See `cutEdgeP`. -/
abbrev cutEdgeA : Finset ℕ := {0, 1}
/-- See `cutEdgeP`. -/
abbrev cutEdgeZ : Finset ℕ := {2}
/-- See `cutEdgeP`. -/
abbrev cutEdgeU : Finset ℕ := {0, 2}
/-- See `cutEdgeP`. -/
abbrev cutEdgeV : Finset ℕ := {1, 2}

/-- **A cut edge: the sphere hypotheses of the cut swap hold with `n = 0`.** The path
`p - a - q` is exchanged for the path `p - u - z - v - q`. -/
theorem cutEdge_example : StellarEquivIn
    ((orderComplex (∅ : Finset (Finset ℕ))).union
      ((orderComplex (insert cutEdgeA ({cutEdgeP, cutEdgeQ} : Finset (Finset ℕ)))).join
        (orderComplex (∅ : Finset (Finset ℕ)))))
    ((orderComplex (∅ : Finset (Finset ℕ))).union
      ((orderComplex (insert cutEdgeU (insert cutEdgeV (insert cutEdgeZ
        ({cutEdgeP, cutEdgeQ} : Finset (Finset ℕ)))))).join
        (orderComplex (∅ : Finset (Finset ℕ))))) := by
  classical
  refine stellarEquivIn_order_cut (n := 0) (L := ({cutEdgeP, cutEdgeQ} : Finset (Finset ℕ)))
    (Up := ∅) (Rest := ∅) (a := cutEdgeA) (u := cutEdgeU) (v := cutEdgeV) (z := cutEdgeZ)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_ ?_ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  · have e : ∀ S : Finset (Finset ℕ), S = {cutEdgeZ, cutEdgeP} → IsSB false (0 + 1) (orderComplex S) := by
      rintro S rfl
      rw [orderComplex_pair_eq_boundary (by decide) (by decide)]
      exact .inl ⟨{cutEdgeZ, cutEdgeP}, by decide, StellarEquivIn.refl _⟩
    refine e _ ?_
    ext x
    simp only [mem_insert, mem_filter, mem_singleton]
    constructor
    · rintro (h | ⟨h | h, hlt⟩)
      · exact .inl h
      · exact .inr h
      · exfalso; subst h; exact absurd hlt (by decide)
    · rintro (h | h)
      · exact .inl h
      · exact .inr ⟨.inl h, by subst h; decide⟩
  · have e : ∀ S : Finset (Finset ℕ), S = {cutEdgeZ, cutEdgeQ} → IsSB false (0 + 1) (orderComplex S) := by
      rintro S rfl
      rw [orderComplex_pair_eq_boundary (by decide) (by decide)]
      exact .inl ⟨{cutEdgeZ, cutEdgeQ}, by decide, StellarEquivIn.refl _⟩
    refine e _ ?_
    ext x
    simp only [mem_insert, mem_filter, mem_singleton]
    constructor
    · rintro (h | ⟨h | h, hlt⟩)
      · exact .inl h
      · exfalso; subst h; exact absurd hlt (by decide)
      · exact .inr h
    · rintro (h | h)
      · exact .inl h
      · exact .inr ⟨.inr h, by subst h; decide⟩

/-- The radial map with centre `0` and scale `x ↦ x.1` sends `(2, 2)` to `(1, 1)` and the midpoint
`(3/2, 1)` of the segment from `(1, 0)` to `(2, 2)` to `(1, 2/3)`, which is not the midpoint
`(1, 1/2)` of the image segment: the map is projective, not affine. -/
theorem projMap_not_affine :
    projMap (0 : ℝ × ℝ) (fun x => x.1) (2, 2) = (1, 1) ∧
    projMap (0 : ℝ × ℝ) (fun x => x.1) (3 / 2, 1) = (1, 2 / 3) ∧
    projMap (0 : ℝ × ℝ) (fun x => x.1) (3 / 2, 1) ≠
      (1 / 2 : ℝ) • projMap (0 : ℝ × ℝ) (fun x => x.1) (1, 0) +
        (1 / 2 : ℝ) • projMap (0 : ℝ × ℝ) (fun x => x.1) (2, 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [projMap, zero_add, sub_zero, Prod.smul_mk, smul_eq_mul]
  · ext <;> norm_num
  · ext <;> norm_num
  · intro h
    have := congrArg Prod.snd h
    norm_num at this

end SComplex
end Lightlike.PL
