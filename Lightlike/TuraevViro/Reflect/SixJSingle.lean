import Lightlike.TuraevViro.Reflect.SixJRow

/-!
# One-term q-Racah sums at the lowest sixth colour

When the sixth colour `q` of the 6j tuple is `j₁ - j₅`, `j₅ - j₁`, `j₄ - j₂` or `j₂ - j₄`, one of the
upper limits of the q-Racah sum equals one of the lower limits. The sum then has exactly one term.
This is the first step of the closed form of the boundary evaluation: at the lowest sixth colour the
square of the 6j symbol is a product of quantum factorials.
-/

namespace Lightlike.TV.Refl

open Lightlike.TV Finset

/-- A q-Racah sum in which an upper limit `b₂` or `b₃` equals a lower limit `a₁` or `a₄` has the single
term `z = a₁` (respectively `a₄`). -/
lemma SR_single {r : ℕ} {a1 a2 a3 a4 b1 b2 b3 : ℤ} (z0 : ℕ)
    (hlow : (z0 : ℤ) = a1 ∨ (z0 : ℤ) = a4)
    (hhigh : (z0 : ℤ) = b2 ∨ (z0 : ℤ) = b3) (hz : (z0 : ℤ) ≤ b1) :
    SR r a1 a2 a3 a4 b1 b2 b3 = qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z0 := by
  unfold SR
  refine Finset.sum_eq_single_of_mem z0 (Finset.mem_range.2 (by omega)) ?_
  intro z _ hne
  rcases lt_or_gt_of_ne hne with h | h
  · apply qRacahTerm_zero_of_lt
    rcases hlow with e | e
    · left; omega
    · right; right; right; omega
  · rcases hhigh with e | e
    · exact qRacahTerm_zero_of_gt2 (by omega)
    · exact qRacahTerm_zero_of_gt3 (by omega)

/-- **One-term sum at the lowest sixth colour.** If `q` is `j₁ - j₅`, `j₅ - j₁`, `j₄ - j₂` or
`j₂ - j₄`, then `Sj` is a single summand of the q-Racah formula. -/
lemma Sj_single (r j1 j2 j4 j5 q : ℕ) (y : ℤ) (hy : 0 ≤ y)
    (hyA : y ≤ (j1 : ℤ) + j2) (hyB : y ≤ (j4 : ℤ) + j5)
    (hq : (q : ℤ) = (j1 : ℤ) - j5 ∨ (q : ℤ) = (j5 : ℤ) - j1 ∨
      (q : ℤ) = (j4 : ℤ) - j2 ∨ (q : ℤ) = (j2 : ℤ) - j4) :
    ∃ z0 : ℕ, Sj r j1 j2 j4 j5 q y =
      qRacahTerm r (((j1 : ℤ) + j2 + y) / 2) (((j1 : ℤ) + j5 + q) / 2) (((j4 : ℤ) + j2 + q) / 2)
        (((j4 : ℤ) + j5 + y) / 2) (((j1 : ℤ) + j2 + j4 + j5) / 2) ((y + j2 + j5 + q) / 2)
        ((y + j1 + q + j4) / 2) z0 := by
  unfold Sj
  rcases hq with h | h | h | h
  · refine ⟨(((j1 : ℤ) + j2 + y) / 2).toNat, SR_single _ (Or.inl ?_) (Or.inl ?_) ?_⟩ <;> omega
  · refine ⟨(((j4 : ℤ) + j5 + y) / 2).toNat, SR_single _ (Or.inr ?_) (Or.inr ?_) ?_⟩ <;> omega
  · refine ⟨(((j4 : ℤ) + j5 + y) / 2).toNat, SR_single _ (Or.inr ?_) (Or.inl ?_) ?_⟩ <;> omega
  · refine ⟨(((j1 : ℤ) + j2 + y) / 2).toNat, SR_single _ (Or.inl ?_) (Or.inr ?_) ?_⟩ <;> omega

end Lightlike.TV.Refl
