import Lightlike.TuraevViro.Reflect.SixJVanish
import Lightlike.TuraevViro.Reflect.SixJRow

/-!
# Single-term q-Racah sums

When the summation box of `SR` is a single point, the sum is one term, and that term is nonzero
if every quantum factorial in it has an argument below `r`. This is the case at the ends of the
range of a colour of a 6j symbol.
-/


namespace Lightlike.TV.Refl

open Lightlike.TV Finset

lemma qRacahTerm_zero_of_out {r : ℕ} {a1 a2 a3 a4 b1 b2 b3 : ℤ} {z : ℕ}
    (h : ¬ (a1 ≤ z ∧ a2 ≤ z ∧ a3 ≤ z ∧ a4 ≤ z ∧ (z : ℤ) ≤ b1 ∧ (z : ℤ) ≤ b2 ∧ (z : ℤ) ≤ b3)) :
    qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z = 0 := by
  by_cases c1 : (z : ℤ) < a1
  · exact qRacahTerm_zero_of_lt (Or.inl c1)
  by_cases c2 : (z : ℤ) < a2
  · exact qRacahTerm_zero_of_lt (Or.inr (Or.inl c2))
  by_cases c3 : (z : ℤ) < a3
  · exact qRacahTerm_zero_of_lt (Or.inr (Or.inr (Or.inl c3)))
  by_cases c4 : (z : ℤ) < a4
  · exact qRacahTerm_zero_of_lt (Or.inr (Or.inr (Or.inr c4)))
  by_cases d1 : b1 < (z : ℤ)
  · exact qRacahTerm_zero_of_gt d1
  by_cases d2 : b2 < (z : ℤ)
  · exact qRacahTerm_zero_of_gt2 d2
  by_cases d3 : b3 < (z : ℤ)
  · exact qRacahTerm_zero_of_gt3 d3
  exact absurd ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩ h

lemma invQFact_pos {r : ℕ} (hr : 2 ≤ r) {u : ℤ} (h0 : 0 ≤ u) (h1 : u < r) : 0 < invQFact r u := by
  unfold invQFact
  simp only [h0, ↓reduceIte]
  exact inv_pos.mpr (qfact_pos hr (by omega))

/-- A single-term `SR` is nonzero when all quantum factorials of the term are nonzero. -/
lemma SR_single_ne {r : ℕ} (hr : 2 ≤ r) {a1 a2 a3 a4 b1 b2 b3 : ℤ} (z0 : ℕ)
    (hout : ∀ z : ℕ, z ≠ z0 →
      ¬ (a1 ≤ z ∧ a2 ≤ z ∧ a3 ≤ z ∧ a4 ≤ z ∧ (z : ℤ) ≤ b1 ∧ (z : ℤ) ≤ b2 ∧ (z : ℤ) ≤ b3))
    (hin : a1 ≤ z0 ∧ a2 ≤ z0 ∧ a3 ≤ z0 ∧ a4 ≤ z0 ∧ (z0 : ℤ) ≤ b1 ∧ (z0 : ℤ) ≤ b2 ∧ (z0 : ℤ) ≤ b3)
    (hr0 : z0 + 1 < r)
    (hd : (z0 : ℤ) - a1 < r ∧ (z0 : ℤ) - a2 < r ∧ (z0 : ℤ) - a3 < r ∧ (z0 : ℤ) - a4 < r ∧
      b1 - z0 < r ∧ b2 - z0 < r ∧ b3 - z0 < r) :
    SR r a1 a2 a3 a4 b1 b2 b3 ≠ 0 := by
  unfold SR
  rw [Finset.sum_eq_single z0 (fun z _ hz => qRacahTerm_zero_of_out (hout z hz))
    (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
  obtain ⟨i1, i2, i3, i4, j1, j2, j3⟩ := hin
  obtain ⟨e1, e2, e3, e4, f1, f2, f3⟩ := hd
  unfold qRacahTerm
  have := qfact_pos hr (by omega : z0 + 1 < r)
  have p1 := invQFact_pos hr (by omega : 0 ≤ (z0 : ℤ) - a1) e1
  have p2 := invQFact_pos hr (by omega : 0 ≤ (z0 : ℤ) - a2) e2
  have p3 := invQFact_pos hr (by omega : 0 ≤ (z0 : ℤ) - a3) e3
  have p4 := invQFact_pos hr (by omega : 0 ≤ (z0 : ℤ) - a4) e4
  have q1 := invQFact_pos hr (by omega : 0 ≤ b1 - (z0 : ℤ)) f1
  have q2 := invQFact_pos hr (by omega : 0 ≤ b2 - (z0 : ℤ)) f2
  have q3 := invQFact_pos hr (by omega : 0 ≤ b3 - (z0 : ℤ)) f3
  have : (-1 : ℝ) ^ z0 ≠ 0 := pow_ne_zero _ (by norm_num)
  positivity

/-- **The sum at the lowest third colour is a single nonzero term.** -/
lemma Sj_low_ne {r : ℕ} (hr : 2 ≤ r) (j1 j2 j4 j5 q x0 : ℕ) (h1 : qAdm r j1 j2 x0)
    (h4 : qAdm r j4 j5 x0) (h2 : qAdm r j1 j5 q) (h3 : qAdm r j4 j2 q)
    (heq : (x0 : ℤ) = (j1 : ℤ) - j2 ∨ (x0 : ℤ) = (j2 : ℤ) - j1 ∨ (x0 : ℤ) = (j4 : ℤ) - j5 ∨
      (x0 : ℤ) = (j5 : ℤ) - j4) :
    Sj r j1 j2 j4 j5 q (x0 : ℤ) ≠ 0 := by
  unfold qAdm Lightlike.Pentagon.Tri at h1 h4 h2 h3
  unfold Sj
  rcases heq with h | h | h | h
  · exact SR_single_ne hr (((j1 + j5 + q) / 2 : ℕ)) (by intro z hz; omega) (by omega) (by omega)
      (by omega)
  · exact SR_single_ne hr (((j4 + j2 + q) / 2 : ℕ)) (by intro z hz; omega) (by omega) (by omega)
      (by omega)
  · exact SR_single_ne hr (((j4 + j2 + q) / 2 : ℕ)) (by intro z hz; omega) (by omega) (by omega)
      (by omega)
  · exact SR_single_ne hr (((j1 + j5 + q) / 2 : ℕ)) (by intro z hz; omega) (by omega) (by omega)
      (by omega)

end Lightlike.TV.Refl
