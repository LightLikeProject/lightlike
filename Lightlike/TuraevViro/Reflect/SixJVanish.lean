import Lightlike.TuraevViro.Reflect.RacahReal

/-!
# Vanishing of the real q-Racah sum outside its natural range

`SR` is zero when the box `max aᵢ ≤ z ≤ min βⱼ` is empty (a violated triangle inequality of a 6j
symbol) and when some `aᵢ ≥ r - 1` (the quantum factorial `[z+1]!` of every term vanishes).
-/

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

open Lightlike.TV Finset

lemma qfact_eq_zero_of_ge {r : ℕ} (hr : 2 ≤ r) {n : ℕ} (hn : r ≤ n) : qfact r n = 0 := by
  unfold qfact
  exact Finset.prod_eq_zero (i := r - 1) (Finset.mem_range.mpr (by omega))
    (by rw [show r - 1 + 1 = r by omega]; exact qnum_self hr)

lemma qRacahTerm_zero_of_gt2 {r : ℕ} {a1 a2 a3 a4 b1 b2 b3 : ℤ} {z : ℕ} (h : b2 < (z : ℤ)) :
    qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z = 0 := by
  unfold qRacahTerm
  have : invQFact r (b2 - z) = 0 := by
    simp only [invQFact, show ¬ (0 ≤ b2 - (z : ℤ)) by omega, ↓reduceIte]
  simp [this]

lemma qRacahTerm_zero_of_gt3 {r : ℕ} {a1 a2 a3 a4 b1 b2 b3 : ℤ} {z : ℕ} (h : b3 < (z : ℤ)) :
    qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z = 0 := by
  unfold qRacahTerm
  have : invQFact r (b3 - z) = 0 := by
    simp only [invQFact, show ¬ (0 ≤ b3 - (z : ℤ)) by omega, ↓reduceIte]
  simp [this]

lemma qRacahTerm_zero_of_big {r : ℕ} (hr : 2 ≤ r) {a1 a2 a3 a4 b1 b2 b3 : ℤ} {z : ℕ}
    (h : r ≤ z + 1) : qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z = 0 := by
  unfold qRacahTerm
  simp [qfact_eq_zero_of_ge hr h]

/-- `SR` vanishes when the summation box is empty. -/
lemma SR_eq_zero_of_empty {r : ℕ} {a1 a2 a3 a4 b1 b2 b3 : ℤ}
    (h : ∀ z : ℤ, ¬ (a1 ≤ z ∧ a2 ≤ z ∧ a3 ≤ z ∧ a4 ≤ z ∧ z ≤ b1 ∧ z ≤ b2 ∧ z ≤ b3)) :
    SR r a1 a2 a3 a4 b1 b2 b3 = 0 := by
  unfold SR
  refine Finset.sum_eq_zero fun z _ => ?_
  have hz := h z
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
  exact absurd ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩ hz

/-- `SR` vanishes when some `aᵢ ≥ r - 1`. -/
lemma SR_eq_zero_of_big {r : ℕ} (hr : 2 ≤ r) {a1 a2 a3 a4 b1 b2 b3 : ℤ}
    (h : (r : ℤ) - 1 ≤ a1 ∨ (r : ℤ) - 1 ≤ a2 ∨ (r : ℤ) - 1 ≤ a3 ∨ (r : ℤ) - 1 ≤ a4) :
    SR r a1 a2 a3 a4 b1 b2 b3 = 0 := by
  unfold SR
  refine Finset.sum_eq_zero fun z _ => ?_
  by_cases c1 : (z : ℤ) < a1
  · exact qRacahTerm_zero_of_lt (Or.inl c1)
  by_cases c2 : (z : ℤ) < a2
  · exact qRacahTerm_zero_of_lt (Or.inr (Or.inl c2))
  by_cases c3 : (z : ℤ) < a3
  · exact qRacahTerm_zero_of_lt (Or.inr (Or.inr (Or.inl c3)))
  by_cases c4 : (z : ℤ) < a4
  · exact qRacahTerm_zero_of_lt (Or.inr (Or.inr (Or.inr c4)))
  exact qRacahTerm_zero_of_big hr (by omega)

end Lightlike.TV.Refl
