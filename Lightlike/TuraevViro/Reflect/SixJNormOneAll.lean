import Lightlike.TuraevViro.Reflect.QDougallAll

/-!
# Norm one of the q-6j matrix at every level

`sixj_norm_one` gives norm one of every row and column of the q-6j matrix, given the boundary
evaluation `QDougall` at the lowest colours. The range hypotheses of `sixj_norm_one` say that `x0` and
`x0 + 2 n` are the lowest and the highest common admissible colour and that `q0` is the lowest
sixth colour, so the boundary evaluation is `QDougallAt`, which `qDougallAll_proved` proves at every
level.

## Main results

* `range_eq`: the range hypotheses force `x0 = aLo` and `x0 + 2 n = aHi`.
* `sixj_norm_one_proved`: **norm one of the q-6j matrix at every level `r ≥ 2`**, without hypothesis.
-/

namespace Lightlike.TV.Refl
open Finset Lightlike.TV

/-- The lowest and the highest colour of a progression of common admissible colours, given by the
range hypotheses of `sixj_norm_one`, are `aLo` and `aHi`. -/
theorem range_eq {r : ℕ} (hr : 2 ≤ r) {a b c d x0 n : ℕ}
    (hadm : ∀ k ≤ n, qAdm r a b (x0 + 2 * k) ∧ qAdm r c d (x0 + 2 * k))
    (hlo : (x0 : ℤ) < (a : ℤ) - b + 2 ∨ (x0 : ℤ) < (b : ℤ) - a + 2 ∨
      (x0 : ℤ) < (c : ℤ) - d + 2 ∨ (x0 : ℤ) < (d : ℤ) - c + 2)
    (hhi : (a : ℤ) + b < (x0 + 2 * n : ℕ) + 2 ∨ (c : ℤ) + d < (x0 + 2 * n : ℕ) + 2 ∨
      (2 * r : ℤ) - 2 ≤ (a : ℤ) + b + ((x0 + 2 * n : ℕ) + 2) ∨
      (2 * r : ℤ) - 2 ≤ (c : ℤ) + d + ((x0 + 2 * n : ℕ) + 2)) :
    x0 = aLo a b c d ∧ x0 + 2 * n = aHi r a b c d := by
  have h0 := hadm 0 (Nat.zero_le _)
  have hn := hadm n le_rfl
  have g0 := h0
  have gn := hn
  unfold qAdm Lightlike.Pentagon.Tri at g0 gn
  have hpar : (a + b + c + d) % 2 = 0 := by omega
  have hab : a + b ≤ 2 * (r - 2) := by omega
  have hcd : c + d ≤ 2 * (r - 2) := by omega
  have iff := adm_pair_iff hr hpar
  have i0 := (iff (x0 + 2 * 0)).1 h0
  have in' := (iff (x0 + 2 * n)).1 hn
  obtain ⟨p1, p2, -, -, -⟩ := pair_facts (r := r) hpar hab hcd
  obtain ⟨l1, l2, l3, l4, -⟩ := aLo_spec a b c d
  obtain ⟨u1, u2, u3, u4, -⟩ := aHi_spec r a b c d
  clear iff g0 gn h0 hn hadm
  rcases hlo with hlo | hlo | hlo | hlo <;> rcases hhi with hhi | hhi | hhi | hhi <;>
    refine ⟨?_, ?_⟩ <;> omega


/-- **Norm one of the q-6j matrix at every level.** `sixj_norm_one` without its hypothesis
`QDougall`, which `qDougallAll_proved` supplies: the range hypotheses force `x0 = aLo`,
`x0 + 2 n = aHi` and `q0 = aLo`, so the boundary evaluation is `QDougallAt`. -/
theorem sixj_norm_one_proved {r : ℕ} (hr : 2 ≤ r) (j1 j2 j4 j5 x0 n q0 m : ℕ)
    (hadmX : ∀ k ≤ n, qAdm r j1 j2 (x0 + 2 * k) ∧ qAdm r j4 j5 (x0 + 2 * k))
    (hloX : (x0 : ℤ) < (j1 : ℤ) - j2 + 2 ∨ (x0 : ℤ) < (j2 : ℤ) - j1 + 2 ∨
      (x0 : ℤ) < (j4 : ℤ) - j5 + 2 ∨ (x0 : ℤ) < (j5 : ℤ) - j4 + 2)
    (hhiX : (j1 : ℤ) + j2 < (x0 + 2 * n : ℕ) + 2 ∨ (j4 : ℤ) + j5 < (x0 + 2 * n : ℕ) + 2 ∨
      (2 * r : ℤ) - 2 ≤ (j1 : ℤ) + j2 + ((x0 + 2 * n : ℕ) + 2) ∨
      (2 * r : ℤ) - 2 ≤ (j4 : ℤ) + j5 + ((x0 + 2 * n : ℕ) + 2))
    (hadmQ : ∀ l ≤ m, qAdm r j1 j5 (q0 + 2 * l) ∧ qAdm r j4 j2 (q0 + 2 * l))
    (hloQ : (q0 : ℤ) < (j1 : ℤ) - j5 + 2 ∨ (q0 : ℤ) < (j5 : ℤ) - j1 + 2 ∨
      (q0 : ℤ) < (j4 : ℤ) - j2 + 2 ∨ (q0 : ℤ) < (j2 : ℤ) - j4 + 2)
    (hhiQ : (j1 : ℤ) + j5 < (q0 + 2 * m : ℕ) + 2 ∨ (j4 : ℤ) + j2 < (q0 + 2 * m : ℕ) + 2 ∨
      (2 * r : ℤ) - 2 ≤ (j1 : ℤ) + j5 + ((q0 + 2 * m : ℕ) + 2) ∨
      (2 * r : ℤ) - 2 ≤ (j4 : ℤ) + j2 + ((q0 + 2 * m : ℕ) + 2))
    (heqX : (x0 : ℤ) = (j1 : ℤ) - j2 ∨ (x0 : ℤ) = (j2 : ℤ) - j1 ∨ (x0 : ℤ) = (j4 : ℤ) - j5 ∨
      (x0 : ℤ) = (j5 : ℤ) - j4)
    (heqQ : (q0 : ℤ) = (j1 : ℤ) - j5 ∨ (q0 : ℤ) = (j5 : ℤ) - j1 ∨ (q0 : ℤ) = (j4 : ℤ) - j2 ∨
      (q0 : ℤ) = (j2 : ℤ) - j4) :
    (∀ l ≤ m, jOmega r j1 j5 j4 j2 (q0 + 2 * l) *
        (∑ k ∈ range (n + 1), jOmega r j1 j2 j4 j5 (x0 + 2 * k) *
          Sj r j1 j2 j4 j5 (q0 + 2 * l) ((x0 + 2 * k : ℕ) : ℤ) ^ 2) = 1) ∧
      (∀ k ≤ n, jOmega r j1 j2 j4 j5 (x0 + 2 * k) *
        (∑ l ∈ range (m + 1), jOmega r j1 j5 j4 j2 (q0 + 2 * l) *
          Sj r j1 j2 j4 j5 (q0 + 2 * l) ((x0 + 2 * k : ℕ) : ℤ) ^ 2) = 1) := by
  obtain ⟨hx0, hn⟩ := range_eq hr hadmX hloX hhiX
  obtain ⟨hq0, -⟩ := range_eq hr hadmQ hloQ hhiQ
  have hD : QDougall r j1 j2 j4 j5 x0 n q0 := by
    have hq1 := (hadmQ 0 (Nat.zero_le _)).1
    have hq2 := (hadmQ 0 (Nat.zero_le _)).2
    simp only [mul_zero, add_zero] at hq1 hq2
    have h := qDougallAll_proved hr j1 j2 j4 j5 q0 hq1 hq2
    unfold QDougallAt at h
    rw [← hx0, ← hq0] at h
    have hn' : (aHi r j1 j2 j4 j5 - x0) / 2 = n := by omega
    rw [hn'] at h
    exact h
  exact sixj_norm_one hr j1 j2 j4 j5 x0 n q0 m hadmX hloX hhiX hadmQ hloQ hhiQ heqX heqQ hD

end Lightlike.TV.Refl
