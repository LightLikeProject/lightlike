import Lightlike.TuraevViro.Reflect.SixJDual
import Lightlike.TuraevViro.Reflect.SixJEnd
import Lightlike.TuraevViro.Reflect.GramConst

/-!
# The norms of the q-6j sums are a single constant

For fixed `j₁, j₂, j₄, j₅` the matrix `P_{xq} = Sj_q(x)` over the admissible third and sixth
colours has orthogonal columns for the weight of the third colour (`sixj_offdiag`) and orthogonal
rows for the weight of the sixth colour (`sixj_offdiag_dual`). The first row and the first column
of `P` have no zero entry, because the sum at the lowest colour is a single term (`Sj_low_ne`).
Hence the weighted squared norms of all columns, and of all rows, equal one constant `c`.
-/


namespace Lightlike.TV.Refl

open Lightlike.TV Finset

/-- The weighted norms of all rows and all columns of the matrix of 6j sums are one common constant. -/
theorem sixj_norm_const {r : ℕ} (hr : 2 ≤ r) (j1 j2 j4 j5 x0 n q0 m : ℕ)
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
    ∃ c : ℝ,
      (∀ l ≤ m, jOmega r j1 j5 j4 j2 (q0 + 2 * l) *
        (∑ k ∈ range (n + 1), jOmega r j1 j2 j4 j5 (x0 + 2 * k) *
          Sj r j1 j2 j4 j5 (q0 + 2 * l) ((x0 + 2 * k : ℕ) : ℤ) ^ 2) = c) ∧
      (∀ k ≤ n, jOmega r j1 j2 j4 j5 (x0 + 2 * k) *
        (∑ l ∈ range (m + 1), jOmega r j1 j5 j4 j2 (q0 + 2 * l) *
          Sj r j1 j2 j4 j5 (q0 + 2 * l) ((x0 + 2 * k : ℕ) : ℤ) ^ 2) = c) := by
  set P : ℕ → ℕ → ℝ := fun k l => Sj r j1 j2 j4 j5 (q0 + 2 * l) ((x0 + 2 * k : ℕ) : ℤ) with hP
  have hX : ∀ l ≤ m, ∀ l' ≤ m, l ≠ l' →
      ∑ k ∈ range (n + 1), jOmega r j1 j2 j4 j5 (x0 + 2 * k) * P k l * P k l' = 0 := by
    intro l hl l' hl' hne
    have e1 := (hadmQ l hl).1
    have e2 := (hadmQ l' hl').1
    unfold qAdm Lightlike.Pentagon.Tri at e1 e2
    exact sixj_offdiag hr j1 j2 j4 j5 x0 n hadmX hloX hhiX (hadmQ l hl).1 (hadmQ l hl).2
      (hadmQ l' hl').1 (hadmQ l' hl').2 (by omega) (by omega) (by omega)
  have hQ : ∀ k ≤ n, ∀ k' ≤ n, k ≠ k' →
      ∑ l ∈ range (m + 1), jOmega r j1 j5 j4 j2 (q0 + 2 * l) * P k l * P k' l = 0 := by
    intro k hk k' hk' hne
    have e1 := (hadmX k hk).1
    have e2 := (hadmX k' hk').1
    unfold qAdm Lightlike.Pentagon.Tri at e1 e2
    exact sixj_offdiag_dual hr j1 j2 j4 j5 q0 m hadmQ hloQ hhiQ (hadmX k hk).1
      (hadmX k hk).2 (hadmX k' hk').1 (hadmX k' hk').2 (by omega) (by omega) (by omega)
  have hrow : ∀ l ≤ m, P 0 l ≠ 0 := by
    intro l hl
    have := Sj_low_ne hr j1 j2 j4 j5 (q0 + 2 * l) x0 (hadmX 0 (Nat.zero_le _)).1
      (hadmX 0 (Nat.zero_le _)).2 (hadmQ l hl).1 (hadmQ l hl).2 heqX
    simpa [hP] using this
  have hcol : ∀ k ≤ n, P k 0 ≠ 0 := by
    intro k hk
    have := Sj_low_ne hr j1 j5 j4 j2 (x0 + 2 * k) q0 (hadmQ 0 (Nat.zero_le _)).1
      (hadmQ 0 (Nat.zero_le _)).2 (hadmX k hk).1 (hadmX k hk).2 heqQ
    have h2 := Sj_dual r j1 j2 j4 j5 (q0 + 2 * 0) (x0 + 2 * k)
    simp only [hP]
    rw [h2]
    simpa using this
  have key := fun k l (hk : k ≤ n) (hl : l ≤ m) (h : P k l ≠ 0) =>
    gram_const P (fun k => jOmega r j1 j2 j4 j5 (x0 + 2 * k))
      (fun l => jOmega r j1 j5 j4 j2 (q0 + 2 * l)) n m hX hQ hk hl h
  refine ⟨jOmega r j1 j2 j4 j5 (x0 + 2 * 0) *
    (∑ l ∈ range (m + 1), jOmega r j1 j5 j4 j2 (q0 + 2 * l) * P 0 l ^ 2), ?_, ?_⟩
  · intro l hl
    exact key 0 l (Nat.zero_le _) hl (hrow l hl)
  · intro k hk
    have h1 := key k 0 hk (Nat.zero_le _) (hcol k hk)
    have h2 := key 0 0 (Nat.zero_le _) (Nat.zero_le _) (hrow 0 (Nat.zero_le _))
    simp only [Nat.mul_zero, Nat.add_zero] at h1 h2 ⊢
    exact h1.symm.trans h2

end Lightlike.TV.Refl
