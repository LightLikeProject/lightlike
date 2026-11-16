import Mathlib

/-!
# Two orthogonality relations force a common norm

Let `P k l` be a matrix with `Σ_k wk k · P k l · P k l' = 0` for `l ≠ l'` and
`Σ_l wl l · P k l · P k' l = 0` for `k ≠ k'`. Then `wl l · N l = wk k · M k` whenever `P k l ≠ 0`,
where `N l = Σ_k wk k · P k l²` and `M k = Σ_l wl l · P k l²`.
-/

namespace Lightlike.TV.Refl

open Finset

/-- If two weighted Gram matrices are diagonal, the weighted row and column norms are one common constant. -/
theorem gram_const (P : ℕ → ℕ → ℝ) (wk wl : ℕ → ℝ) (n m : ℕ)
    (hX : ∀ l ≤ m, ∀ l' ≤ m, l ≠ l' → ∑ k ∈ range (n + 1), wk k * P k l * P k l' = 0)
    (hQ : ∀ k ≤ n, ∀ k' ≤ n, k ≠ k' → ∑ l ∈ range (m + 1), wl l * P k l * P k' l = 0)
    {k l : ℕ} (hk : k ≤ n) (hl : l ≤ m) (hP : P k l ≠ 0) :
    wl l * (∑ k' ∈ range (n + 1), wk k' * P k' l ^ 2) =
      wk k * (∑ l' ∈ range (m + 1), wl l' * P k l' ^ 2) := by
  have e1 : ∑ k' ∈ range (n + 1), ∑ l' ∈ range (m + 1),
      P k l' * wl l' * P k' l' * wk k' * P k' l
      = P k l * (wl l * ∑ k' ∈ range (n + 1), wk k' * P k' l ^ 2) := by
    rw [Finset.sum_comm]
    have : ∀ l' ∈ range (m + 1), ∑ k' ∈ range (n + 1), P k l' * wl l' * P k' l' * wk k' * P k' l
        = P k l' * wl l' * (∑ k' ∈ range (n + 1), wk k' * P k' l' * P k' l) := by
      intro l' _
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k' _ => by ring
    rw [Finset.sum_congr rfl this]
    rw [Finset.sum_eq_single l]
    · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k' _ => by ring
    · intro l' hl' hne
      rw [hX l' (by simpa [Nat.lt_succ_iff] using hl') l hl hne, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have e2 : ∑ k' ∈ range (n + 1), ∑ l' ∈ range (m + 1),
      P k l' * wl l' * P k' l' * wk k' * P k' l
      = P k l * (wk k * ∑ l' ∈ range (m + 1), wl l' * P k l' ^ 2) := by
    have : ∀ k' ∈ range (n + 1), ∑ l' ∈ range (m + 1), P k l' * wl l' * P k' l' * wk k' * P k' l
        = wk k' * P k' l * (∑ l' ∈ range (m + 1), wl l' * P k l' * P k' l') := by
      intro k' _
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l' _ => by ring
    rw [Finset.sum_congr rfl this]
    rw [Finset.sum_eq_single k]
    · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l' _ => by ring
    · intro k' hk' hne
      rw [hQ k hk k' (by simpa [Nat.lt_succ_iff] using hk') (Ne.symm hne), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  exact mul_left_cancel₀ hP (e1.symm.trans e2)

end Lightlike.TV.Refl
