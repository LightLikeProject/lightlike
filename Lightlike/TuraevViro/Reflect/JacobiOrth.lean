import Mathlib

/-!
# Orthogonality of eigenvectors of a weighted three-term recurrence

A finite Jacobi-type recurrence `a k * v (k+1) + b k * v k + c k * v (k-1) = λ * v k` on the indices
`0, …, n`, with weights `ω` satisfying detailed balance `ω k * a k = ω (k+1) * c (k+1)` and with the
two boundary coefficients `c 0` and `a n` zero, has weighted-orthogonal eigenvectors for
different eigenvalues. This is the abstract algebra behind the orthogonality of the quantum 6j
symbols in one of their colours.
-/

open Finset

namespace Lightlike.TV.Refl

variable {R : Type*} [CommRing R] {a b c ω v w : ℕ → R} {lam mu : R}

/-- Shifting the lower-diagonal sum by one index turns it into the upper-diagonal sum. -/
lemma jacobi_shift (n : ℕ) (a c ω v w : ℕ → R) (hdb : ∀ k < n, ω k * a k = ω (k + 1) * c (k + 1))
    (hc0 : c 0 = 0) (han : a n = 0) :
    ∑ k ∈ range (n + 1), ω k * c k * v (k - 1) * w k
      = ∑ k ∈ range (n + 1), ω k * a k * v k * w (k + 1) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ _ n]
  simp only [hc0, han, mul_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n := Finset.mem_range.mp hk
  have := hdb k hk'
  simp only [Nat.add_sub_cancel]
  calc ω (k + 1) * c (k + 1) * v k * w (k + 1) = (ω (k + 1) * c (k + 1)) * v k * w (k + 1) := rfl
    _ = (ω k * a k) * v k * w (k + 1) := by rw [this]
    _ = ω k * a k * v k * w (k + 1) := rfl

/-- **Orthogonality for different eigenvalues** of a weighted finite Jacobi recurrence. -/
theorem jacobi_orth (n : ℕ) (hdb : ∀ k < n, ω k * a k = ω (k + 1) * c (k + 1))
    (hc0 : c 0 = 0) (han : a n = 0)
    (hv : ∀ k ≤ n, a k * v (k + 1) + b k * v k + c k * v (k - 1) = lam * v k)
    (hw : ∀ k ≤ n, a k * w (k + 1) + b k * w k + c k * w (k - 1) = mu * w k) :
    (lam - mu) * ∑ k ∈ range (n + 1), ω k * v k * w k = 0 := by
  have s1 := jacobi_shift n a c ω v w hdb hc0 han
  have s2 := jacobi_shift n a c ω w v hdb hc0 han
  have e1 : lam * ∑ k ∈ range (n + 1), ω k * v k * w k
      = ∑ k ∈ range (n + 1), ω k * a k * v (k + 1) * w k
        + ∑ k ∈ range (n + 1), ω k * b k * v k * w k
        + ∑ k ∈ range (n + 1), ω k * c k * v (k - 1) * w k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have := hv k (by have := Finset.mem_range.mp hk; omega)
    linear_combination (-(ω k * w k)) * this
  have e2 : mu * ∑ k ∈ range (n + 1), ω k * v k * w k
      = ∑ k ∈ range (n + 1), ω k * a k * w (k + 1) * v k
        + ∑ k ∈ range (n + 1), ω k * b k * w k * v k
        + ∑ k ∈ range (n + 1), ω k * c k * w (k - 1) * v k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have := hw k (by have := Finset.mem_range.mp hk; omega)
    linear_combination (-(ω k * v k)) * this
  have t1 : ∑ k ∈ range (n + 1), ω k * b k * v k * w k
      = ∑ k ∈ range (n + 1), ω k * b k * w k * v k :=
    Finset.sum_congr rfl fun k _ => by ring
  have t2 : ∑ k ∈ range (n + 1), ω k * a k * w (k + 1) * v k
      = ∑ k ∈ range (n + 1), ω k * a k * v k * w (k + 1) :=
    Finset.sum_congr rfl fun k _ => by ring
  have t3 : ∑ k ∈ range (n + 1), ω k * a k * v (k + 1) * w k
      = ∑ k ∈ range (n + 1), ω k * c k * w (k - 1) * v k := by
    rw [s2]; exact Finset.sum_congr rfl fun k _ => by ring
  linear_combination e1 - e2 + t1 - t2 + s1 + t3

end Lightlike.TV.Refl
