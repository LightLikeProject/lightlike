import Mathlib

/-!
# A balanced alternating Gamma-ratio sum with known value

Row G3-167 (SP2), trust check "a sum with known asymptotics".  The sum `Σ_t (−1)^t C(2n,t)²`, with
`C(2n,t) = Γ(2n+1)/(Γ(t+1) Γ(2n−t+1))`, is an alternating sum of a ratio of Gamma functions, but it is **not** of the shape of
Racah's single sum (that shape has `Γ(t+2)` in the numerator and seven Gamma functions in the denominator, as in the
statement of `racahSumAsymptotics`).  Its value is exactly known, `(−1)^n C(2n,n)` (Kummer), while the sum of the absolute values of
its terms is `C(4n,2n)` (Vandermonde): the terms are exponentially larger than the sum, by a factor at least `4^n/(4n+1)`.
So a real-variable estimate that controls the terms in absolute value cannot give the sum (`kummer_cancellation`).
-/

open Finset Polynomial

namespace Lightlike.Asymptotics

/-- **Kummer's alternating sum of squares of binomial coefficients**: `Σ_t (−1)^t C(2n,t)² = (−1)^n C(2n,n)`. -/
theorem kummer_alternating (n : ℕ) :
    ∑ t ∈ range (2 * n + 1), (-1 : ℤ) ^ t * ((2 * n).choose t : ℤ) ^ 2 = (-1) ^ n * ((2 * n).choose n : ℤ) := by
  have hm : ((X - 1 : ℤ[X]) ^ (2 * n) * (X + 1) ^ (2 * n)) =
      expand ℤ 2 ((X - 1 : ℤ[X]) ^ (2 * n)) := by
    rw [← mul_pow, map_pow]
    congr 1
    simp [expand_X]
    ring
  have h1 := congrArg (fun p : ℤ[X] => p.coeff (2 * n)) hm
  simp only [coeff_mul] at h1
  rw [coeff_expand (by norm_num), if_pos (dvd_mul_right 2 n), Nat.mul_div_cancel_left _ (by norm_num)] at h1
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h1
  have e1 : (X - 1 : ℤ[X]) = X + C (-1) := by simp [sub_eq_add_neg]
  have hL : ∀ k ∈ range (2 * n + 1), ((X - 1 : ℤ[X]) ^ (2 * n)).coeff k * ((X + 1 : ℤ[X]) ^ (2 * n)).coeff (2 * n - k) =
      (-1 : ℤ) ^ k * ((2 * n).choose k : ℤ) ^ 2 := by
    intro k hk
    have hk' : k ≤ 2 * n := by simpa [Nat.lt_succ_iff] using hk
    have c1 : ((X - 1 : ℤ[X]) ^ (2 * n)).coeff k = (-1) ^ (2 * n - k) * ((2 * n).choose k : ℤ) := by
      rw [e1, coeff_X_add_C_pow]
    have c2 : ((X + 1 : ℤ[X]) ^ (2 * n)).coeff (2 * n - k) = ((2 * n).choose (2 * n - k) : ℤ) := by
      rw [coeff_X_add_one_pow]
    rw [c1, c2, Nat.choose_symm hk']
    have : (-1 : ℤ) ^ (2 * n - k) = (-1) ^ k := by
      by_cases hev : Even k
      · rw [hev.neg_one_pow, ((Nat.even_sub hk').2 ⟨fun _ => hev, fun _ => ⟨n, by ring⟩⟩).neg_one_pow]
      · have hodd : Odd k := Nat.not_even_iff_odd.1 hev
        have h2 : Odd (2 * n - k) := by
          rw [← Nat.not_even_iff_odd, Nat.even_sub hk']
          intro h
          exact hev (h.1 ⟨n, by ring⟩)
        rw [hodd.neg_one_pow, h2.neg_one_pow]
    rw [this]; ring
  rw [Finset.sum_congr rfl hL] at h1
  rw [h1, e1, coeff_X_add_C_pow]
  have : 2 * n - n = n := by omega
  rw [this]

/-- The terms of Kummer's sum add up in absolute value to `C(4n, 2n)` (Vandermonde). -/
theorem kummer_abs_sum (n : ℕ) :
    ∑ t ∈ range (2 * n + 1), |(-1 : ℤ) ^ t * ((2 * n).choose t : ℤ) ^ 2| = ((4 * n).choose (2 * n) : ℤ) := by
  have h := Nat.add_choose_eq (2 * n) (2 * n) (2 * n)
  rw [show 2 * n + 2 * n = 4 * n by ring, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  have h' : ((4 * n).choose (2 * n) : ℤ) = ∑ t ∈ range (2 * n + 1), ((2 * n).choose t : ℤ) ^ 2 := by
    have := congrArg (fun m : ℕ => (m : ℤ)) h
    simp only [Nat.cast_sum, Nat.cast_mul] at this
    rw [this]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t ≤ 2 * n := by simpa [Nat.lt_succ_iff] using ht
    simp only [Nat.choose_symm ht']
    ring
  rw [h']
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_of_nonneg (Int.natCast_nonneg _)]

/-- **A real-variable estimate cannot see Kummer's sum.** The sum of the absolute values of the terms exceeds the
absolute value of the sum by a factor at least `4^n / (4n + 1)`, exponentially large. -/
theorem kummer_cancellation (n : ℕ) :
    (4 : ℤ) ^ n * |∑ t ∈ range (2 * n + 1), (-1 : ℤ) ^ t * ((2 * n).choose t : ℤ) ^ 2| ≤
      (4 * n + 1) * ∑ t ∈ range (2 * n + 1), |(-1 : ℤ) ^ t * ((2 * n).choose t : ℤ) ^ 2| := by
  rw [kummer_alternating, kummer_abs_sum, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Int.natCast_nonneg _)]
  have h1 : ((2 * n).choose n : ℤ) ≤ 4 ^ n := by
    have := Nat.centralBinom_le_four_pow n
    rw [Nat.centralBinom_eq_two_mul_choose] at this
    exact_mod_cast this
  have h2 : (4 : ℤ) ^ (2 * n) ≤ (4 * n + 1) * ((4 * n).choose (2 * n) : ℤ) := by
    have := Nat.four_pow_le_two_mul_add_one_mul_central_binom (2 * n)
    rw [show 2 * (2 * n) = 4 * n by ring, show 4 * n + 1 = 4 * n + 1 from rfl] at this
    have h3 : ((4 : ℕ) ^ (2 * n) : ℤ) ≤ (((4 * n + 1) * (4 * n).choose (2 * n) : ℕ) : ℤ) := by exact_mod_cast this
    push_cast at h3
    nlinarith
  calc (4 : ℤ) ^ n * ((2 * n).choose n : ℤ) ≤ 4 ^ n * 4 ^ n := by
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 4 ^ (2 * n) := by ring
    _ ≤ _ := h2

end Lightlike.Asymptotics
