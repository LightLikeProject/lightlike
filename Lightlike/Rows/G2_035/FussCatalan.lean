import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Fuss–Catalan numbers (G2-035)

The Fuss–Catalan number `fussCatalan p n = binom(pn, n) / ((p-1) n + 1)` counts the rooted `p`-ary
trees with `n` internal nodes; for `p = D + 1` these are the melonic counts of colored tensor models
(`bonzom-gurau-riello-rivasseau-2011`).  Mathlib has only the case `p = 2` (`catalan`).

This file defines the numbers, shows that the division is exact (`mul_fussCatalan`), and compares
with Mathlib's `catalan` (`fussCatalan_two`).

**Sources.** `bonzom-gurau-riello-rivasseau-2011`, `gurau-2011`; no equation number is cited.
-/

namespace Lightlike.Rows.G2_035

/-- The **Fuss–Catalan number** `binom(p n, n) / ((p - 1) n + 1)` (natural-number division, which is
exact for `p ≥ 1`: see `mul_fussCatalan`). -/
def fussCatalan (p n : ℕ) : ℕ := (p * n).choose n / ((p - 1) * n + 1)

/-- The numerator is divisible by `(p-1) n + 1`, with the quotient `binom(pn,n) - (p-1) binom(pn,n-1)`
(for `n ≥ 1`).  Stated for `p = q + 1`. -/
theorem dvd_choose (q n : ℕ) : (q * n + 1) ∣ ((q + 1) * n).choose n := by
  rcases n with _ | m
  · simp
  · set N := (q + 1) * (m + 1) with hN
    have h1 := Nat.choose_succ_right_eq N m
    have hsub : N - m = q * (m + 1) + 1 := by
      rw [hN]; ring_nf; omega
    rw [hsub] at h1
    -- h1 : C(N,m+1) * (m+1) = C(N,m) * (q*(m+1)+1)
    have hle : q * N.choose m ≤ N.choose (m + 1) := by
      by_contra hcon0
      have hcon := not_le.mp hcon0
      have : (m + 1) * N.choose (m + 1) < (m + 1) * (q * N.choose m) :=
        Nat.mul_lt_mul_of_pos_left hcon (Nat.succ_pos m)
      nlinarith [Nat.zero_le (N.choose m)]
    refine ⟨N.choose (m + 1) - q * N.choose m, ?_⟩
    obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le hle
    rw [hw]
    rw [hw] at h1
    simp only [Nat.add_sub_cancel_left]
    nlinarith [h1]

/-- **Exactness**: `((p-1) n + 1) · fussCatalan p n = binom(p n, n)` for `p ≥ 1`. -/
theorem mul_fussCatalan {p : ℕ} (hp : 1 ≤ p) (n : ℕ) :
    ((p - 1) * n + 1) * fussCatalan p n = (p * n).choose n := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hp
  have := dvd_choose q n
  simpa [fussCatalan] using Nat.mul_div_cancel' this

/-- For `p = 2` the Fuss–Catalan numbers are Mathlib's Catalan numbers. -/
theorem fussCatalan_two (n : ℕ) : fussCatalan 2 n = catalan n := by
  rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]
  simp [fussCatalan]

/-- For `p = 1` every Fuss–Catalan number is `1` (the unary tree with `n` nodes is unique). -/
theorem fussCatalan_one (n : ℕ) : fussCatalan 1 n = 1 := by
  simp [fussCatalan]

/-- Trust check, `p = 3` (ternary trees): `1, 1, 3, 12, 55, 273`. -/
theorem fussCatalan_three_values :
    (List.range 6).map (fussCatalan 3) = [1, 1, 3, 12, 55, 273] := by decide +kernel

/-- Trust check, `p = 4` (the melonic counts of the `D = 3` colored model): `1, 1, 4, 22, 140`. -/
theorem fussCatalan_four_values :
    (List.range 5).map (fussCatalan 4) = [1, 1, 4, 22, 140] := by decide +kernel

/-- A wrong model gives a different answer: dropping the `+1` in the denominator gives `14`, not the
ternary-tree count `12`, at `n = 3`. -/
theorem wrong_denominator_ne : (3 * 3).choose 3 / ((3 - 1) * 3) ≠ fussCatalan 3 3 := by decide +kernel

end Lightlike.Rows.G2_035
