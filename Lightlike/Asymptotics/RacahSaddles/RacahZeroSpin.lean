import Lightlike.Asymptotics.Racah
import Lightlike.PonzanoRegge.BEZero

/-!
# Racah's sum with one spin zero: an exact known value

The Racah sum `racahSum` at spins `(0, a, a, c, b, b)` (the 6j symbol
`{0 a a; c b b}` with a zero spin) has a single term, `t = a + b + c`, and so a closed form
`(-1)^(a+b+c) (a+b+c+1)! / ((b+c-a)! (a+c-b)! (a+b-c)!)` = `(-1)^(a+b+c) / Δ(a b c)²`. It is a known value of the
sum in the exact shape of `racahSum`, but it has **no cancellation** (one term) and a zero spin is not a Euclidean
tetrahedron, so it does not test `racahSumAsymptotics` (which needs `IsEuclid`); it tests the sign and factorial
conventions of `racahSum`.
-/

open Finset PhyslibAlpha.Sl2

set_option linter.unusedSimpArgs false

namespace Lightlike.Asymptotics

/-- **Racah's sum at `(0, a, a, c, b, b)`** with `(a, b, c)` a triad: one term, `t = a + b + c`. -/
theorem racahSum_zero_spin (a b c : ℕ) (hab : c ≤ a + b) (hac : a ≤ b + c) (hbc : b ≤ a + c) :
    racahSum ![0, a, a, c, b, b] =
      (-1 : ℝ) ^ (a + b + c) * ((a + b + c + 1).factorial : ℝ) *
        (((b + c - a).factorial : ℝ)⁻¹ * ((a + c - b).factorial : ℝ)⁻¹ * ((a + b - c).factorial : ℝ)⁻¹) := by
  have hq0 : quadN ![0, a, a, c, b, b] 0 = a + b + c := by simp [quadN]; ring
  unfold racahSum
  rw [hq0]
  rw [Finset.sum_eq_single (a + b + c)]
  · have f0 : invFact (((a + b + c : ℕ) : ℤ) - faceN ![0, a, a, c, b, b] 0) =
        ((b + c - a).factorial : ℝ)⁻¹ := by
      apply invFact_eq; simp [faceN]; omega
    have f1 : invFact (((a + b + c : ℕ) : ℤ) - faceN ![0, a, a, c, b, b] 1) =
        ((a + c - b).factorial : ℝ)⁻¹ := by
      apply invFact_eq; simp [faceN]; omega
    have f2 : invFact (((a + b + c : ℕ) : ℤ) - faceN ![0, a, a, c, b, b] 2) = 1 := by
      rw [invFact_eq (t := 0) (by simp [faceN]; omega)]; simp
    have f3 : invFact (((a + b + c : ℕ) : ℤ) - faceN ![0, a, a, c, b, b] 3) = 1 := by
      rw [invFact_eq (t := 0) (by simp [faceN]; omega)]; simp
    have g0 : invFact ((quadN ![0, a, a, c, b, b] 0 : ℤ) - ((a + b + c : ℕ) : ℤ)) = 1 := by
      rw [invFact_eq (t := 0) (by rw [hq0]; simp)]; simp
    have g1 : invFact ((quadN ![0, a, a, c, b, b] 1 : ℤ) - ((a + b + c : ℕ) : ℤ)) =
        ((a + b - c).factorial : ℝ)⁻¹ := by
      apply invFact_eq; simp [quadN]; omega
    have g2 : invFact ((quadN ![0, a, a, c, b, b] 2 : ℤ) - ((a + b + c : ℕ) : ℤ)) = 1 := by
      rw [invFact_eq (t := 0) (by simp [quadN])]; simp
    simp only [Fin.prod_univ_four, Fin.prod_univ_three, f0, f1, f2, f3, g0, g1, g2]
    ring
  · intro t ht hne
    have htl : t < a + b + c := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)) hne
    have : invFact ((t : ℤ) - faceN ![0, a, a, c, b, b] 2) = 0 := by
      simp only [invFact]
      split_ifs with h
      · exfalso
        simp [faceN] at h
        omega
      · rfl
    have hp : ∏ i, invFact ((t : ℤ) - faceN ![0, a, a, c, b, b] i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ 2) this
    rw [hp]; simp
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

/-- **Cross-check against the 6j symbol.** `Δ · racahSum` at `(0, a, a, c, b, b)` (Racah's formula) equals the closed form
of the 6j symbol with a zero spin, `(-1)^(a+b+c) / √((2a+1)(2b+1))`: the single-term value of the sum above and
`sixJSym_zero_left` (proved independently) agree through `racahFormula`. -/
theorem racahDelta_mul_racahSum_zero_spin (a b c : ℕ) (hab : c ≤ a + b) (hac : a ≤ b + c)
    (hbc : b ≤ a + c) :
    racahDelta ![0, a, a, c, b, b] * racahSum ![0, a, a, c, b, b] =
      (-1 : ℝ) ^ (a + b + c) / (√(2 * (a : ℝ) + 1) * √(2 * (b : ℝ) + 1)) := by
  have h := racahFormula ![0, a, a, c, b, b] (by simp [PR.IsTriad, Nat.add_comm, hab, hac, hbc]) (by simp [PR.IsTriad, Nat.add_comm, hab, hac, hbc])
    (by simp [PR.IsTriad, Nat.add_comm, hab, hac, hbc]) (by simp [PR.IsTriad, Nat.add_comm, hab, hac, hbc])
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h
  rw [← h]
  have hT : Lightlike.Pentagon.Tri (2 * a) (2 * b) (2 * c) := by
    refine ⟨by omega, by omega, by omega, by omega⟩
  simp only [mul_zero]
  rw [Lightlike.Pentagon.sixJSym_zero_left, if_pos ⟨rfl, rfl, hT⟩]
  have e : (2 * a + 2 * b + 2 * c) / 2 = a + b + c := by omega
  rw [e]
  push_cast
  rfl

end Lightlike.Asymptotics
