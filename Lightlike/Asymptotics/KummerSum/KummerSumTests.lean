import Lightlike.Asymptotics.KummerSum.Asymptotic

/-!
# Tests for the saddle-point run on Kummer's sum

Known values of `kummerSum` (Kummer's identity at small `m`), the vanishing of the leading term
for odd `m` (where the sum is zero), and a deliberately wrong saddle: the real midpoint `α = ½`,
where the real-variable heuristics would put the maximum of the terms, is not a critical point of
the phase (`ψ'(½) = iπ ≠ 0`), so the saddle is genuinely complex.
-/

open Complex Finset
open scoped Real

namespace Lightlike.Asymptotics

/-- `Σ_t (−1)^t C(2,t)² = 1 − 4 + 1 = −2 = (−1)^1 C(2,1)`. -/
example : kummerSum 2 = -2 := by
  simp [kummerSum, Finset.sum_range_succ, Nat.choose]; norm_num

/-- `Σ_t (−1)^t C(4,t)² = 1 − 16 + 36 − 16 + 1 = 6 = C(4,2)`. -/
example : kummerSum 4 = 6 := by
  simp [kummerSum, Finset.sum_range_succ, Nat.choose]; norm_num

/-- For odd `m` the sum vanishes, and so does the leading term (`Im(i^{m+1}) = 0`). -/
example : kummerSum 3 = 0 ∧ kummerLead 3 = 0 := by
  refine ⟨by simp [kummerSum, Finset.sum_range_succ, Nat.choose]; norm_num, ?_⟩
  rw [kummerLead, show I ^ (3 + 1) = 1 by rw [show 3 + 1 = 2 * 2 by rfl, pow_mul, I_sq]; norm_num]
  simp

/-- **A wrong saddle**: the real midpoint `α = ½` is not a critical point of the phase. -/
theorem dkummerPhase_half_ne_zero : dkummerPhase (1 / 2) ≠ 0 := by
  rw [dkummerPhase, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, sub_self, mul_zero, sub_zero]
  exact mul_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero) I_ne_zero

/-- Non-vacuity of `kummerSum_saddle_bound`: its hypothesis `5 ≤ m` holds, and the leading term is
nonzero, at `m = 6`. -/
example : 5 ≤ 6 ∧ kummerLead (2 * 3) ≠ 0 := ⟨by norm_num, kummerLead_two_mul_ne_zero 3⟩

end Lightlike.Asymptotics
