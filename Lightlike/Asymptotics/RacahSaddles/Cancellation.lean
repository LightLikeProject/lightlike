import Lightlike.Asymptotics.Assembly

/-!
# Cancellation in Racah's sum

Racah's alternating sum `racahSum J = Σ_t (−1)^t (t+1)! / (∏ᵢ (t − aᵢ)! ∏ₖ (bₖ − t)!)` has terms that are
exponentially larger than the sum. A real-variable estimate that controls the terms in absolute value
(a Riemann sum, Euler–Maclaurin) cannot see the sum; this is why the asymptotics are proved by a complex
contour (`racahSumAsymptotics`).

* `racahSummand J t`: the `t`-th term of `racahSum`, `racahSum_eq_sum_racahSummand`;
* `racahSum_regular_ten`, `_twenty`, `_forty`: the exact values of Racah's sum of the regular tetrahedron with
  spins `10`, `20`, `40`;
* `racah_cancellation_regular_ten`, `_twenty`, `_forty`: for these spins the absolute values of the terms add up
  to more than `100`, `800` and `10^6` times the absolute value of the sum (the measured ratios are `111`, `835`
  and `1.04 · 10^6`), exponential growth in the spin.

**Limits.** Three instances, not the asymptotic statement that the ratio is unbounded as the spins grow.
-/

open Finset PhyslibAlpha.Sl2

namespace Lightlike.Asymptotics

/-- The `t`-th term of Racah's alternating sum. -/
noncomputable def racahSummand (J : Fin 6 → ℕ) (t : ℕ) : ℝ :=
  (-1 : ℝ) ^ t * ((t + 1).factorial : ℝ) * (∏ i, invFact ((t : ℤ) - faceN J i)) *
    ∏ k, invFact ((quadN J k : ℤ) - t)

/-- Racah's sum is the sum of its terms. -/
theorem racahSum_eq_sum_racahSummand (J : Fin 6 → ℕ) :
    racahSum J = ∑ t ∈ range (quadN J 0 + 1), racahSummand J t := rfl

/-- The face sums of the regular tetrahedron with spins `n` are `3n`. -/
lemma faceN_regular_const (n : ℕ) (i : Fin 4) : faceN (fun _ => n) i = 3 * n := by
  fin_cases i <;> simp [faceN] <;> ring

/-- The quadrilateral sums of the regular tetrahedron with spins `n` are `4n`. -/
lemma quadN_regular_const (n : ℕ) (k : Fin 3) : quadN (fun _ => n) k = 4 * n := by
  fin_cases k <;> simp [quadN] <;> ring

/-- **Known value**: Racah's sum of the regular tetrahedron with spins `10`. -/
theorem racahSum_regular_ten : racahSum (fun _ => 10) = -86442481157519015900951580 := by
  rw [racahSum_eq_sum_racahSummand]
  simp only [racahSummand, faceN_regular_const, quadN_regular_const, Fin.prod_univ_four, Fin.prod_univ_three,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [invFact, Nat.factorial]

/-- **The real-variable estimate fails, spins `10`**: the absolute values of the terms of Racah's sum add up to
more than `100` times the absolute value of the sum. -/
theorem racah_cancellation_regular_ten :
    100 * |racahSum (fun _ => 10)| ≤ ∑ t ∈ range (quadN (fun _ => 10) 0 + 1), |racahSummand (fun _ => 10) t| := by
  rw [racahSum_regular_ten]
  simp only [racahSummand, faceN_regular_const, quadN_regular_const, Fin.prod_univ_four, Fin.prod_univ_three,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [invFact, Nat.factorial, abs_mul]

/-- **Known value**: Racah's sum of the regular tetrahedron with spins `20`. -/
theorem racahSum_regular_twenty :
    racahSum (fun _ => 20) = -6248537816604694597174085898273653303317767844323352500 := by
  rw [racahSum_eq_sum_racahSummand]
  simp only [racahSummand, faceN_regular_const, quadN_regular_const, Fin.prod_univ_four, Fin.prod_univ_three,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [invFact, Nat.factorial]

/-- **The real-variable estimate fails, spins `20`**: the ratio of the absolute terms to the sum exceeds `800`. -/
theorem racah_cancellation_regular_twenty :
    800 * |racahSum (fun _ => 20)| ≤ ∑ t ∈ range (quadN (fun _ => 20) 0 + 1), |racahSummand (fun _ => 20) t| := by
  rw [racahSum_regular_twenty]
  simp only [racahSummand, faceN_regular_const, quadN_regular_const, Fin.prod_univ_four, Fin.prod_univ_three,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [invFact, Nat.factorial, abs_mul]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- **Known value**: Racah's sum of the regular tetrahedron with spins `40`. -/
theorem racahSum_regular_forty :
    racahSum (fun _ => 40) =
      4060103848009089721152370464574783283905490525792971765830281586551143092104579309538237724879887714909566081820 := by
  rw [racahSum_eq_sum_racahSummand]
  simp only [racahSummand, faceN_regular_const, quadN_regular_const, Fin.prod_univ_four, Fin.prod_univ_three,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [invFact, Nat.factorial]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- **The real-variable estimate fails, spins `40`**: the ratio of the absolute terms to the sum exceeds `10^6`. -/
theorem racah_cancellation_regular_forty :
    1000000 * |racahSum (fun _ => 40)| ≤ ∑ t ∈ range (quadN (fun _ => 40) 0 + 1), |racahSummand (fun _ => 40) t| := by
  rw [racahSum_regular_forty]
  simp only [racahSummand, faceN_regular_const, quadN_regular_const, Fin.prod_univ_four, Fin.prod_univ_three,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [invFact, Nat.factorial, abs_mul]

end Lightlike.Asymptotics
