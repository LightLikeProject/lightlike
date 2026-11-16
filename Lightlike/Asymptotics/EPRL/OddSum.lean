import Lightlike.Asymptotics.EPRL.HaarNode

/-!
# An odd node sum kills the coherent `15j` integral

A coherent intertwiner `ι_J(g⃗) = P (⊗_a |J_a/2, g_a⟩)` is invariant under the centre element `-1` of
`SU(2)`, which acts on `⊗_a V_{J_a/2}` as the sign `(-1)^{Σ J_a}`. If the doubled spins at a node of
`K₅` have an odd sum, the coherent intertwiner of that node vanishes, so the coherent `15j` integral
`coh15j` is zero for all boundary data. This is a trust check of the hypotheses of
`Coh15jAsymptoticFormula`: with an odd node sum the integral vanishes identically, so the nonzero
leading term of the formula cannot hold; the even node sums are necessary.

## Main results

* `rhoN_negOne`: the diagonal action of `-1` is the sign `(-1)^{Σ J_a}`.
* `cohInt_eq_zero_of_odd`: a coherent intertwiner vanishes when `Σ J_a` is odd.
* `coh15j_eq_zero_of_odd`: the coherent `15j` integral vanishes when the doubled spins at some node of
  `K₅` have an odd sum.

## References

* J. W. Barrett, W. J. Fairbairn, F. Hellmann, *Quantum gravity asymptotics from the SU(2) 15j symbol*,
  arXiv:0912.4907, eq. (1) (the coherent integral, formalized in `Amplitude.lean`).
-/

open Matrix MeasureTheory

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2

variable {N : ℕ} (J : Fin N → ℕ)

/-- The diagonal action of the centre element `-1` on `⊗_a V_{J_a/2}` is the sign `(-1)^{Σ J_a}`. -/
theorem rhoN_negOne : rhoN J negOne = ((-1 : ℂ) ^ ∑ a, J a) • (1 : Matrix (LIdx J) (LIdx J) ℂ) := by
  ext k l
  simp only [rhoN, Matrix.of_apply, spinMat_negOne, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  by_cases h : k = l
  · subst h; simp
  · obtain ⟨a, ha⟩ : ∃ a, k a ≠ l a := not_forall.mp fun hc => h (funext hc)
    have hz : (∏ x, if k x = l x then (1 : ℂ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a) (ite_eq_right_iff.mpr fun h' => absurd h' ha)
    simp [h, hz]

/-- **A coherent intertwiner vanishes when the sum of the spins is odd**: it is invariant under the
centre element `-1`, which acts as `(-1)^{Σ J_a}`. -/
theorem cohInt_eq_zero_of_odd (g : Fin N → SU2) (h : Odd (∑ a, J a)) : cohInt J g = 0 := by
  have hinv := cohInt_isInvariantN (J := J) g negOne
  rw [rhoN_negOne, Matrix.smul_mulVec, Matrix.one_mulVec, h.neg_one_pow] at hinv
  funext i
  have := congrFun hinv i
  simp only [Pi.smul_apply, smul_eq_mul, neg_mul, one_mul] at this
  have h2 : (2 : ℂ) * cohInt J g i = 0 := by linear_combination (-1 : ℂ) * this
  simpa using h2

/-- **Trust check for the even-sum hypothesis.** If the doubled spins at some node of `K₅` have an odd
sum, the coherent `15j` integral vanishes for all boundary data (the integrand changes sign under
`X_a ↦ -X_a`), so the nonzero leading term of the asymptotic formula cannot hold: the even node sums
of `Coh15jAsymptoticFormula` are necessary. -/
theorem coh15j_eq_zero_of_odd (n : Fin 10 → ℕ) (g : Fin 10 → Fin 2 → SU2) (a : Fin 5)
    (h : Odd (∑ l, k5Spins n a l)) :
    coh15j n (fun e s => (g e s : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
  rw [← k5Contract_cohInt]
  have h0 : cohInt (k5Spins n a) (nodeBdry g a) = 0 := cohInt_eq_zero_of_odd _ _ h
  unfold k5Contract
  refine Finset.sum_eq_zero fun μ _ => ?_
  rw [Finset.prod_eq_zero (Finset.mem_univ a)]
  · simp
  · simp [h0, projNode]

end Lightlike.Asymptotics.EPRL
