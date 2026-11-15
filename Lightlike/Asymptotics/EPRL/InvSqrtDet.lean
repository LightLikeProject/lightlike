import Lightlike.Oscillatory.Gaussian

/-!
# Two rules for `invSqrtDet`

* a positive real factor `c` on the matrix gives the factor `(c^{-1/2})^n` (`invSqrtDet_smul_pos`);
* a simultaneous permutation of rows and columns does not change it (`invSqrtDet_submatrix`).

They convert the Hessian of the amplitude in the gnomonic chart, `4 P H P`, into the Hessian `H` in
the exponential chart that the asymptotic formula is stated with.
-/

open Matrix Polynomial Lightlike.Oscillatory

namespace Lightlike.Asymptotics.EPRL

/-- A positive real factor passes through the principal power. -/
lemma ofReal_mul_cpow_pos {c : ℝ} (hc : 0 < c) (μ r : ℂ) :
    ((c : ℂ) * μ) ^ r = (c : ℂ) ^ r * μ ^ r := by
  by_cases hμ : μ = 0
  · subst hμ
    by_cases hr : r = 0
    · simp [hr]
    · simp [Complex.zero_cpow hr]
  · have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hc0 hμ), Complex.cpow_def_of_ne_zero hc0,
      Complex.cpow_def_of_ne_zero hμ, Complex.log_ofReal_mul hc hμ, add_mul, Complex.exp_add, Complex.ofReal_log hc.le]

/-- **A positive real factor**: `invSqrtDet (c A) = (c^{-1/2})^n invSqrtDet A`. -/
theorem invSqrtDet_smul_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {c : ℝ} (hc : 0 < c) :
    invSqrtDet ((c : ℂ) • A) = (((c : ℂ) ^ (-(1 / 2 : ℂ))) ^ n) * invSqrtDet A := by
  have h := invSqrtDet_smul_one_add_smul A 0 (c : ℂ)
  rw [zero_smul, zero_add] at h
  rw [h, invSqrtDet]
  simp only [zero_add]
  simp only [ofReal_mul_cpow_pos hc]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]
  have hcard : A.charpoly.roots.card = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [hcard]

/-- **Simultaneous permutation** of rows and columns leaves `invSqrtDet` unchanged. -/
theorem invSqrtDet_submatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) :
    invSqrtDet (A.submatrix σ σ) = invSqrtDet A := by
  have : A.submatrix σ σ = reindex σ.symm σ.symm A := by
    ext i j; simp [reindex_apply]
  rw [invSqrtDet, this, charpoly_reindex]
  rfl

end Lightlike.Asymptotics.EPRL
