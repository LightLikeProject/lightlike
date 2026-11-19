import Lightlike.OperatorAlgebras.FiniteKMS

/-!
# Checks for the finite-dimensional KMS condition

The task's checks: the Gibbs state of a qubit is KMS at its temperature, and a non-Gibbs state fails. The qubit has the Hamiltonian
`H = diag(0, 1)` and `β = 1`; its Gibbs state is `diag(1, e^{-1}) / (1 + e^{-1})`, and the maximally mixed state `1/2` is not `1`-KMS.
-/

open Matrix NormedSpace

namespace Lightlike.OperatorAlgebras

/-- The qubit Hamiltonian with energies `0` and `1`. -/
noncomputable def qubitH : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![0, 1]

lemma exp_neg_qubitH : exp (-(((1 : ℝ) : ℂ) • qubitH)) = diagonal ![1, Complex.exp (-1)] := by
  rw [Complex.ofReal_one, one_smul, qubitH, diagonal_neg, exp_diagonal, Pi.exp_def]
  congr 1
  funext i
  fin_cases i
  · simp
  · show exp (-(1 : ℂ)) = Complex.exp (-1)
    rw [← Complex.exp_eq_exp_ℂ]

lemma trace_exp_neg_qubitH : (exp (-(((1 : ℝ) : ℂ) • qubitH))).trace = 1 + Complex.exp (-1) := by
  rw [exp_neg_qubitH, trace_diagonal, Fin.sum_univ_two]
  rfl

lemma one_add_exp_neg_one_ne_zero : (1 + Complex.exp (-1)) ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  simp [Complex.exp_re] at this
  linarith [Real.exp_pos (-1)]

lemma trace_exp_neg_qubitH_ne_zero : (exp (-(((1 : ℝ) : ℂ) • qubitH))).trace ≠ 0 := by
  rw [trace_exp_neg_qubitH]
  exact one_add_exp_neg_one_ne_zero

/-- **The Gibbs state of a qubit is KMS at its temperature** (the task's first check). -/
theorem qubit_gibbs_isKMS : IsKMS qubitH (gibbs qubitH 1) 1 := isKMS_gibbs qubitH 1

/-- **A non-Gibbs state fails** (the task's second check): the maximally mixed state `1/2` is not `1`-KMS for `diag(0, 1)`. -/
theorem qubit_maximallyMixed_not_isKMS : ¬ IsKMS qubitH ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 1 := by
  intro hK
  have htr : ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).trace = 1 := by
    rw [trace_smul, trace_one, Fintype.card_fin]; norm_num
  have h := (isKMS_iff_eq_gibbs qubitH _ 1 trace_exp_neg_qubitH_ne_zero htr).mp hK
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [gibbs, exp_neg_qubitH, trace_exp_neg_qubitH, Matrix.smul_apply, Matrix.one_apply_eq, diagonal_apply_eq,
    smul_eq_mul] at h00 h11
  have he : Complex.exp (-1) ≠ 1 := by
    intro h1
    have := Complex.exp_eq_one_iff.mp h1
    obtain ⟨k, hk⟩ := this
    have hre := congrArg Complex.re hk
    simp at hre
  apply he
  -- from `1/2 = c` and `1/2 = c e^{-1}` with `c = (1 + e^{-1})⁻¹ ≠ 0`
  have hc : (diagonal ![(1 : ℂ), Complex.exp (-1)]).trace⁻¹ ≠ 0 := by
    refine inv_ne_zero ?_
    rw [← exp_neg_qubitH]
    exact trace_exp_neg_qubitH_ne_zero
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_one] at h00 h11
  have h5 : (diagonal ![(1 : ℂ), Complex.exp (-1)]).trace⁻¹ * 1 =
      (diagonal ![(1 : ℂ), Complex.exp (-1)]).trace⁻¹ * Complex.exp (-1) := by
    rw [mul_one]; exact h00.symm.trans h11
  exact (mul_left_cancel₀ hc h5).symm

end Lightlike.OperatorAlgebras
