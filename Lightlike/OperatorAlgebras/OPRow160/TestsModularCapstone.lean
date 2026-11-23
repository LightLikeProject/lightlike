import Lightlike.OperatorAlgebras.OPRow160.ModularCapstone

/-!
# Checks for the OP3 capstone

The trust checks of OP3 for the qubit `H = diag (0, E)`: the Gibbs state `diag (1, e^{-βE}) / (1 + e^{-βE})` is `β`-KMS, and the
maximally mixed state is not `1`-KMS for `E = 1`.
-/

open Matrix

namespace Lightlike.OperatorAlgebras

/-- The Gibbs weights of the qubit at inverse temperature `β` give a KMS state. -/
theorem qubit_gibbs_weights_isKMS (E : ℂ) (β : ℝ) (h : (1 + Complex.exp (-(β * E))) ≠ 0) :
    IsKMS (qubitHam E) (Matrix.diagonal ![(1 + Complex.exp (-(β * E)))⁻¹,
      Complex.exp (-(β * E)) * (1 + Complex.exp (-(β * E)))⁻¹]) β := by
  have hexp : Complex.exp (β * E) * Complex.exp (-(β * E)) = 1 := by
    rw [← Complex.exp_add]; simp
  refine (qubit_isKMS_iff E β _ _ ?_).mpr ?_
  · field_simp
  · calc (1 + Complex.exp (-(β * E)))⁻¹
        = Complex.exp (-(β * E)) * (1 + Complex.exp (-(β * E)))⁻¹ * (Complex.exp (β * E)) := by
          rw [mul_right_comm, mul_comm (Complex.exp (-(β * E))), hexp, one_mul]
      _ = _ := by ring

/-- The maximally mixed qubit state is not `1`-KMS for `H = diag (0, 1)`. -/
theorem qubit_maxMixed_not_isKMS_capstone :
    ¬ IsKMS (qubitHam 1) (Matrix.diagonal ![(1 / 2 : ℂ), 1 / 2]) 1 := by
  rw [qubit_isKMS_iff 1 1 _ _ (by norm_num)]
  intro h
  have h2 := mul_left_cancel₀ (show (1 / 2 : ℂ) ≠ 0 by norm_num)
    (show (1 / 2 : ℂ) * 1 = 1 / 2 * Complex.exp (((1 : ℝ) : ℂ) * 1) by rw [mul_one]; exact h)
  have h3 : Complex.exp 1 = 1 := by simpa using h2.symm
  have h4 : ((Real.exp 1 : ℝ) : ℂ) = 1 := by rw [Complex.ofReal_exp, Complex.ofReal_one]; exact h3
  have h5 : Real.exp 1 = 1 := Complex.ofReal_eq_one.mp h4
  have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
  linarith

end Lightlike.OperatorAlgebras
