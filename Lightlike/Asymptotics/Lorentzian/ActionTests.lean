import Lightlike.Asymptotics.Lorentzian.Action

/-!
# Trust checks for the one-triangle action

* The action is the power form, `e^S = (⟨Z,ξ⟩⟨Jξ',Z'⟩)^{2k} / …`. At a point with
  `⟨Z,ξ⟩⟨Jξ',Z'⟩ = -1` and the odd doubled spin `2k = 1` the earlier form `k log(u²)` gives
  `e^S = 1` and the power form gives `e^S = -1` (`exp_triAction_odd_sign`); at `2k = 2` both give
  `1` (`exp_triAction_even_agree`). The modulus is the same for both.
* The bound `Re S ≤ 0` needs `0 ≤ k`: for `k = -1` the weight exceeds `1` at a point where the
  overlap ratio is `1/2` (`triWeight_neg_spin_gt_one`).
-/

open Complex

namespace Lightlike.Asymptotics.Lorentzian

/-- The earlier form of the action, `k log(u²) + i p log(‖Z'‖²/‖Z‖²)`, kept for the comparison. -/
noncomputable def triActionLog (k p : ℝ) (Z ξ Z' ξ' : Spinor) : ℂ :=
  (k : ℂ) * Complex.log ((inner ℂ Z ξ) ^ 2 * (inner ℂ (jMap ξ') Z') ^ 2 /
      ((‖Z‖ ^ 2 : ℝ) * (‖Z'‖ ^ 2 : ℝ))) +
    Complex.I * (p : ℂ) * Complex.log (((‖Z'‖ ^ 2 : ℝ) : ℂ) / ((‖Z‖ ^ 2 : ℝ) : ℂ))

/-- The data `Z = ξ = ξ' = e₀`, `Z' = -e₁`, with `⟨Z,ξ⟩ = 1` and `⟨Jξ',Z'⟩ = -1`. -/
theorem odd_point_values :
    inner ℂ e0 e0 = (1 : ℂ) ∧ inner ℂ (jMap e0) (-e1) = (-1 : ℂ) ∧ ‖e0‖ = 1 ∧ ‖-e1‖ = 1 := by
  have hj : jMap e0 = e1 := by
    ext i; fin_cases i <;> simp [e0, e1]
  refine ⟨?_, ?_, norm_e0, by rw [norm_neg, norm_e1]⟩
  · rw [inner_self_eq_norm_sq_to_K, norm_e0]; simp
  · rw [hj, inner_neg_right, inner_self_eq_norm_sq_to_K, norm_e1]; simp

/-- **Odd spin, branch flip**: at `2k = 1` the earlier form gives `e^S = 1` and the power form
gives `e^S = -1`. -/
theorem exp_triAction_odd_sign (p : ℝ) :
    Complex.exp (triActionLog (1 / 2) p e0 e0 (-e1) e0) = 1 ∧
      Complex.exp (triAction (1 / 2) p e0 e0 (-e1) e0) = -1 := by
  obtain ⟨h1, h2, h3, h4⟩ := odd_point_values
  constructor
  · simp [triActionLog, h1, h2, h3, h4]
  · simp only [triAction, h1, h2, h3, h4, one_mul, mul_neg, mul_one, Complex.log_neg_one]
    simp [Complex.exp_pi_mul_I]

/-- **Control**: at an even doubled spin `2k = 2` both forms give `e^S = 1`. -/
theorem exp_triAction_even_agree (p : ℝ) :
    Complex.exp (triActionLog 1 p e0 e0 (-e1) e0) = 1 ∧
      Complex.exp (triAction 1 p e0 e0 (-e1) e0) = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := odd_point_values
  constructor
  · simp [triActionLog, h1, h2, h3, h4]
  · simp only [triAction, h1, h2, h3, h4, one_mul, mul_neg, mul_one, Complex.log_neg_one]
    simp
    rw [← mul_assoc]
    exact Complex.exp_two_pi_mul_I

/-- **Wrong input**: the bound `‖e^S‖ ≤ 1` needs `0 ≤ k`. For `k = -1` the weight at
`Z = ξ = ξ' = e₀`, `Z' = (1, 1)` is `2 > 1`. -/
theorem triWeight_neg_spin_gt_one : 1 < triWeight (-1) e0 e0 (!₂[1, 1]) e0 := by
  have hj : jMap e0 = e1 := by
    ext i; fin_cases i <;> simp [e0, e1]
  have h1 : inner ℂ e0 e0 = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, norm_e0]; simp
  have h2 : inner ℂ e1 (!₂[1, 1] : Spinor) = (1 : ℂ) := by
    simp [e1, PiLp.inner_apply, Fin.sum_univ_two]
  have hn : ‖(!₂[1, 1] : Spinor)‖ ^ 2 = 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]; norm_num
  have hr : triReal e0 e0 (!₂[1, 1]) e0 = 1 / 2 := by
    unfold triReal
    rw [hj, h1, h2, norm_e0, hn]; simp
  unfold triWeight
  rw [hr, Real.rpow_neg_one]
  norm_num

end Lightlike.Asymptotics.Lorentzian
