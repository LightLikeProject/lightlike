import Lightlike.OperatorAlgebras.Yosida
import Lightlike.OperatorAlgebras.TestsResolvent

/-!
# Trust checks for the approximants

For the phase-group generator `λ • 1`, the approximant is the scalar `t² λ / (λ² + t²)`, which tends to `λ`:
this tests the factor `t² / 2`, the signs of the two resolvents and that `A_n x → A x`.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The approximant of the phase-group generator** is `t² λ / (λ² + t²)`. -/
theorem approx_phaseGroup (l : ℝ) (n : ℕ) (y : H) :
    approx (UnitaryGroup.generator_isSelfAdjoint (phaseGroup l : UnitaryGroup H)) n y =
      ((((tn n) ^ 2 * l / (l ^ 2 + (tn n) ^ 2) : ℝ) : ℂ)) • y := by
  have hsa := UnitaryGroup.generator_isSelfAdjoint (phaseGroup l : UnitaryGroup H)
  have hP : resP hsa n y = ((l : ℂ) - Complex.I * (tn n : ℂ))⁻¹ • y :=
    resolvent_phaseGroup l (z := Complex.I * (tn n : ℂ)) (by simpa using (tn_pos n).ne') y
  have hM : resM hsa n y = ((l : ℂ) - -(Complex.I * (tn n : ℂ)))⁻¹ • y :=
    resolvent_phaseGroup l (z := -(Complex.I * (tn n : ℂ))) (by simpa using (tn_pos n).ne') y
  rw [approx_apply, hP, hM, ← add_smul, smul_smul]
  congr 1
  have ht : (tn n : ℝ) ≠ 0 := (tn_pos n).ne'
  have h1 : (l : ℂ) - Complex.I * (tn n : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact ht this
  have h2 : (l : ℂ) - -(Complex.I * (tn n : ℂ)) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact ht this
  have h3 : (l : ℂ) ^ 2 + (tn n : ℂ) ^ 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [sq] at this
    have : l * l + tn n * tn n = 0 := by exact_mod_cast this
    nlinarith [mul_self_nonneg l, mul_pos (tn_pos n) (tn_pos n)]
  have e1 : ((l : ℂ) - Complex.I * (tn n : ℂ)) + ((l : ℂ) - -(Complex.I * (tn n : ℂ))) = 2 * l := by ring
  have e2 : ((l : ℂ) - Complex.I * (tn n : ℂ)) * ((l : ℂ) - -(Complex.I * (tn n : ℂ))) =
      (l : ℂ) ^ 2 + (tn n : ℂ) ^ 2 := by
    ring_nf; simp [Complex.I_sq]
  rw [inv_add_inv h1 h2, e1, e2]
  push_cast
  field_simp

end Lightlike.OperatorAlgebras
