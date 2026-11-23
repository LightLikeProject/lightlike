import Lightlike.Regge.CMS4.Kuhn4
import Lightlike.Regge.CMS4.Dihedral4Deriv

/-!
# The first variation of the orthoscheme's dihedral angles

Evaluates the data of `hasDerivAt_dihS` at the squared lengths `kd4` of the Kuhn orthoscheme:
the Gram determinants of the two tetrahedra at every hinge are positive and the cosine of the
dihedral angle is `hcos`, so the angle is differentiable along every line `kd4 + ε δ`.
-/

open Real

namespace Lightlike.Regge4

theorem kuhn4_cosS (h : Fin 10) :
    cosS kd4 (hP h) (hQ h) (hR h) (hS h) (hU h) = hcos h := by
  fin_cases h <;>
    simp [cosS, mixedS, gram3S, ipS, det3, kd4, kv4, hP, hQ, hR, hS, hU, hcos,
      Fin.sum_univ_four] <;> norm_num
  all_goals
    have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h2p : 0 < √2 := by positivity
    field_simp
    linarith

theorem kuhn4_gram_S (h : Fin 10) : 0 < gram3S kd4 (hP h) (hQ h) (hR h) (hS h) := by
  fin_cases h <;>
    simp [gram3S, ipS, det3, kd4, kv4, hP, hQ, hR, hS, Fin.sum_univ_four] <;> norm_num

theorem kuhn4_gram_U (h : Fin 10) : 0 < gram3S kd4 (hP h) (hQ h) (hR h) (hU h) := by
  fin_cases h <;>
    simp [gram3S, ipS, det3, kd4, kv4, hP, hQ, hR, hU, Fin.sum_univ_four] <;> norm_num

theorem kuhn4_hcos_sq (h : Fin 10) : hcos h ^ 2 < 1 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2p : 0 < √2 := by positivity
  fin_cases h <;> simp [hcos] <;>
    first | nlinarith | (rw [abs_lt]; constructor <;> nlinarith)

theorem kuhn4_hcos_ne (h : Fin 10) : hcos h ≠ 1 ∧ hcos h ≠ -1 := by
  have := kuhn4_hcos_sq h
  constructor <;> intro H <;> rw [H] at this <;> norm_num at this

/-- Every dihedral angle of the orthoscheme is differentiable along every line `kd4 + ε δ`, with
the derivative of `hasDerivAt_dihS`. -/
theorem kuhn4_hasDerivAt (δ : Fin 5 → Fin 5 → ℝ) (h : Fin 10) :
    ∃ d : ℝ, HasDerivAt (fun ε : ℝ => dihS (fun x y => kd4 x y + ε * δ x y) (hP h) (hQ h) (hR h)
        (hS h) (hU h)) d 0 :=
  ⟨_, hasDerivAt_dihS kd4 δ _ _ _ _ _ (kuhn4_gram_S h) (kuhn4_gram_U h)
    (by rw [kuhn4_cosS]; exact (kuhn4_hcos_ne h).1)
    (by rw [kuhn4_cosS]; exact (kuhn4_hcos_ne h).2)⟩

end Lightlike.Regge4
