import Lightlike.Regge.CMS4.Kuhn4Deriv

/-!
# First variation of the hinge angles 4, 7 and 9 of the orthoscheme, explicitly

The hinges `(0,3,4)` omitting `1,2` and `(0,1,4)` omitting `2,3` have dihedral angle `π/3`, the
hinge `(0,1,2)` omitting `3,4` has angle `π/4`; the derivative of each along `kd4 + ε δ` is a
linear form in `δ`, obtained as for `kuhn4_hinge0_deriv`.
-/

open Real

namespace Lightlike.Regge4

theorem kuhn4_hinge4_gram_S : gram3S kd4 0 3 4 1 = 2 := by
  simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num

theorem kuhn4_hinge4_gram_U : gram3S kd4 0 3 4 2 = 2 := by
  simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num

theorem kuhn4_hinge4_mixed : mixedS kd4 0 3 4 1 2 = 1 := by
  simp [mixedS, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num

/-- **Explicit first variation of the hinge angle 4 of the orthoscheme**: the angle at the triangle
`(0,3,4)` between the tetrahedra omitting `2` and `1`. -/
theorem kuhn4_hinge4_deriv (δ : Fin 5 → Fin 5 → ℝ) :
    HasDerivAt (fun ε : ℝ => dihS (fun x y => kd4 x y + ε * δ x y) 0 3 4 1 2)
      (-(-(1 / 2) * δ 0 3 - (1 / 8) * δ 3 3 + (3 / 4) * δ 0 2 + (1 / 4) * δ 3 2
          - (3 / 2) * δ 1 2 + (7 / 8) * δ 1 3 - (1 / 8) * δ 3 1 + (3 / 8) * δ 1 1
          + (3 / 8) * δ 2 2 - (1 / 4) * δ 2 3) / √3) 0 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h3p : 0 < √3 := by positivity
  have hc : cosS kd4 0 3 4 1 2 = 1 / 2 := by
    rw [cosS, kuhn4_hinge4_gram_S, kuhn4_hinge4_gram_U, kuhn4_hinge4_mixed]
    rw [show (2 : ℝ) * 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have key := hasDerivAt_dihS kd4 δ 0 3 4 1 2 (by rw [kuhn4_hinge4_gram_S]; norm_num)
    (by rw [kuhn4_hinge4_gram_U]; norm_num)
    (by rw [hc]; norm_num) (by rw [hc]; norm_num)
  convert key using 1
  rw [kuhn4_hinge4_gram_S, kuhn4_hinge4_gram_U, kuhn4_hinge4_mixed, hc]
  have h5 : √(1 - (1 / 2 : ℝ) ^ 2) = √3 / 2 := by
    rw [show 1 - (1 / 2 : ℝ) ^ 2 = (√3 / 2) * (√3 / 2) by nlinarith,
      Real.sqrt_mul_self (by positivity)]
  have h4 : √((2 : ℝ) * 2) = 2 := by
    rw [show (2 : ℝ) * 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h5, h4]
  simp [gram3S', mixedS', ipS, det3, kd4, kv4, Fin.sum_univ_four]
  field_simp
  ring_nf

theorem kuhn4_hinge7_gram_S : gram3S kd4 0 1 4 2 = 2 := by
  simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num

theorem kuhn4_hinge7_gram_U : gram3S kd4 0 1 4 3 = 2 := by
  simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num

theorem kuhn4_hinge7_mixed : mixedS kd4 0 1 4 2 3 = 1 := by
  simp [mixedS, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num

/-- **Explicit first variation of the hinge angle 7 of the orthoscheme**: the angle at the triangle
`(0,1,4)` between the tetrahedra omitting `3` and `2`. -/
theorem kuhn4_hinge7_deriv (δ : Fin 5 → Fin 5 → ℝ) :
    HasDerivAt (fun ε : ℝ => dihS (fun x y => kd4 x y + ε * δ x y) 0 1 4 2 3)
      (-(-(1 / 8) * δ 1 1 - (1 / 2) * δ 1 4 + (7 / 8) * δ 1 3 - (1 / 8) * δ 4 4
          + (1 / 4) * δ 4 3 - (3 / 2) * δ 2 3 + (7 / 8) * δ 2 4 + (1 / 4) * δ 2 1
          - (1 / 4) * δ 1 2 - (1 / 8) * δ 4 2 + (3 / 8) * δ 2 2 + (3 / 8) * δ 3 3
          - (1 / 4) * δ 3 4 - (1 / 8) * δ 3 1) / √3) 0 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h3p : 0 < √3 := by positivity
  have hc : cosS kd4 0 1 4 2 3 = 1 / 2 := by
    rw [cosS, kuhn4_hinge7_gram_S, kuhn4_hinge7_gram_U, kuhn4_hinge7_mixed]
    rw [show (2 : ℝ) * 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have key := hasDerivAt_dihS kd4 δ 0 1 4 2 3 (by rw [kuhn4_hinge7_gram_S]; norm_num)
    (by rw [kuhn4_hinge7_gram_U]; norm_num)
    (by rw [hc]; norm_num) (by rw [hc]; norm_num)
  convert key using 1
  rw [kuhn4_hinge7_gram_S, kuhn4_hinge7_gram_U, kuhn4_hinge7_mixed, hc]
  have h5 : √(1 - (1 / 2 : ℝ) ^ 2) = √3 / 2 := by
    rw [show 1 - (1 / 2 : ℝ) ^ 2 = (√3 / 2) * (√3 / 2) by nlinarith,
      Real.sqrt_mul_self (by positivity)]
  have h4 : √((2 : ℝ) * 2) = 2 := by
    rw [show (2 : ℝ) * 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h5, h4]
  simp [gram3S', mixedS', ipS, det3, kd4, kv4, Fin.sum_univ_four]
  field_simp
  ring_nf

theorem kuhn4_hinge9_gram_S : gram3S kd4 0 1 2 3 = 1 := by
  simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num

theorem kuhn4_hinge9_gram_U : gram3S kd4 0 1 2 4 = 2 := by
  simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num

theorem kuhn4_hinge9_mixed : mixedS kd4 0 1 2 3 4 = 1 := by
  simp [mixedS, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num

/-- **Explicit first variation of the hinge angle 9 of the orthoscheme**: the angle at the triangle
`(0,1,2)` between the tetrahedra omitting `4` and `3`. -/
theorem kuhn4_hinge9_deriv (δ : Fin 5 → Fin 5 → ℝ) :
    HasDerivAt (fun ε : ℝ => dihS (fun x y => kd4 x y + ε * δ x y) 0 1 2 3 4)
      (-(-(1 / 8) * δ 2 2 + (3 / 8) * δ 2 4 - (1 / 2) * δ 3 4 + (1 / 4) * δ 3 2
          - (1 / 4) * δ 2 3 + (1 / 4) * δ 3 3 + (1 / 8) * δ 4 4 - (1 / 8) * δ 4 2)) 0 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2p : 0 < √2 := by positivity
  have h22 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : cosS kd4 0 1 2 3 4 = √2 / 2 := by
    rw [cosS, kuhn4_hinge9_gram_S, kuhn4_hinge9_gram_U, kuhn4_hinge9_mixed, one_mul]
    field_simp
    nlinarith
  have key := hasDerivAt_dihS kd4 δ 0 1 2 3 4 (by rw [kuhn4_hinge9_gram_S]; norm_num)
    (by rw [kuhn4_hinge9_gram_U]; norm_num)
    (by rw [hc]; intro H; nlinarith) (by rw [hc]; intro H; nlinarith)
  convert key using 1
  rw [kuhn4_hinge9_gram_S, kuhn4_hinge9_gram_U, kuhn4_hinge9_mixed, hc, one_mul]
  have h5 : √(1 - (√2 / 2) ^ 2) = √2 / 2 := by
    rw [show 1 - (√2 / 2) ^ 2 = (√2 / 2) * (√2 / 2) by nlinarith,
      Real.sqrt_mul_self (by positivity)]
  rw [h5]
  simp [gram3S', mixedS', ipS, det3, kd4, kv4, Fin.sum_univ_four]
  field_simp
  ring_nf
  rw [h22]
  ring_nf

end Lightlike.Regge4
