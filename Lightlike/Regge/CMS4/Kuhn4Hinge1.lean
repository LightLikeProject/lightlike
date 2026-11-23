import Lightlike.Regge.CMS4.Kuhn4Deriv

/-!
# First variation of the right-angle hinges `1, 2, 3` of the orthoscheme

For a hinge whose dihedral angle is `π/2` the mixed determinant vanishes, and the derivative of the
angle is `-m' / √(g_t g_u)`, with `m'` the derivative of the mixed determinant.
-/

open Real

namespace Lightlike.Regge4

/-- Derivative of a right dihedral angle: only the mixed determinant contributes. -/
theorem hasDerivAt_dihS_cos0 (s δ : Fin 5 → Fin 5 → ℝ) (p q r t u : Fin 5)
    (h1 : 0 < gram3S s p q r t) (h2 : 0 < gram3S s p q r u) (hm : mixedS s p q r t u = 0) :
    HasDerivAt (fun ε : ℝ => dihS (fun x y => s x y + ε * δ x y) p q r t u)
      (-(mixedS' s δ p q r t u) / √(gram3S s p q r t * gram3S s p q r u)) 0 := by
  have hc : cosS s p q r t u = 0 := by rw [cosS, hm, zero_div]
  have key := hasDerivAt_dihS s δ p q r t u h1 h2 (by rw [hc]; norm_num) (by rw [hc]; norm_num)
  have hsq : 0 < √(gram3S s p q r t * gram3S s p q r u) := Real.sqrt_pos.2 (mul_pos h1 h2)
  convert key using 1
  rw [hm, hc]
  simp
  field_simp

/-- Hinge `1`: triangle `(1,3,4)`, omitted vertices `0, 2`; derivative `-m'/√2`. -/
theorem kuhn4_hinge1_deriv (δ : Fin 5 → Fin 5 → ℝ) :
    HasDerivAt (fun ε : ℝ => dihS (fun x y => kd4 x y + ε * δ x y) 1 3 4 0 2)
      (-(δ 1 0 / 2 + δ 1 2 - δ 0 2 - δ 1 3 / 2 + δ 0 3 / 2) / √2) 0 := by
  have g1 : gram3S kd4 1 3 4 0 = 2 := by
    simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four] <;> norm_num
  have g2 : gram3S kd4 1 3 4 2 = 1 := by
    simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four] <;> norm_num
  have hm : mixedS kd4 1 3 4 0 2 = 0 := by
    simp [mixedS, ipS, det3, kd4, kv4, Fin.sum_univ_four] <;> norm_num
  have key := hasDerivAt_dihS_cos0 kd4 δ 1 3 4 0 2 (by rw [g1]; norm_num) (by rw [g2]; norm_num) hm
  convert key using 1
  rw [g1, g2, show mixedS' kd4 δ 1 3 4 0 2
    = δ 1 0 / 2 + δ 1 2 - δ 0 2 - δ 1 3 / 2 + δ 0 3 / 2 by
    simp [mixedS', ipS, det3, kd4, kv4, Fin.sum_univ_four] <;> norm_num <;> ring]
  norm_num

/-- Hinge `2`: triangle `(1,2,4)`, omitted vertices `0, 3`; derivative `-m'/√2`. -/
theorem kuhn4_hinge2_deriv (δ : Fin 5 → Fin 5 → ℝ) :
    HasDerivAt (fun ε : ℝ => dihS (fun x y => kd4 x y + ε * δ x y) 1 2 4 0 3)
      (-(δ 1 3 - δ 0 3 - δ 1 4 / 2 + δ 0 4 / 2 - δ 1 2 / 2 + δ 0 2 / 2) / √2) 0 := by
  have g1 : gram3S kd4 1 2 4 0 = 2 := by
    simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four] <;> norm_num
  have g2 : gram3S kd4 1 2 4 3 = 1 := by
    simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four] <;> norm_num
  have hm : mixedS kd4 1 2 4 0 3 = 0 := by
    simp [mixedS, ipS, det3, kd4, kv4, Fin.sum_univ_four] <;> norm_num
  have key := hasDerivAt_dihS_cos0 kd4 δ 1 2 4 0 3 (by rw [g1]; norm_num) (by rw [g2]; norm_num) hm
  convert key using 1
  rw [g1, g2, show mixedS' kd4 δ 1 2 4 0 3
    = δ 1 3 - δ 0 3 - δ 1 4 / 2 + δ 0 4 / 2 - δ 1 2 / 2 + δ 0 2 / 2 by
    simp [mixedS', ipS, det3, kd4, kv4, Fin.sum_univ_four] <;> norm_num <;> ring]
  norm_num

/-- Hinge `3`: triangle `(1,2,3)`, omitted vertices `0, 4`; derivative `-m'`. -/
theorem kuhn4_hinge3_deriv (δ : Fin 5 → Fin 5 → ℝ) :
    HasDerivAt (fun ε : ℝ => dihS (fun x y => kd4 x y + ε * δ x y) 1 2 3 0 4)
      (-(δ 1 4 / 2 - δ 0 4 / 2 - δ 1 3 / 2 + δ 0 3 / 2)) 0 := by
  have g1 : gram3S kd4 1 2 3 0 = 1 := by
    simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four] <;> norm_num
  have g2 : gram3S kd4 1 2 3 4 = 1 := by
    simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four] <;> norm_num
  have hm : mixedS kd4 1 2 3 0 4 = 0 := by
    simp [mixedS, ipS, det3, kd4, kv4, Fin.sum_univ_four] <;> norm_num
  have key := hasDerivAt_dihS_cos0 kd4 δ 1 2 3 0 4 (by rw [g1]; norm_num) (by rw [g2]; norm_num) hm
  convert key using 1
  rw [g1, g2, show mixedS' kd4 δ 1 2 3 0 4
    = δ 1 4 / 2 - δ 0 4 / 2 - δ 1 3 / 2 + δ 0 3 / 2 by
    simp [mixedS', ipS, det3, kd4, kv4, Fin.sum_univ_four] <;> norm_num <;> ring]
  norm_num

end Lightlike.Regge4
