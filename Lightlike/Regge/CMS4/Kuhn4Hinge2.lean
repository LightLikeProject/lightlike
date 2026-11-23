import Lightlike.Regge.CMS4.Kuhn4Hinge1

/-!
# First variation of the right-angle hinges `5, 6, 8` of the orthoscheme

Same recipe as for the hinges `1, 2, 3`: the angle is `π/2`, so only the mixed determinant varies.
The squared edge lengths are perturbed by `ε δ` with a general `δ`, not assumed symmetric.
-/

open Real

namespace Lightlike.Regge4

/-- Hinge `5`: triangle `(0,2,4)`, omitted vertices `1, 3`; derivative `-m'/2`. -/
theorem kuhn4_hinge5_deriv (δ : Fin 5 → Fin 5 → ℝ) :
    HasDerivAt (fun ε : ℝ => dihS (fun x y => kd4 x y + ε * δ x y) 0 2 4 1 3)
      (-(-(δ 0 2 + δ 2 2 + δ 0 4 + δ 2 4) / 2 + δ 2 3 + δ 0 3 - δ 1 3 * 2 + δ 1 4 + δ 1 2) / 2) 0 := by
  have g1 : gram3S kd4 0 2 4 1 = 2 := by
    simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num
  have g2 : gram3S kd4 0 2 4 3 = 2 := by
    simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num
  have hm : mixedS kd4 0 2 4 1 3 = 0 := by
    simp [mixedS, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num
  have key := hasDerivAt_dihS_cos0 kd4 δ 0 2 4 1 3 (by rw [g1]; norm_num) (by rw [g2]; norm_num) hm
  convert key using 1
  rw [g1, g2, show mixedS' kd4 δ 0 2 4 1 3
    = -(δ 0 2 + δ 2 2 + δ 0 4 + δ 2 4) / 2 + δ 2 3 + δ 0 3 - δ 1 3 * 2 + δ 1 4 + δ 1 2 by
    simp [mixedS', ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num; ring]
  rw [show (2 : ℝ) * 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Hinge `6`: triangle `(0,2,3)`, omitted vertices `1, 4`; derivative `-m'/√2`. -/
theorem kuhn4_hinge6_deriv (δ : Fin 5 → Fin 5 → ℝ) :
    HasDerivAt (fun ε : ℝ => dihS (fun x y => kd4 x y + ε * δ x y) 0 2 3 1 4)
      (-(-(δ 0 3 + δ 2 3) / 2 + (δ 0 4 + δ 2 4) / 2 - δ 1 4 + δ 1 3) / √2) 0 := by
  have g1 : gram3S kd4 0 2 3 1 = 1 := by
    simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num
  have g2 : gram3S kd4 0 2 3 4 = 2 := by
    simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num
  have hm : mixedS kd4 0 2 3 1 4 = 0 := by
    simp [mixedS, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num
  have key := hasDerivAt_dihS_cos0 kd4 δ 0 2 3 1 4 (by rw [g1]; norm_num) (by rw [g2]; norm_num) hm
  convert key using 1
  rw [g1, g2, show mixedS' kd4 δ 0 2 3 1 4
    = -(δ 0 3 + δ 2 3) / 2 + (δ 0 4 + δ 2 4) / 2 - δ 1 4 + δ 1 3 by
    simp [mixedS', ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num; ring]
  norm_num

/-- Hinge `8`: triangle `(0,1,3)`, omitted vertices `2, 4`; derivative `-m'/√2`. -/
theorem kuhn4_hinge8_deriv (δ : Fin 5 → Fin 5 → ℝ) :
    HasDerivAt (fun ε : ℝ => dihS (fun x y => kd4 x y + ε * δ x y) 0 1 3 2 4)
      (-(-(δ 1 3 + δ 3 3) / 2 + (δ 1 4 + δ 3 4) / 2 - δ 2 4 + δ 2 3) / √2) 0 := by
  have g1 : gram3S kd4 0 1 3 2 = 1 := by
    simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num
  have g2 : gram3S kd4 0 1 3 4 = 2 := by
    simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num
  have hm : mixedS kd4 0 1 3 2 4 = 0 := by
    simp [mixedS, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num
  have key := hasDerivAt_dihS_cos0 kd4 δ 0 1 3 2 4 (by rw [g1]; norm_num) (by rw [g2]; norm_num) hm
  convert key using 1
  rw [g1, g2, show mixedS' kd4 δ 0 1 3 2 4
    = -(δ 1 3 + δ 3 3) / 2 + (δ 1 4 + δ 3 4) / 2 - δ 2 4 + δ 2 3 by
    simp [mixedS', ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num; ring]
  norm_num

end Lightlike.Regge4
