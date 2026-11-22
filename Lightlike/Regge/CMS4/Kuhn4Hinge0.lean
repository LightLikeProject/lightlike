import Lightlike.Regge.CMS4.Kuhn4Deriv

/-!
# The first variation of the first hinge angle of the orthoscheme, explicitly

Smoke test for the explicit evaluation of `hasDerivAt_dihS` at `kd4`: for the hinge `(2,3,4)` with
omitted vertices `0, 1` (angle `π/4`) the derivative along `kd4 + ε δ` is a linear form in `δ`
with rational coefficients. The same recipe (values of the two Gram determinants and of the mixed
determinant, `√(1 - cos²)`, then `field_simp` and `ring_nf`) gives the other nine hinges.
-/

open Real

namespace Lightlike.Regge4

theorem kuhn4_hinge0_gram_S : gram3S kd4 2 3 4 0 = 2 := by
  simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four]; norm_num

theorem kuhn4_hinge0_gram_U : gram3S kd4 2 3 4 1 = 1 := by
  simp [gram3S, ipS, det3, kd4, kv4, Fin.sum_univ_four]

theorem kuhn4_hinge0_mixed : mixedS kd4 2 3 4 0 1 = 1 := by
  simp [mixedS, ipS, det3, kd4, kv4, Fin.sum_univ_four]

/-- **Explicit first variation of the first hinge angle of the orthoscheme.** Along `kd4 + ε δ`
the angle at the triangle `(2,3,4)` between the tetrahedra omitting `1` and `0` has derivative
`-(2 δ₂₀ - 4 δ₀₁ + δ₀₀ + 2 δ₁₁) / 8` at `ε = 0`. -/
theorem kuhn4_hinge0_deriv (δ : Fin 5 → Fin 5 → ℝ) :
    HasDerivAt (fun ε : ℝ => dihS (fun x y => kd4 x y + ε * δ x y) 2 3 4 0 1)
      (-(2 * δ 2 0 - 4 * δ 0 1 + δ 0 0 + 2 * δ 1 1) / 8) 0 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2p : 0 < √2 := by positivity
  have h22 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : cosS kd4 2 3 4 0 1 = √2 / 2 := by
    rw [cosS, kuhn4_hinge0_gram_S, kuhn4_hinge0_gram_U, kuhn4_hinge0_mixed, mul_one]
    field_simp
    nlinarith
  have key := hasDerivAt_dihS kd4 δ 2 3 4 0 1 (by rw [kuhn4_hinge0_gram_S]; norm_num)
    (by rw [kuhn4_hinge0_gram_U]; norm_num)
    (by rw [hc]; intro H; nlinarith) (by rw [hc]; intro H; nlinarith)
  convert key using 1
  rw [kuhn4_hinge0_gram_S, kuhn4_hinge0_gram_U, kuhn4_hinge0_mixed, hc, mul_one]
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
