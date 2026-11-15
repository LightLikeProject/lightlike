import Mathlib
import Lightlike.Regge.CMS.Winding
import Lightlike.Regge.CMS.NormalCoord

/-!
# The angles of a frozen-metric star add up to `2π` (RC6b, step 5)

The angles at a vertex `v`, computed from the squared lengths of the flat metric `G = g(v)`, are the
Euclidean angles of the star under a linear map `A` with `Aᵀ A = G` (a Cholesky factor, which
preserves orientation). This file builds `A` as `z ↦ α z + β z̄` on `ℂ` and applies
`sum_angle_linear`.

## Main results

* `exists_chol`: a symmetric positive definite `2 × 2` matrix is `Mᵀ M` for `M = [[p, q], [0, r]]`.
* `normSq_lin_eq_ip`: `|A z|² = z · G z`.
* `sum_triAngle_gram`: for a positively oriented star `u` winding once (angles adding up to `2π`),
  the angles computed from the squared lengths `u i · G u i`, `u (i+1) · G u (i+1)` and
  `(u (i+1) - u i) · G (u (i+1) - u i)` add up to `2π`.
-/

open Complex Real

namespace Lightlike.CMS

/-- The coordinates `(z 0, z 1)` as a complex number. -/
def toC (z : Fin 2 → ℝ) : ℂ := ⟨z 0, z 1⟩

theorem toC_sub (z z' : Fin 2 → ℝ) : toC (z - z') = toC z - toC z' := by
  apply Complex.ext <;> simp [toC]

theorem exists_chol {G : Matrix (Fin 2) (Fin 2) ℝ} (h00 : 0 < G 0 0)
    (hdet : 0 < G 0 0 * G 1 1 - G 0 1 ^ 2) :
    ∃ p q r : ℝ, 0 < p ∧ 0 < r ∧ G 0 0 = p ^ 2 ∧ G 0 1 = p * q ∧ G 1 1 = q ^ 2 + r ^ 2 := by
  have hp : 0 < √(G 0 0) := Real.sqrt_pos.mpr h00
  have hp2 : √(G 0 0) ^ 2 = G 0 0 := Real.sq_sqrt h00.le
  set p := √(G 0 0)
  set q := G 0 1 / p with hq
  have hr : 0 < G 1 1 - q ^ 2 := by
    have : G 1 1 - q ^ 2 = (G 0 0 * G 1 1 - G 0 1 ^ 2) / G 0 0 := by
      rw [hq, div_pow, hp2]; field_simp
    rw [this]; positivity
  refine ⟨p, q, √(G 1 1 - q ^ 2), hp, Real.sqrt_pos.mpr hr, hp2.symm, ?_, ?_⟩
  · rw [hq]; field_simp
  · rw [Real.sq_sqrt hr.le]; ring

/-- The orientation preserving linear map `z ↦ M z`, `M = [[p, q], [0, r]]`, as `z ↦ α z + β z̄`. -/
noncomputable def cholα (p q r : ℝ) : ℂ := ⟨(p + r) / 2, -q / 2⟩

/-- See `cholα`. -/
noncomputable def cholβ (p q r : ℝ) : ℂ := ⟨(p - r) / 2, q / 2⟩

theorem norm_cholβ_lt {p q r : ℝ} (hp : 0 < p) (hr : 0 < r) :
    ‖cholβ p q r‖ < ‖cholα p q r‖ := by
  have h : ‖cholβ p q r‖ ^ 2 < ‖cholα p q r‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [cholα, cholβ]
    nlinarith [mul_pos hp hr]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h

theorem normSq_lin_eq_ip {G : Matrix (Fin 2) (Fin 2) ℝ} {p q r : ℝ} (hs : G 0 1 = G 1 0)
    (h00 : G 0 0 = p ^ 2) (h01 : G 0 1 = p * q) (h11 : G 1 1 = q ^ 2 + r ^ 2) (z : Fin 2 → ℝ) :
    ‖lin (cholα p q r) (cholβ p q r) 1 (toC z)‖ ^ 2 = CMS.ip G z z := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [lin, cholα, cholβ, toC, CMS.ip, Fin.sum_univ_two, Complex.add_re, Complex.mul_re,
    Complex.mul_im, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_one, one_mul]
  have h10 : G 1 0 = p * q := hs ▸ h01
  rw [h00, h01, h10, h11]
  ring

theorem lin_sub (α β : ℂ) (a b : ℂ) : lin α β 1 (a - b) = lin α β 1 a - lin α β 1 b := by
  simp only [lin, map_sub]; ring

/-- **The angles of a frozen-metric star add up to `2π`.** -/
theorem sum_triAngle_gram {n : ℕ} [NeZero n] {G : Matrix (Fin 2) (Fin 2) ℝ} (hs : G 0 1 = G 1 0)
    (h00 : 0 < G 0 0) (hdet : 0 < G 0 0 * G 1 1 - G 0 1 ^ 2) {u : ZMod n → Fin 2 → ℝ}
    (hu : IsPosStar (fun i => toC (u i)))
    (h2π : ∑ i, InnerProductGeometry.angle (toC (u i)) (toC (u (i + 1))) = 2 * π) :
    ∑ i, triAngle (CMS.ip G (u i) (u i)) (CMS.ip G (u (i + 1)) (u (i + 1)))
      (CMS.ip G (u (i + 1) - u i) (u (i + 1) - u i)) = 2 * π := by
  obtain ⟨p, q, r, hp, hr, h00', h01, h11⟩ := exists_chol h00 hdet
  have hβ := norm_cholβ_lt (q := q) hp hr
  have key := sum_angle_linear hu hβ
  rw [h2π] at key
  rw [← key]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := triAngle_eq_angle (lin (cholα p q r) (cholβ p q r) 1 (toC (u i))) 0
    (lin (cholα p q r) (cholβ p q r) 1 (toC (u (i + 1))))
  rw [dist_zero_right, dist_zero_right] at e
  have e3 : dist (lin (cholα p q r) (cholβ p q r) 1 (toC (u i)))
      (lin (cholα p q r) (cholβ p q r) 1 (toC (u (i + 1)))) ^ 2 =
      CMS.ip G (u (i + 1) - u i) (u (i + 1) - u i) := by
    rw [dist_comm, dist_eq_norm, ← lin_sub, ← toC_sub]
    exact normSq_lin_eq_ip hs h00' h01 h11 _
  rw [normSq_lin_eq_ip hs h00' h01 h11, normSq_lin_eq_ip hs h00' h01 h11, e3] at e
  rw [e]
  simp [EuclideanGeometry.angle]

/-- **Non-vacuity.** The four axis vectors form a star that winds once, and under the stretched
metric `diag(2, 1)` the angles computed from the squared lengths still add up to `2π`. -/
example : ∑ i : ZMod 4, triAngle
    (CMS.ip !![(2 : ℝ), 0; 0, 1] (![(axisStar i).re, (axisStar i).im])
      (![(axisStar i).re, (axisStar i).im]))
    (CMS.ip !![(2 : ℝ), 0; 0, 1] (![(axisStar (i + 1)).re, (axisStar (i + 1)).im])
      (![(axisStar (i + 1)).re, (axisStar (i + 1)).im]))
    (CMS.ip !![(2 : ℝ), 0; 0, 1]
      (![(axisStar (i + 1)).re, (axisStar (i + 1)).im] - ![(axisStar i).re, (axisStar i).im])
      (![(axisStar (i + 1)).re, (axisStar (i + 1)).im] - ![(axisStar i).re, (axisStar i).im])) =
    2 * π := by
  have hto : ∀ i, toC ![(axisStar i).re, (axisStar i).im] = axisStar i := fun i => by
    apply Complex.ext <;> simp [toC]
  have e0 : (0 : ZMod 4) + 1 = 1 := by decide
  have e1 : (1 : ZMod 4) + 1 = 2 := by decide
  have e2 : (2 : ZMod 4) + 1 = 3 := by decide
  have e3 : (3 : ZMod 4) + 1 = 0 := by decide
  have hang : ∀ i : ZMod 4, InnerProductGeometry.angle (axisStar i) (axisStar (i + 1)) = π / 2 := by
    intro i
    rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
    rcases hi with rfl | rfl | rfl | rfl <;> simp [axisStar, e0, e1, e2, e3, Complex.inner]
  refine sum_triAngle_gram (G := !![(2 : ℝ), 0; 0, 1]) (by simp) (by simp) (by simp)
    (u := fun i => ![(axisStar i).re, (axisStar i).im]) ?_ ?_
  · intro i; simp only [hto]; exact axisStar_isPosStar i
  · simp only [hto, hang]; simp; ring

end Lightlike.CMS
