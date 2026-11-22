module

public import Lightlike.Lorentz.SL2R

/-!
# The hyperbolic radius on SL(2,ℝ)

For `g ∈ SL(2,ℝ)` put `cosh d(g) = (a² + b² + c² + d²) / 2`, the hyperbolic cosine of the
distance from `i` to `g · i` in the upper half-plane. It is the first ingredient of the
bi-`SO(2)`-invariant (spherical) Plancherel formula of `SL(2,ℝ)` (milestone HA3), as
`Lightlike.Lorentz.coshDist` is for `SL(2,ℂ)`.

* `coshDistR_eq_of_toSL2R`: on the Iwasawa section it is `(x² + y² + 1) / (2y)`.
* `one_le_coshDistR`: it is at least `1`.
* `coshDistR_rot_mul`, `coshDistR_mul_rot`: it is bi-`SO(2)`-invariant.
-/

@[expose] public section

open Matrix UpperHalfPlane

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- **The hyperbolic cosine of the radius** of `g ∈ SL(2,ℝ)`: `(a² + b² + c² + d²) / 2`, the
hyperbolic cosine of the distance from `i` to `g · i`. -/
def coshDistR (g : SL2R) : ℝ :=
  (g 0 0 ^ 2 + g 0 1 ^ 2 + g 1 0 ^ 2 + g 1 1 ^ 2) / 2

lemma continuous_coshDistR : Continuous coshDistR := by
  unfold coshDistR
  have h : ∀ i j : Fin 2, Continuous fun g : SL2R => g i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  have := h 0 0
  have := h 0 1
  have := h 1 0
  have := h 1 1
  fun_prop

/-- `cosh d ≥ 1`, with the determinant condition `ad − bc = 1`. -/
lemma one_le_coshDistR (g : SL2R) : 1 ≤ coshDistR g := by
  have h := det_eq g
  unfold coshDistR
  nlinarith [sq_nonneg (g 0 0 - g 1 1), sq_nonneg (g 0 1 + g 1 0)]

/-- Left invariance under rotations. -/
lemma coshDistR_rot_mul (θ : ℝ) (g : SL2R) : coshDistR (rot θ * g) = coshDistR g := by
  have h := Real.sin_sq_add_cos_sq θ
  simp only [coshDistR, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    coe_rot, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  linear_combination (g 0 0 ^ 2 + g 0 1 ^ 2 + g 1 0 ^ 2 + g 1 1 ^ 2) / 2 * h

/-- Right invariance under rotations. -/
lemma coshDistR_mul_rot (g : SL2R) (θ : ℝ) : coshDistR (g * rot θ) = coshDistR g := by
  have h := Real.sin_sq_add_cos_sq θ
  simp only [coshDistR, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    coe_rot, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  linear_combination (g 0 0 ^ 2 + g 0 1 ^ 2 + g 1 0 ^ 2 + g 1 1 ^ 2) / 2 * h

/-- On the Iwasawa section, `cosh d(g_z) = (x² + y² + 1) / (2y)` for `z = x + iy`. -/
lemma coshDistR_toSL2R (z : ℍ) :
    coshDistR z.toSL2R = (z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im) := by
  have hy := z.im_pos
  have hs : Real.sqrt z.im ^ 2 = z.im := Real.sq_sqrt hy.le
  have hs0 : Real.sqrt z.im ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  simp only [coshDistR, coe_toSL2R, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  have h4 : Real.sqrt z.im ^ 4 = z.im ^ 2 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hs]
  field_simp
  rw [h4, hs]
  ring

/-- The radius of `g` is that of its Iwasawa point: `cosh d(g_z rot θ) = (x² + y² + 1) / (2y)`. -/
lemma coshDistR_iwasawa (p : ℍ × ℝ) :
    coshDistR (iwasawa p) = (p.1.re ^ 2 + p.1.im ^ 2 + 1) / (2 * p.1.im) := by
  rw [iwasawa, coshDistR_mul_rot, coshDistR_toSL2R]

end Lightlike.Lorentz.SL2R
