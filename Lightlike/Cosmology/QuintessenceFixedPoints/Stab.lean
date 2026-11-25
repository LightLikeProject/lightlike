import Mathlib
import Lightlike.Cosmology.QuintessenceFixedPoints.Fixed

/-!
# Quintessence with an exponential potential: the Jacobian at the fixed points

Row G1-029 (milestone CO17), continuation of `Fixed.lean`.  We write the Jacobian of the vector field
`(vfx, vfy)` of `Fixed.lean`, prove that its entries are the partial derivatives, and compute its trace and
determinant at the matter point, the two kinetic points, the scalar-field-dominated point and the scaling
point.  The eigenvalues are the roots of `z² - tr z + det`; the linearised-stability criterion (DS1) is
not proved here.

## Main definitions

* `jxx`, `jxy`, `jyx`, `jyy`: the entries of the Jacobian; `jtr`, `jdet`: its trace and determinant.

## Main statements

* `hasDerivAt_vfx_x` etc.: the entries are the partial derivatives of `vfx`, `vfy`.
* `jtr_sf`, `jdet_sf`, `jtr_sc`, `jdet_sc`, `jtr_kin_pos`, ...: traces and determinants at the fixed points.

## References

* copeland-2006
-/

namespace Lightlike.Rows.G1_029

noncomputable section

/-- `∂vfx/∂x`. -/
def jxx (_μ γ x y : ℝ) : ℝ := -3 + 3 / 2 * aux γ x y + 3 * (2 - γ) * x ^ 2

/-- `∂vfx/∂y`. -/
def jxy (μ γ x y : ℝ) : ℝ := 2 * μ * y - 3 * γ * x * y

/-- `∂vfy/∂x`. -/
def jyx (μ γ x y : ℝ) : ℝ := -μ * y + 3 * (2 - γ) * x * y

/-- `∂vfy/∂y`. -/
def jyy (μ γ x y : ℝ) : ℝ := -μ * x + 3 / 2 * aux γ x y - 3 * γ * y ^ 2

/-- Trace of the Jacobian. -/
def jtr (μ γ x y : ℝ) : ℝ := jxx μ γ x y + jyy μ γ x y

/-- Determinant of the Jacobian. -/
def jdet (μ γ x y : ℝ) : ℝ := jxx μ γ x y * jyy μ γ x y - jxy μ γ x y * jyx μ γ x y

/-! ### The entries are the partial derivatives -/

theorem hasDerivAt_vfx_x (μ γ x y : ℝ) :
    HasDerivAt (fun x => vfx μ γ x y) (jxx μ γ x y) x := by
  have hx : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
  have h1 := (((hx.const_mul (-3)).add_const (μ * y ^ 2)).add
    ((hx.const_mul (3 / 2)).mul
      (((hx.pow 2).const_mul 2).add
        ((((hasDerivAt_const x (1 : ℝ)).sub (hx.pow 2)).sub_const (y ^ 2)).const_mul γ))))
  unfold vfx jxx aux
  convert h1 using 1
  simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring

theorem hasDerivAt_vfx_y (μ γ x y : ℝ) :
    HasDerivAt (fun y => vfx μ γ x y) (jxy μ γ x y) y := by
  have hy : HasDerivAt (fun y : ℝ => y) 1 y := hasDerivAt_id y
  have h1 := ((hasDerivAt_const y (-3 * x)).add ((hy.pow 2).const_mul μ)).add
    ((hasDerivAt_const y (3 / 2 * x)).mul
      ((((hasDerivAt_const y (1 - x ^ 2)).sub (hy.pow 2)).const_mul γ).const_add (2 * x ^ 2)))
  unfold vfx jxy aux
  convert h1 using 1
  simp only [Pi.sub_apply, Pi.pow_apply]; ring

theorem hasDerivAt_vfy_x (μ γ x y : ℝ) :
    HasDerivAt (fun x => vfy μ γ x y) (jyx μ γ x y) x := by
  have hx : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
  have h1 := (hx.const_mul (-μ * y)).add
    ((hasDerivAt_const x (3 / 2 * y)).mul
      (((hx.pow 2).const_mul 2).add
        ((((hasDerivAt_const x (1 : ℝ)).sub (hx.pow 2)).sub_const (y ^ 2)).const_mul γ)))
  unfold vfy jyx aux
  convert h1 using 1
  · funext x; simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]; ring
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring

theorem hasDerivAt_vfy_y (μ γ x y : ℝ) :
    HasDerivAt (fun y => vfy μ γ x y) (jyy μ γ x y) y := by
  have hy : HasDerivAt (fun y : ℝ => y) 1 y := hasDerivAt_id y
  have h1 := (hy.const_mul (-μ * x)).add
    ((hy.const_mul (3 / 2)).mul
      ((((hasDerivAt_const y (1 - x ^ 2)).sub (hy.pow 2)).const_mul γ).const_add (2 * x ^ 2)))
  unfold vfy jyy aux
  convert h1 using 1
  simp only [Pi.sub_apply, Pi.pow_apply]; ring

/-! ### Trace and determinant at the fixed points -/

lemma jdet_eq (μ γ x y : ℝ) :
    jdet μ γ x y = jxx μ γ x y * jyy μ γ x y -
      y ^ 2 * ((2 * μ - 3 * γ * x) * (-μ + 3 * (2 - γ) * x)) := by
  unfold jdet jxy jyx; ring

/-- The matter point `(0, 0)`: `det = -(9/4) γ (2 - γ)`. -/
lemma jdet_origin (μ γ : ℝ) : jdet μ γ 0 0 = -(9 / 4) * (γ * (2 - γ)) := by
  simp [jdet, jxx, jyy, jxy, jyx, aux]; ring

lemma jtr_origin (μ γ : ℝ) : jtr μ γ 0 0 = -3 + 3 * γ := by
  simp [jtr, jxx, jyy, aux]; ring

lemma jtr_kin_pos (μ γ : ℝ) : jtr μ γ 1 0 = 3 * (2 - γ) + (3 - μ) := by
  simp [jtr, jxx, jyy, aux]; ring

lemma jdet_kin_pos (μ γ : ℝ) : jdet μ γ 1 0 = 3 * (2 - γ) * (3 - μ) := by
  unfold jdet jxx jyy jxy jyx aux; ring

lemma jtr_kin_neg (μ γ : ℝ) : jtr μ γ (-1) 0 = 3 * (2 - γ) + (3 + μ) := by
  simp [jtr, jxx, jyy, aux]; ring

lemma jdet_kin_neg (μ γ : ℝ) : jdet μ γ (-1) 0 = 3 * (2 - γ) * (3 + μ) := by
  unfold jdet jxx jyy jxy jyx aux; ring

/-- Trace at the scalar-field-dominated point `(μ/3, y)`, `y² = 1 - μ²/9`. -/
lemma jtr_sf {μ γ y : ℝ} (hy : y ^ 2 = 1 - μ ^ 2 / 9) :
    jtr μ γ (μ / 3) y = μ ^ 2 - 3 - 3 * γ := by
  unfold jtr jxx jyy aux
  rw [hy]; ring

/-- Determinant at the scalar-field-dominated point. -/
lemma jdet_sf {μ γ y : ℝ} (hy : y ^ 2 = 1 - μ ^ 2 / 9) :
    jdet μ γ (μ / 3) y = (μ ^ 2 - 9) * (2 * μ ^ 2 - 9 * γ) / 9 := by
  rw [jdet_eq]
  unfold jxx jyy aux
  rw [hy]; ring

/-- Trace at the scaling point `(3γ/(2μ), y)`, `y² = 9γ(2-γ)/(4μ²)`. -/
lemma jtr_sc {μ γ y : ℝ} (hμ : μ ≠ 0) (hy : y ^ 2 = 9 * γ * (2 - γ) / (4 * μ ^ 2)) :
    jtr μ γ (3 * γ / (2 * μ)) y = -(3 * (2 - γ) / 2) := by
  unfold jtr jxx jyy aux
  rw [hy]; field_simp; ring

/-- Determinant at the scaling point. -/
lemma jdet_sc {μ γ y : ℝ} (hμ : μ ≠ 0) (hy : y ^ 2 = 9 * γ * (2 - γ) / (4 * μ ^ 2)) :
    jdet μ γ (3 * γ / (2 * μ)) y = 9 * γ * (2 - γ) * (2 * μ ^ 2 - 9 * γ) / (4 * μ ^ 2) := by
  rw [jdet_eq]
  unfold jxx jyy aux
  rw [hy]; field_simp; ring

end

end Lightlike.Rows.G1_029
