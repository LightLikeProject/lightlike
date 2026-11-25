import Lightlike.Cosmology.QuintessenceFixedPoints.Fixed2

/-!
# Quintessence with an exponential potential: the equation of state at the fixed points

Row G1-029 (milestone CO17).  With `x = φ̇/(√6 H)`, `y = √V/(√3 H)` the equation-of-state parameter
of the scalar field is `w_φ = (x² - y²)/(x² + y²)`.  We evaluate it at the fixed points of
`Fixed.lean` (copeland-2006, eq. (175) ff.).

## Main statements

* `wphi_sfPoint`: at the scalar-field-dominated point, `w_φ = -1 + λ²/3` (for `λ² ≤ 6`).
* `wphi_kin_pos`, `wphi_kin_neg`: at the kinetic points `(±1, 0)`, `w_φ = 1`.
* `wphi_scPoint`: at the scaling point, `w_φ = γ - 1 = w_m` (for `0 < γ ≤ 2`, `λ ≠ 0`).

## References

* copeland-2006
-/

namespace Lightlike.Cosmology.QuintessenceFixedPoints

noncomputable section

/-- The equation-of-state parameter `w_φ = (x² - y²)/(x² + y²)` of the scalar field in the
variables `x, y`. -/
def wphi (x y : ℝ) : ℝ := (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2)

/-- At the scalar-field-dominated point, `w_φ = -1 + λ²/3`. -/
theorem wphi_sfPoint {l : ℝ} (hl : l ^ 2 ≤ 6) :
    wphi (sfPoint l).1 (sfPoint l).2 = -1 + l ^ 2 / 3 := by
  have hn := sfPoint_norm_sq hl
  have hx : (sfPoint l).1 ^ 2 = l ^ 2 / 6 := by
    have : (sfPoint l).1 = c32 * l / 3 := rfl
    rw [this, div_pow, mul_pow, c32_sq]; ring
  unfold wphi
  rw [hn, div_one]
  have hy : (sfPoint l).2 ^ 2 = 1 - (sfPoint l).1 ^ 2 := by linarith
  rw [hy, hx]; ring

/-- At the kinetic point `(1, 0)`, `w_φ = 1`. -/
theorem wphi_kin_pos : wphi 1 0 = 1 := by norm_num [wphi]

/-- At the kinetic point `(-1, 0)`, `w_φ = 1`. -/
theorem wphi_kin_neg : wphi (-1) 0 = 1 := by norm_num [wphi]

/-- At the scaling point, `w_φ = γ - 1`, the equation of state of the matter fluid. -/
theorem wphi_scPoint {l γ : ℝ} (hγ : 0 < γ) (hγ2 : γ ≤ 2) (hl : l ≠ 0) :
    wphi (scPoint l γ).1 (scPoint l γ).2 = γ - 1 := by
  have h2 := c32_sq
  have hpos : 0 ≤ 3 * (2 - γ) * γ / (2 * l ^ 2) := by
    have : 0 ≤ 2 - γ := by linarith
    positivity
  have hx : (scPoint l γ).1 ^ 2 = 3 * γ ^ 2 / (2 * l ^ 2) := by
    simp only [scPoint]
    rw [div_pow, mul_pow, h2]; field_simp
  have hy : (scPoint l γ).2 ^ 2 = 3 * (2 - γ) * γ / (2 * l ^ 2) := by
    simp only [scPoint]
    rw [Real.sq_sqrt hpos]
  unfold wphi
  rw [hx, hy]
  have hγ' : γ ≠ 0 := hγ.ne'
  field_simp
  ring

end

end Lightlike.Cosmology.QuintessenceFixedPoints

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.wphi := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.wphi
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.wphi_kin_neg := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.wphi_kin_neg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.wphi_kin_pos := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.wphi_kin_pos
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.wphi_scPoint := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.wphi_scPoint
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.wphi_sfPoint := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.wphi_sfPoint
