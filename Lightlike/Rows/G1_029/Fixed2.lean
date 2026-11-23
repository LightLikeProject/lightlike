import Lightlike.Rows.G1_029.Fixed

/-!
# Quintessence with an exponential potential: existence conditions of the fixed points

Row G1-029 (milestone CO17).  Continuation of `Fixed.lean`: when do the scalar-field-dominated point
`sfPoint` and the scaling point `scPoint` lie in the closed half disc `x² + y² ≤ 1`, and when do they
coincide?  Here `γ = 1 + w_m` is the matter parameter and `λ` the slope of the potential
(copeland-2006, eq. (175) ff.).

## Main statements

* `sfPoint_mem_disc_iff`: `sfPoint` lies in the disc iff `λ² ≤ 6` (then it lies on the circle).
* `scPoint_mem_disc_iff`: for `0 ≤ γ ≤ 2`, `λ ≠ 0`, `scPoint` lies in the disc iff `3γ ≤ λ²`.
* `scPoint_eq_sfPoint_iff`: for `0 ≤ γ ≤ 2`, `λ ≠ 0`, the two points coincide iff `λ² = 3γ`
  (for dust, `γ = 1`, this is `λ² = 3`).

## References

* copeland-2006
-/

namespace Lightlike.Rows.G1_029

noncomputable section

/-- The scalar-field-dominated point lies on the unit circle when `λ² ≤ 6`. -/
lemma sfPoint_norm_sq {l : ℝ} (hl : l ^ 2 ≤ 6) :
    (sfPoint l).1 ^ 2 + (sfPoint l).2 ^ 2 = 1 := by
  have hm : (c32 * l) ^ 2 = 3 / 2 * l ^ 2 := by rw [mul_pow, c32_sq]
  have hx : (sfPoint l).1 = c32 * l / 3 := rfl
  have hy : (sfPoint l).2 ^ 2 = 1 - (c32 * l) ^ 2 / 9 := by
    simp only [sfPoint]
    rw [Real.sq_sqrt (by rw [hm]; linarith)]
  rw [hx, hy]; ring

/-- The scalar-field-dominated point lies in the closed half disc iff `λ² ≤ 6`. -/
theorem sfPoint_mem_disc_iff {l : ℝ} :
    (sfPoint l).1 ^ 2 + (sfPoint l).2 ^ 2 ≤ 1 ↔ l ^ 2 ≤ 6 := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hm : (c32 * l) ^ 2 = 3 / 2 * l ^ 2 := by rw [mul_pow, c32_sq]
    have hx : (sfPoint l).1 ^ 2 = (c32 * l) ^ 2 / 9 := by
      simp only [sfPoint]; ring
    have hy : (sfPoint l).2 = 0 := by
      simp only [sfPoint]
      apply Real.sqrt_eq_zero_of_nonpos
      rw [hm]; linarith
    rw [hx, hy, hm] at h
    nlinarith
  · intro h
    exact (sfPoint_norm_sq h).le

/-- The scaling point has `x² + y² = 3γ/λ²` for `0 ≤ γ ≤ 2` (this is `Ω_φ`). -/
lemma scPoint_norm_sq {l γ : ℝ} (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) (hl : l ≠ 0) :
    (scPoint l γ).1 ^ 2 + (scPoint l γ).2 ^ 2 = 3 * γ / l ^ 2 := by
  have h2 := c32_sq
  have hpos : 0 ≤ 3 * (2 - γ) * γ / (2 * l ^ 2) := by
    have : 0 ≤ 2 - γ := by linarith
    positivity
  simp only [scPoint]
  rw [Real.sq_sqrt hpos, div_pow, mul_pow, h2]
  field_simp
  ring

/-- For `0 ≤ γ ≤ 2` and `λ ≠ 0`, the scaling point lies in the closed half disc iff `3γ ≤ λ²`. -/
theorem scPoint_mem_disc_iff {l γ : ℝ} (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) (hl : l ≠ 0) :
    (scPoint l γ).1 ^ 2 + (scPoint l γ).2 ^ 2 ≤ 1 ↔ 3 * γ ≤ l ^ 2 := by
  have hl2 : 0 < l ^ 2 := by positivity
  rw [scPoint_norm_sq hγ hγ2 hl, div_le_one hl2]

/-- For `0 ≤ γ ≤ 2` and `λ ≠ 0`, the scaling point equals the scalar-field-dominated point iff
`λ² = 3γ` (for `γ = 1` this is `λ² = 3`). -/
theorem scPoint_eq_sfPoint_iff {l γ : ℝ} (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) (hl : l ≠ 0) :
    scPoint l γ = sfPoint l ↔ l ^ 2 = 3 * γ := by
  have hc := c32_pos
  have h2 := c32_sq
  have hl2 : 0 < l ^ 2 := by positivity
  constructor
  · intro h
    have hx : c32 * γ / l = c32 * l / 3 := congrArg Prod.fst h
    field_simp at hx
    linarith
  · intro h
    have hm : (c32 * l) ^ 2 = 3 / 2 * l ^ 2 := by rw [mul_pow, h2]
    refine Prod.ext ?_ ?_
    · show c32 * γ / l = c32 * l / 3
      field_simp
      linarith
    · show Real.sqrt (3 * (2 - γ) * γ / (2 * l ^ 2)) = Real.sqrt (1 - (c32 * l) ^ 2 / 9)
      congr 1
      rw [hm, h]
      have hγ0 : γ ≠ 0 := by
        rintro rfl
        simp at h
        exact hl h
      field_simp
      ring

end

end Lightlike.Rows.G1_029
