import Mathlib
import Lightlike.Cosmology.QuintessenceFixedPoints.Stab

/-!
# Quintessence with an exponential potential: linear stability of the fixed points

Row G1-029 (milestone CO17), continuation of `Stab.lean`.  A fixed point is *linearly stable* when both
eigenvalues of its Jacobian, the roots of `z² - tr z + det`, have negative real part (this is the
hypothesis of the linearised-stability theorem DS1, which is not proved here).  We prove the
trace–determinant criterion `tr < 0 ∧ 0 < det` and use it to classify the fixed points of the system
of `Fixed.lean` (Copeland–Sami–Tsujikawa 2006, copeland-2006), for `0 < γ < 2`.

## Main statements

* `linStable_iff`: `LinStable tr det ↔ tr < 0 ∧ 0 < det`.
* `origin_saddle`: the matter point has `det < 0` (a saddle) for `0 < γ < 2`.
* `kin_pos_not_stable`, `kin_neg_not_stable`: the kinetic points are never stable.
* `sfPoint_stable_iff`: for `λ² < 6`, the scalar-field-dominated point is stable iff `λ² < 3γ`.
* `scPoint_stable_iff`: for `λ ≠ 0`, the scaling point is stable iff `λ² > 3γ`; it exists in the half disc
  iff `λ² ≥ 3γ`, so at `λ² = 3γ` it merges with `sfPoint` and the stability passes from one to the other.
-/

namespace Lightlike.Cosmology.QuintessenceFixedPoints

noncomputable section

/-- Linear stability of a planar fixed point whose Jacobian has trace `tr` and determinant `det`: both
roots of the characteristic polynomial `z² - tr z + det` (in `ℂ`) have negative real part. -/
def LinStable (tr det : ℝ) : Prop :=
  ∀ z : ℂ, z ^ 2 - (tr : ℂ) * z + (det : ℂ) = 0 → z.re < 0

lemma re_neg_of_root {tr det : ℝ} (htr : tr < 0) (hdet : 0 < det) {z : ℂ}
    (hz : z ^ 2 - (tr : ℂ) * z + (det : ℂ) = 0) : z.re < 0 := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp [pow_two] at hre him
  have him' : z.im * (2 * z.re - tr) = 0 := by linarith
  rcases mul_eq_zero.1 him' with h | h
  · by_contra hc
    push_neg at hc
    rw [h] at hre
    nlinarith [mul_nonneg hc hc, mul_nonneg hc (neg_nonneg.2 htr.le)]
  · linarith

lemma root_real {tr det s : ℝ} (hs : s ^ 2 = tr ^ 2 - 4 * det) (e : ℝ) (he : e = 1 ∨ e = -1) :
    (((tr + e * s) / 2 : ℝ) : ℂ) ^ 2 - (tr : ℂ) * (((tr + e * s) / 2 : ℝ) : ℂ) + (det : ℂ) = 0 := by
  have : ((tr + e * s) / 2) ^ 2 - tr * ((tr + e * s) / 2) + det = 0 := by
    have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
    have : e ^ 2 * s ^ 2 = tr ^ 2 - 4 * det := by rw [he2, one_mul, hs]
    linear_combination (1 / 4) * this - (1 / 4) * (tr ^ 2 - 4 * det) * 0
  exact_mod_cast this

/-- The trace–determinant criterion: both eigenvalues have negative real part iff `tr < 0` and `det > 0`. -/
theorem linStable_iff (tr det : ℝ) : LinStable tr det ↔ tr < 0 ∧ 0 < det := by
  constructor
  · intro h
    by_cases hD : 0 ≤ tr ^ 2 - 4 * det
    · set s := Real.sqrt (tr ^ 2 - 4 * det) with hsdef
      have hs : s ^ 2 = tr ^ 2 - 4 * det := Real.sq_sqrt hD
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have h1 := h _ (root_real hs 1 (Or.inl rfl))
      have h2 := h _ (root_real hs (-1) (Or.inr rfl))
      simp only [Complex.ofReal_re] at h1 h2
      constructor
      · linarith
      · nlinarith
    · push_neg at hD
      set s := Real.sqrt (4 * det - tr ^ 2) with hsdef
      have hs : s ^ 2 = 4 * det - tr ^ 2 := Real.sq_sqrt (by linarith)
      have hz : (⟨tr / 2, s / 2⟩ : ℂ) ^ 2 - (tr : ℂ) * ⟨tr / 2, s / 2⟩ + (det : ℂ) = 0 := by
        apply Complex.ext
        · simp [pow_two]; nlinarith
        · simp [pow_two]; ring
      have h1 := h _ hz
      simp only at h1
      constructor
      · linarith
      · nlinarith [sq_nonneg tr]
  · rintro ⟨h1, h2⟩ z hz
    exact re_neg_of_root h1 h2 hz

/-! ### Classification, in terms of `μ = √(3/2) λ` -/

/-- Matter-dominated origin: determinant negative, so a saddle (never stable). -/
theorem origin_saddle {μ γ : ℝ} (h0 : 0 < γ) (h2 : γ < 2) : jdet μ γ 0 0 < 0 := by
  rw [jdet_origin]
  have : 0 < γ * (2 - γ) := mul_pos h0 (by linarith)
  linarith

theorem origin_not_stable {μ γ : ℝ} (h0 : 0 < γ) (h2 : γ < 2) :
    ¬ LinStable (jtr μ γ 0 0) (jdet μ γ 0 0) := by
  rw [linStable_iff]
  have := origin_saddle (μ := μ) h0 h2
  intro h
  linarith [h.2]

/-- The kinetic point `(1, 0)` is never linearly stable (`0 < γ < 2`). -/
theorem kin_pos_not_stable {μ γ : ℝ} (h0 : 0 < γ) (h2 : γ < 2) :
    ¬ LinStable (jtr μ γ 1 0) (jdet μ γ 1 0) := by
  rw [linStable_iff, jtr_kin_pos, jdet_kin_pos]
  rintro ⟨h1, h3⟩
  have h4 : 0 < 2 - γ := by linarith
  have : 0 < 3 - μ := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg h4.le (by linarith : 0 ≤ μ - 3)]
  linarith

/-- The kinetic point `(-1, 0)` is never linearly stable (`0 < γ < 2`). -/
theorem kin_neg_not_stable {μ γ : ℝ} (h0 : 0 < γ) (h2 : γ < 2) :
    ¬ LinStable (jtr μ γ (-1) 0) (jdet μ γ (-1) 0) := by
  rw [linStable_iff, jtr_kin_neg, jdet_kin_neg]
  rintro ⟨h1, h3⟩
  have h4 : 0 < 2 - γ := by linarith
  have : 0 < 3 + μ := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg h4.le (by linarith : 0 ≤ -(3 + μ))]
  linarith

/-! ### The two non-trivial points, in terms of `λ` -/

lemma sfPoint_y_sq {l : ℝ} (hl : l ^ 2 ≤ 6) :
    (sfPoint l).2 ^ 2 = 1 - (c32 * l) ^ 2 / 9 := by
  have : (c32 * l) ^ 2 = 3 / 2 * l ^ 2 := by rw [mul_pow, c32_sq]
  simp only [sfPoint]
  rw [Real.sq_sqrt (by linarith), this]

/-- Scalar-field-dominated point: trace and determinant in terms of `λ`. -/
lemma sf_tr_det {l γ : ℝ} (hl : l ^ 2 ≤ 6) :
    jtr (c32 * l) γ (sfPoint l).1 (sfPoint l).2 = 3 / 2 * l ^ 2 - 3 - 3 * γ ∧
      jdet (c32 * l) γ (sfPoint l).1 (sfPoint l).2 = (l ^ 2 - 6) * (l ^ 2 - 3 * γ) / 2 := by
  have hm : (c32 * l) ^ 2 = 3 / 2 * l ^ 2 := by rw [mul_pow, c32_sq]
  have hx : (sfPoint l).1 = c32 * l / 3 := rfl
  have hy := sfPoint_y_sq hl
  rw [hx]
  constructor
  · rw [jtr_sf hy, hm]
  · rw [jdet_sf hy, hm]; ring

/-- For `λ² < 6` and `0 < γ`, the scalar-field-dominated point is linearly stable iff `λ² < 3γ`. -/
theorem sfPoint_stable_iff {l γ : ℝ} (hγ : 0 < γ) (hl : l ^ 2 < 6) :
    LinStable (jtr (c32 * l) γ (sfPoint l).1 (sfPoint l).2)
      (jdet (c32 * l) γ (sfPoint l).1 (sfPoint l).2) ↔ l ^ 2 < 3 * γ := by
  obtain ⟨ht, hd⟩ := sf_tr_det (γ := γ) hl.le
  rw [linStable_iff, ht, hd]
  constructor
  · rintro ⟨_, h2⟩
    by_contra hc
    push_neg at hc
    nlinarith
  · intro h
    constructor
    · nlinarith
    · nlinarith

lemma scPoint_x_eq {l γ : ℝ} (hl : l ≠ 0) : (scPoint l γ).1 = 3 * γ / (2 * (c32 * l)) := by
  have := c32_pos
  have h2 := c32_sq
  simp only [scPoint]
  field_simp
  linear_combination (2 * γ) * h2

lemma scPoint_y_sq {l γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hl : l ≠ 0) :
    (scPoint l γ).2 ^ 2 = 9 * γ * (2 - γ) / (4 * (c32 * l) ^ 2) := by
  have h2 := c32_sq
  have hpos : 0 ≤ 3 * (2 - γ) * γ / (2 * l ^ 2) := by
    have : 0 < 2 - γ := by linarith
    positivity
  simp only [scPoint]
  rw [Real.sq_sqrt hpos, mul_pow, h2]
  field_simp
  ring

/-- Scaling point: trace and determinant in terms of `λ`. -/
lemma sc_tr_det {l γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hl : l ≠ 0) :
    jtr (c32 * l) γ (scPoint l γ).1 (scPoint l γ).2 = -(3 * (2 - γ) / 2) ∧
      jdet (c32 * l) γ (scPoint l γ).1 (scPoint l γ).2 =
        9 * γ * (2 - γ) * (l ^ 2 - 3 * γ) / (2 * l ^ 2) := by
  have hμ : c32 * l ≠ 0 := mul_ne_zero c32_pos.ne' hl
  have hm : (c32 * l) ^ 2 = 3 / 2 * l ^ 2 := by rw [mul_pow, c32_sq]
  have hx := scPoint_x_eq (γ := γ) hl
  have hy := scPoint_y_sq hγ hγ2 hl
  rw [hx]
  constructor
  · exact jtr_sc hμ hy
  · rw [jdet_sc hμ hy, hm]
    field_simp
    ring

/-- For `0 < γ < 2` and `λ ≠ 0`, the scaling point is linearly stable iff `λ² > 3γ`.  Together with
`scPoint_mem_disc_iff` (it lies in the half disc iff `λ² ≥ 3γ`) and `scPoint_eq_sfPoint_iff`
(it equals `sfPoint` iff `λ² = 3γ`), the stability passes from `sfPoint` to `scPoint` at `λ² = 3γ`. -/
theorem scPoint_stable_iff {l γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hl : l ≠ 0) :
    LinStable (jtr (c32 * l) γ (scPoint l γ).1 (scPoint l γ).2)
      (jdet (c32 * l) γ (scPoint l γ).1 (scPoint l γ).2) ↔ 3 * γ < l ^ 2 := by
  obtain ⟨ht, hd⟩ := sc_tr_det hγ hγ2 hl
  rw [linStable_iff, ht, hd]
  have hl2 : 0 < l ^ 2 := by positivity
  have h2 : 0 < 2 - γ := by linarith
  have hpos : 0 < 9 * γ * (2 - γ) / (2 * l ^ 2) := by positivity
  have key : 9 * γ * (2 - γ) * (l ^ 2 - 3 * γ) / (2 * l ^ 2) =
      (9 * γ * (2 - γ) / (2 * l ^ 2)) * (l ^ 2 - 3 * γ) := by ring
  rw [key]
  constructor
  · rintro ⟨_, h⟩
    have := (pos_iff_pos_of_mul_pos h).1 hpos
    linarith
  · intro h
    exact ⟨by linarith, mul_pos hpos (by linarith)⟩

end

end Lightlike.Cosmology.QuintessenceFixedPoints

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.LinStable := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.LinStable
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.kin_neg_not_stable := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.kin_neg_not_stable
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.kin_pos_not_stable := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.kin_pos_not_stable
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.linStable_iff := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.linStable_iff
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.origin_not_stable := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.origin_not_stable
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.origin_saddle := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.origin_saddle
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.re_neg_of_root := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.re_neg_of_root
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.root_real := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.root_real
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.scPoint_stable_iff := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.scPoint_stable_iff
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.scPoint_x_eq := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.scPoint_x_eq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.scPoint_y_sq := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.scPoint_y_sq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.sc_tr_det := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.sc_tr_det
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.sfPoint_stable_iff := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.sfPoint_stable_iff
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.sfPoint_y_sq := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.sfPoint_y_sq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_029.sf_tr_det := _root_.Lightlike.Cosmology.QuintessenceFixedPoints.sf_tr_det
