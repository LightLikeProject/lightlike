import Mathlib
import Lightlike.Cosmology.QuintessenceFixedPoints.Fixed

/-!
# Quintessence with an exponential potential and no matter fluid

Row G1-029 (milestone CO17), continuation of `Fixed.lean`.  Without a matter fluid the Friedmann
constraint is `x² + y² = 1`: the half disc collapses to its boundary, the unit half circle, which is
invariant, and the planar system reduces to the one-dimensional system on `x ∈ [-1, 1]`
(Copeland–Sami–Tsujikawa 2006, copeland-2006)
`x' = (1 - x²)(μ - 3x)`, `μ = √(3/2) λ`.

## Main statements

* `vfx_circle`: on the circle `y² = 1 - x²` the field `vfx` equals `vacF μ x` (for every `γ`).
* `vacF_zero_iff`: the zeros in `[-1, 1]` are `x = ±1` (kinetic points) and `x = μ/3` (the
  scalar-field-dominated point, which lies in `[-1, 1]` iff `λ² ≤ 6`).
* `vacF'_sf`, `vacF'_kin_pos`, `vacF'_kin_neg`: the eigenvalues (derivatives of `vacF`) at the fixed
  points: `(λ² - 6)/2`, `6 - 2μ`, `6 + 2μ`.
* `vac_sf_stable_iff`, `vac_kin_pos_stable_iff`, `vac_kin_neg_stable_iff`: the scalar-field point is
  stable iff `λ² < 6`; the kinetic point `x = 1` is stable iff `λ > √6`, `x = -1` iff `λ < -√6`.
* `vacF_pos_of_lt`, `vacF_neg_of_gt`: for `λ² < 6` the flow on `(-1, 1)` points toward `μ/3`, so the
  scalar-field point is a global attractor of the open interval (nonlinear statement).
-/

namespace Lightlike.Rows.G1_029

noncomputable section

/-- The reduced one-dimensional field on the circle `x² + y² = 1`. -/
def vacF (μ x : ℝ) : ℝ := (1 - x ^ 2) * (μ - 3 * x)

/-- Its derivative in `x`. -/
def vacF' (μ x : ℝ) : ℝ := 9 * x ^ 2 - 2 * μ * x - 3

/-- On the invariant circle `y² = 1 - x²` the planar field reduces to `vacF` (any matter index). -/
theorem vfx_circle (μ γ x y : ℝ) (h : y ^ 2 = 1 - x ^ 2) : vfx μ γ x y = vacF μ x := by
  simp only [vfx, aux, vacF, h]
  ring

lemma hasDerivAt_vacF (μ x : ℝ) : HasDerivAt (vacF μ) (vacF' μ x) x := by
  have h1 : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub 1)
  have h2 : HasDerivAt (fun x : ℝ => μ - 3 * x) (-3) x := by
    simpa using ((hasDerivAt_id x).const_mul 3).const_sub μ
  have := h1.mul h2
  exact this.congr_deriv (by unfold vacF'; ring)

/-- The zeros of the reduced field in `[-1,1]`: the two kinetic points and `x = μ/3`. -/
theorem vacF_zero_iff (μ x : ℝ) : vacF μ x = 0 ↔ x = 1 ∨ x = -1 ∨ x = μ / 3 := by
  simp only [vacF, mul_eq_zero]
  constructor
  · rintro (h | h)
    · have : (x - 1) * (x + 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (by linarith))
  · rintro (h | h | h)
    · left; rw [h]; norm_num
    · left; rw [h]; norm_num
    · right; rw [h]; ring

/-- Eigenvalue at the scalar-field-dominated point `x = μ/3`: `(λ² - 6)/2`. -/
theorem vacF'_sf (l : ℝ) : vacF' (c32 * l) (c32 * l / 3) = (l ^ 2 - 6) / 2 := by
  have : (c32 * l) ^ 2 = 3 / 2 * l ^ 2 := by rw [mul_pow, c32_sq]
  simp only [vacF']
  nlinarith [this]

/-- Eigenvalue at the kinetic point `x = 1`: `6 - 2μ`. -/
theorem vacF'_kin_pos (μ : ℝ) : vacF' μ 1 = 6 - 2 * μ := by simp only [vacF']; ring

/-- Eigenvalue at the kinetic point `x = -1`: `6 + 2μ`. -/
theorem vacF'_kin_neg (μ : ℝ) : vacF' μ (-1) = 6 + 2 * μ := by simp only [vacF']; ring

/-- Without matter, the scalar-field point is linearly stable iff `λ² < 6`. -/
theorem vac_sf_stable_iff (l : ℝ) : vacF' (c32 * l) (c32 * l / 3) < 0 ↔ l ^ 2 < 6 := by
  rw [vacF'_sf]
  constructor <;> intro h <;> linarith

/-- Without matter, the kinetic point `x = 1` is linearly stable iff `λ > √6`, i.e. `λ > 0`, `λ² > 6`. -/
theorem vac_kin_pos_stable_iff (l : ℝ) : vacF' (c32 * l) 1 < 0 ↔ 0 < l ∧ 6 < l ^ 2 := by
  have hc := c32_pos
  have hm : (c32 * l) ^ 2 = 3 / 2 * l ^ 2 := by rw [mul_pow, c32_sq]
  rw [vacF'_kin_pos]
  constructor
  · intro h
    have h3 : 3 < c32 * l := by linarith
    have hl : 0 < l := by
      by_contra hl
      push Not at hl
      nlinarith
    exact ⟨hl, by nlinarith⟩
  · rintro ⟨hl, h6⟩
    by_contra hcon
    push Not at hcon
    have : c32 * l ≤ 3 := by linarith
    have : 0 < c32 * l := mul_pos hc hl
    nlinarith

/-- Without matter, the kinetic point `x = -1` is linearly stable iff `λ < -√6`. -/
theorem vac_kin_neg_stable_iff (l : ℝ) : vacF' (c32 * l) (-1) < 0 ↔ l < 0 ∧ 6 < l ^ 2 := by
  have h := vac_kin_pos_stable_iff (-l)
  have e : vacF' (c32 * -l) 1 = vacF' (c32 * l) (-1) := by
    simp only [vacF']; ring
  rw [e] at h
  rw [h]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by nlinarith⟩

/-- For `|μ| < 3` (`λ² < 6`) the field is positive on `(-1, μ/3)`. -/
theorem vacF_pos_of_lt {μ x : ℝ} (hx : -1 < x) (hxμ : x < μ / 3) (hμ : μ < 3) :
    0 < vacF μ x := by
  have h1 : x < 1 := by linarith
  have : 0 < 1 - x ^ 2 := by nlinarith
  exact mul_pos this (by linarith)

/-- For `|μ| < 3` the field is negative on `(μ/3, 1)`. -/
theorem vacF_neg_of_gt {μ x : ℝ} (hx : x < 1) (hxμ : μ / 3 < x) (hμ : -3 < μ) :
    vacF μ x < 0 := by
  have h1 : -1 < x := by linarith
  have : 0 < 1 - x ^ 2 := by nlinarith
  exact mul_neg_of_pos_of_neg this (by linarith)

end

end Lightlike.Rows.G1_029
