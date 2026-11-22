import Mathlib

/-!
# Quintessence with an exponential potential: the autonomous system and its fixed points

Row G1-029 (milestone CO17).  For a canonical scalar field with `V = V₀ e^{-λφ}` and a perfect fluid of
equation of state `p = (γ - 1) ρ`, Copeland–Sami–Tsujikawa (copeland-2006, eq. (175) ff.) use the variables
`x = φ̇/(√6 H)`, `y = √V/(√3 H)`; the Friedmann and field equations become the planar system
`x' = -3x + (√6/2) λ y² + (3/2) x [2x² + γ(1 - x² - y²)]`,
`y' = -(√6/2) λ x y + (3/2) y [2x² + γ(1 - x² - y²)]`
on the closed half disc `x² + y² ≤ 1`, `y ≥ 0` (here `'` is `d/dN`, `N = ln a`).  We write `μ = √(3/2) λ`
(`= (√6/2) λ`), and `γ = 0` is the case without matter.

This file defines the vector field and the candidate fixed points (the matter point, the two kinetic points,
the scalar-field-dominated point `sfPoint` and the scaling point `scPoint`) and proves that each is a zero
of the vector field.  The reduction from the Einstein–Klein–Gordon equations to this system is not proved
here, and the stability statements are in `Stab.lean` and `Stab2.lean`.

## Main definitions

* `c32`, `aux`, `vfx`, `vfy`: the constant `√(3/2)` and the two components of the vector field.
* `sfPoint`, `scPoint`: the scalar-field-dominated point and the scaling point.

## References

* copeland-2006
-/

namespace Lightlike.Rows.G1_029

noncomputable section

/-- The constant `√(3/2)`, so that `μ = c32 * λ` is the coefficient `(√6/2) λ` of the system. -/
def c32 : ℝ := Real.sqrt (3 / 2)

lemma c32_pos : 0 < c32 := Real.sqrt_pos.2 (by norm_num)

lemma c32_sq : c32 ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)

/-- The bracket `2x² + γ(1 - x² - y²)` of the system (it equals `-2Ḣ/(3H²)`); `γ = 1 + w_m`. -/
def aux (γ x y : ℝ) : ℝ := 2 * x ^ 2 + γ * (1 - x ^ 2 - y ^ 2)

/-- First component of the vector field, `dx/dN`, with `μ = (√6/2) λ`. -/
def vfx (μ γ x y : ℝ) : ℝ := -3 * x + μ * y ^ 2 + 3 / 2 * x * aux γ x y

/-- Second component of the vector field, `dy/dN`, with `μ = (√6/2) λ`. -/
def vfy (μ γ x y : ℝ) : ℝ := -μ * x * y + 3 / 2 * y * aux γ x y

lemma vfy_eq (μ γ x y : ℝ) :
    vfy μ γ x y = y * (-μ * x + 3 / 2 * (2 * x ^ 2 + γ * (1 - x ^ 2 - y ^ 2))) := by
  unfold vfy aux; ring

/-- The scalar-field-dominated point `(λ/√6, √(1 - λ²/6))`, written with `μ = c32 * λ`. -/
def sfPoint (l : ℝ) : ℝ × ℝ := (c32 * l / 3, Real.sqrt (1 - (c32 * l) ^ 2 / 9))

/-- The scaling point `(√(3/2) γ/λ, √(3γ(2-γ)/(2λ²)))`. -/
def scPoint (l γ : ℝ) : ℝ × ℝ :=
  (c32 * γ / l, Real.sqrt (3 * (2 - γ) * γ / (2 * l ^ 2)))

/-! ### The points are fixed points -/

/-- The matter-dominated point `(0, 0)` is a fixed point. -/
theorem vf_origin (μ γ : ℝ) : vfx μ γ 0 0 = 0 ∧ vfy μ γ 0 0 = 0 := by
  simp [vfx, vfy, aux]

/-- The kinetic point `(1, 0)` is a fixed point. -/
theorem vf_kin_pos (μ γ : ℝ) : vfx μ γ 1 0 = 0 ∧ vfy μ γ 1 0 = 0 := by
  simp [vfx, vfy, aux]

/-- The kinetic point `(-1, 0)` is a fixed point. -/
theorem vf_kin_neg (μ γ : ℝ) : vfx μ γ (-1) 0 = 0 ∧ vfy μ γ (-1) 0 = 0 := by
  simp [vfx, vfy, aux]

/-- A point `(μ/3, y)` with `y² = 1 - μ²/9` is a fixed point (the scalar-field-dominated point). -/
theorem vf_sf {μ γ y : ℝ} (hy : y ^ 2 = 1 - μ ^ 2 / 9) :
    vfx μ γ (μ / 3) y = 0 ∧ vfy μ γ (μ / 3) y = 0 := by
  constructor
  · unfold vfx aux
    rw [hy]; ring
  · rw [vfy_eq, hy]
    have : -μ * (μ / 3) + 3 / 2 * (2 * (μ / 3) ^ 2 + γ * (1 - (μ / 3) ^ 2 - (1 - μ ^ 2 / 9))) = 0 := by
      ring
    rw [this, mul_zero]

/-- The scaling point is a fixed point. -/
theorem vf_sc {μ γ y : ℝ} (hμ : μ ≠ 0) (hy : y ^ 2 = 9 * γ * (2 - γ) / (4 * μ ^ 2)) :
    vfx μ γ (3 * γ / (2 * μ)) y = 0 ∧ vfy μ γ (3 * γ / (2 * μ)) y = 0 := by
  constructor
  · unfold vfx aux
    rw [hy]; field_simp; ring
  · rw [vfy_eq, hy]
    have : -μ * (3 * γ / (2 * μ)) + 3 / 2 * (2 * (3 * γ / (2 * μ)) ^ 2 +
        γ * (1 - (3 * γ / (2 * μ)) ^ 2 - 9 * γ * (2 - γ) / (4 * μ ^ 2))) = 0 := by
      field_simp; ring
    rw [this, mul_zero]

end

end Lightlike.Rows.G1_029
