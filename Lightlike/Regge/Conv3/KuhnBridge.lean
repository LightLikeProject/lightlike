import Mathlib
import Lightlike.Regge.Conv3.DihedralDeriv

/-!
# Scaling lemmas between the dihedral-angle derivative and the Gram polynomials

The derivative of a dihedral angle in `DihedralDeriv` is written with `Nn`, `Pp`, which carry the
denominator `4a`. Multiplied by the squared length `a` of the hinge they become the polynomial
quantities `N = a * Nn` and `P = a * Pp` of the Gram matrix (`P = |u|²|e|² - (e·u)²`,
`N = (u·w)|e|² - (e·u)(e·w)`), which are the quantities of `KuhnBasis`. The first-order
variations carry a correction in the variation `a₁` of the hinge length that cancels in the
combination that occurs in the derivative of the angle.

## Main results

* `mul_Pp_eq`, `mul_Nn_eq`: `a * Pp` and `a * Nn` as polynomials in the squared lengths.
* `mul_diff_eq`: the derivative combination `Nn' - Nn / 2 * (Pp₁' / Pp₁ + Pp₂' / Pp₂)`, times `a`,
  equals the same combination built from the polynomial quantities.
-/

namespace Lightlike.Regge.Conv3

/-- The polynomial face quantity `P = a * Pp`, in squared lengths. -/
noncomputable def PPoly (a b c : ℝ) : ℝ := a * b - (b + a - c) ^ 2 / 4

/-- The polynomial cross quantity `N = a * Nn`, in squared lengths. -/
noncomputable def NPoly (a b c d e f : ℝ) : ℝ :=
  a * (b + d - f) / 2 - (b + a - c) * (d + a - e) / 4

/-- The variation of `PPoly` along `(a + ε a₁, b + ε b₁, c + ε c₁)` at `ε = 0`. -/
noncomputable def PPoly' (a b c a₁ b₁ c₁ : ℝ) : ℝ :=
  a₁ * b + a * b₁ - (b + a - c) * (b₁ + a₁ - c₁) / 2

/-- The variation of `NPoly` along the line of squared lengths at `ε = 0`. -/
noncomputable def NPoly' (a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ : ℝ) : ℝ :=
  a₁ * (b + d - f) / 2 + a * (b₁ + d₁ - f₁) / 2 -
    ((b₁ + a₁ - c₁) * (d + a - e) + (b + a - c) * (d₁ + a₁ - e₁)) / 4

/-- `a * Pp` is the polynomial `PPoly`. -/
theorem mul_Pp_eq {a b c : ℝ} (ha : a ≠ 0) : a * Pp a b c = PPoly a b c := by
  unfold Pp PPoly
  field_simp

/-- `a * Nn` is the polynomial `NPoly`. -/
theorem mul_Nn_eq {a b c d e f : ℝ} (ha : a ≠ 0) : a * Nn a b c d e f = NPoly a b c d e f := by
  unfold Nn NPoly
  field_simp

/-- `a * Pp'` is `PPoly'` minus the correction `a₁ * Pp`. -/
theorem mul_Pp'_eq {a b c a₁ b₁ c₁ : ℝ} (ha : a ≠ 0) :
    a * Pp' a b c a₁ b₁ c₁ = PPoly' a b c a₁ b₁ c₁ - a₁ * Pp a b c := by
  unfold Pp' Pp PPoly'
  field_simp
  ring

/-- `a * Nn'` is `NPoly'` minus the correction `a₁ * Nn`. -/
theorem mul_Nn'_eq {a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ : ℝ} (ha : a ≠ 0) :
    a * Nn' a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ =
      NPoly' a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ - a₁ * Nn a b c d e f := by
  unfold Nn' Nn NPoly'
  field_simp
  ring

/-- The derivative combination of the dihedral angle, times the hinge length `a`, equals the same
combination of the polynomial quantities: the corrections in `a₁` cancel. -/
theorem mul_diff_eq {a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ : ℝ} (ha : a ≠ 0)
    (h1 : PPoly a b c ≠ 0) (h2 : PPoly a d e ≠ 0) :
    a * (Nn' a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ -
        Nn a b c d e f / 2 * (Pp' a b c a₁ b₁ c₁ / Pp a b c + Pp' a d e a₁ d₁ e₁ / Pp a d e)) =
      NPoly' a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ -
        NPoly a b c d e f / 2 *
          (PPoly' a b c a₁ b₁ c₁ / PPoly a b c + PPoly' a d e a₁ d₁ e₁ / PPoly a d e) := by
  have hp1 : Pp a b c ≠ 0 := fun h => h1 (by rw [← mul_Pp_eq ha, h, mul_zero])
  have hp2 : Pp a d e ≠ 0 := fun h => h2 (by rw [← mul_Pp_eq ha, h, mul_zero])
  have e1 := mul_Pp'_eq (a := a) (b := b) (c := c) (a₁ := a₁) (b₁ := b₁) (c₁ := c₁) ha
  have e2 := mul_Pp'_eq (a := a) (b := d) (c := e) (a₁ := a₁) (b₁ := d₁) (c₁ := e₁) ha
  have e3 := mul_Nn'_eq (a := a) (b := b) (c := c) (d := d) (e := e) (f := f) (a₁ := a₁)
    (b₁ := b₁) (c₁ := c₁) (d₁ := d₁) (e₁ := e₁) (f₁ := f₁) ha
  have q1 := mul_Pp_eq (b := b) (c := c) ha
  have q2 := mul_Pp_eq (b := d) (c := e) ha
  have q3 := mul_Nn_eq (b := b) (c := c) (d := d) (e := e) (f := f) ha
  have d1 : Pp' a b c a₁ b₁ c₁ = (PPoly' a b c a₁ b₁ c₁ - a₁ * Pp a b c) / a := by
    field_simp; linarith
  have d2 : Pp' a d e a₁ d₁ e₁ = (PPoly' a d e a₁ d₁ e₁ - a₁ * Pp a d e) / a := by
    field_simp; linarith
  have d3 : Nn' a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ =
      (NPoly' a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ - a₁ * Nn a b c d e f) / a := by
    field_simp; linarith
  have pe1 : PPoly a b c = a * Pp a b c := q1.symm
  have pe2 : PPoly a d e = a * Pp a d e := q2.symm
  have ne : NPoly a b c d e f = a * Nn a b c d e f := q3.symm
  rw [d1, d2, d3, pe1, pe2, ne]
  field_simp
  ring

end Lightlike.Regge.Conv3
