import Lightlike.Rows.G1_063.Divergence

/-!
# The 2D trace anomaly with conservation, in conformal gauge (row G1-063, milestone SC7)

On `(ℝ², e^{2ψ} η)` the requirement `T^μ_μ = c R / (24 π)` together with `∇^μ T_{μν} = 0`
is, pointwise, equivalent to a flat-space system of equations for the components of `T`
(`anomaly_conservation_iff`), with `κ = c / (12 π)` and `L = ∂_t² ψ - ∂_x² ψ`:

* `-T_tt + T_xx = κ L`,
* `-∂_t T_{tν} + ∂_x T_{xν} = κ (∂_ν ψ) L`   (`ν = t, x`).

This is the classical core of the 2D trace anomaly (Birrell–Davies 1982): the trace fixes the
conformal-factor dependence and the conservation law is the Wess–Zumino consistency of it.
-/

noncomputable section

namespace Lightlike.Rows.G1_063

open Lightlike
open scoped ContDiff

/-- The right-hand side of the anomaly in conformal gauge: `c R / (24 π) = e^{-2ψ} (c / (12 π)) L`,
with `L = ∂_t² ψ - ∂_x² ψ`. -/
lemma anomaly_rhs {ψ : (Fin 2 → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (c : ℝ) (x : Fin 2 → ℝ) :
    c * scalarCurvature (confEta2 ψ) x / (24 * Real.pi) =
      Real.exp (-(2 * ψ x)) * (c / (12 * Real.pi) *
        (pd 0 (fun y => pd 0 ψ y) x - pd 1 (fun y => pd 1 ψ y) x)) := by
  rw [scalarCurvature_conformalEta2 hψ]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **The 2D trace anomaly with conservation, in conformal gauge.** For a symmetric `(0,2)`-tensor
field `T` on `(ℝ², e^{2ψ} η)`, at a point `x`, the trace anomaly `T^μ_μ = c R / (24 π)` and the
conservation `(div T)_ν = 0` (`ν = t, x`) hold iff the flat-space equations
`-T_tt + T_xx = κ L` and `-∂_t T_{tν} + ∂_x T_{xν} = κ (∂_ν ψ) L` hold, where `κ = c / (12 π)` and
`L = ∂_t² ψ - ∂_x² ψ`. -/
theorem anomaly_conservation_iff {ψ : (Fin 2 → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (c : ℝ)
    (T : Fin 2 → Fin 2 → (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) (hT : T 0 1 x = T 1 0 x) :
    (trT (confEta2 ψ) T x = c * scalarCurvature (confEta2 ψ) x / (24 * Real.pi) ∧
        ∀ ν, divT (confEta2 ψ) T ν x = 0) ↔
      (-T 0 0 x + T 1 1 x = c / (12 * Real.pi) *
          (pd 0 (fun y => pd 0 ψ y) x - pd 1 (fun y => pd 1 ψ y) x) ∧
        ∀ ν, -pd 0 (T 0 ν) x + pd 1 (T 1 ν) x = pd ν ψ x * (c / (12 * Real.pi) *
          (pd 0 (fun y => pd 0 ψ y) x - pd 1 (fun y => pd 1 ψ y) x))) := by
  have he : Real.exp (-(2 * ψ x)) ≠ 0 := (Real.exp_pos _).ne'
  rw [trT_confEta2, anomaly_rhs hψ]
  simp only [divT_confEta2 hψ T x hT, mul_eq_mul_left_iff, mul_eq_zero, he, or_false, false_or]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun ν => ?_⟩
    have := h2 ν
    rw [h1] at this
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun ν => ?_⟩
    have := h2 ν
    rw [h1]
    linarith

end Lightlike.Rows.G1_063
