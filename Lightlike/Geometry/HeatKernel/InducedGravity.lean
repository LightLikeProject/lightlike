import Mathlib
import Lightlike.Geometry.HeatKernel.Potential

/-!
# Induced gravity: the Einstein–Hilbert term from `a₁` (algebraic part)

Tier 2 of row G1-018, first steps towards milestone OA3 (Sakharov 1967). A scalar field with
operator `D = -Δ + ξR` is the Laplace-type operator `-(Δ + E)` with `E = -ξR` (constant `R`). Its
Seeley–DeWitt coefficient is `a₁ = (4π)^{-n/2} V R (1 - 6ξ)/6` (`heatCoeffsE_xi_one`), the "6E" of
`vassilevich-2003`, eq. (4.27).

## Main results

* `heatCoeffsE_xi_one`: `a₁` of `-Δ + ξR` is `(4π)^{-n/2} V R (1 - 6ξ)/6`.
* `conformalCoupling`, `conformalCoupling_eq_sixth_iff`: `ξ_n = (n-2)/(4(n-1))` equals `1/6` iff `n = 4`.
* `heatCoeffsE_conformal_four_one`: in dimension `4` the conformally coupled scalar has `a₁ = 0`.
* `heatCoeffsE_minimal_one_ne_zero`: the minimally coupled scalar has `a₁ ≠ 0` when `R ≠ 0`.
* `inducedInvG`, `inducedInvG_spec`: the induced `1/G = Λ²(1 - 6ξ)/(12π)` (Λ² = 1/ε).
-/

open Real

noncomputable section

namespace Lightlike.HeatKernel

/-- The conformal coupling `ξ_n = (n-2)/(4(n-1))` of the scalar field in dimension `n`. -/
def conformalCoupling (n : ℕ) : ℝ := ((n : ℝ) - 2) / (4 * ((n : ℝ) - 1))

theorem conformalCoupling_four : conformalCoupling 4 = 1 / 6 := by
  norm_num [conformalCoupling]

theorem conformalCoupling_three : conformalCoupling 3 = 1 / 8 := by
  norm_num [conformalCoupling]

theorem conformalCoupling_two : conformalCoupling 2 = 0 := by
  norm_num [conformalCoupling]

/-- The conformal coupling equals `1/6` exactly in dimension `4`. -/
theorem conformalCoupling_eq_sixth_iff (n : ℕ) : conformalCoupling n = 1 / 6 ↔ n = 4 := by
  constructor
  · intro h
    unfold conformalCoupling at h
    by_cases h1 : (n : ℝ) - 1 = 0
    · rw [h1] at h
      norm_num at h
    · rw [div_eq_iff (by intro h0; apply h1; linarith)] at h
      have : (n : ℝ) = 4 := by linarith
      exact_mod_cast this
  · rintro rfl
    exact conformalCoupling_four

/-- **`a₁` of `-Δ + ξR`.** With potential `E = -ξR`, `a₁ = (4π)^{-n/2} V R (1 - 6ξ)/6`. -/
theorem heatCoeffsE_xi_one (n : ℕ) (V R ric riem ξ : ℝ) :
    heatCoeffsE n V R ric riem (-(ξ * R)) 1 =
      (4 * π) ^ (-((n : ℝ) / 2)) * V * R * (1 - 6 * ξ) / 6 := by
  simp only [heatCoeffsE]
  ring

/-- The minimally coupled scalar (`ξ = 0`) has `a₁ = (4π)^{-n/2} V R/6`. -/
theorem heatCoeffsE_minimal_one (n : ℕ) (V R ric riem : ℝ) :
    heatCoeffsE n V R ric riem (-(0 * R)) 1 = (4 * π) ^ (-((n : ℝ) / 2)) * V * R / 6 := by
  rw [heatCoeffsE_xi_one]
  ring

/-- The minimally coupled scalar has non-zero `a₁` on a space of positive volume and `R ≠ 0`. -/
theorem heatCoeffsE_minimal_one_ne_zero (n : ℕ) {V R : ℝ} (ric riem : ℝ) (hV : 0 < V) (hR : R ≠ 0) :
    heatCoeffsE n V R ric riem (-(0 * R)) 1 ≠ 0 := by
  rw [heatCoeffsE_minimal_one]
  have h4 : 0 < (4 * π) ^ (-((n : ℝ) / 2)) := Real.rpow_pos_of_pos (by positivity) _
  have : (4 * π) ^ (-((n : ℝ) / 2)) * V * R ≠ 0 := by positivity
  intro h
  apply this
  linarith

/-- **Conformal coupling kills `a₁` in dimension 4.** For `ξ = 1/6`, `a₁ = 0`. -/
theorem heatCoeffsE_conformal_four_one (V R ric riem : ℝ) :
    heatCoeffsE 4 V R ric riem (-(conformalCoupling 4 * R)) 1 = 0 := by
  rw [heatCoeffsE_xi_one, conformalCoupling_four]
  ring

/-- In every dimension `n ≠ 4`, the conformally coupled scalar has `a₁ ≠ 0` when `V > 0`, `R ≠ 0`. -/
theorem heatCoeffsE_conformal_one_ne_zero {n : ℕ} (hn : n ≠ 4) {V R : ℝ} (ric riem : ℝ)
    (hV : 0 < V) (hR : R ≠ 0) :
    heatCoeffsE n V R ric riem (-(conformalCoupling n * R)) 1 ≠ 0 := by
  rw [heatCoeffsE_xi_one]
  have h4 : 0 < (4 * π) ^ (-((n : ℝ) / 2)) := Real.rpow_pos_of_pos (by positivity) _
  have hξ : 1 - 6 * conformalCoupling n ≠ 0 := by
    intro h
    apply hn
    rw [← conformalCoupling_eq_sixth_iff]
    linarith
  have : (4 * π) ^ (-((n : ℝ) / 2)) * V * R * (1 - 6 * conformalCoupling n) ≠ 0 := by
    have := h4.ne'
    have := hV.ne'
    positivity
  intro h
  apply this
  linarith

/-- The induced inverse Newton constant of a scalar with coupling `ξ` in dimension `4` with
proper-time cutoff `ε = 1/Λ²`: `1/G = Λ² (1 - 6ξ)/(12π)`, i.e. `(1 - 6ξ)/(12π ε)`. -/
def inducedInvG (ξ ε : ℝ) : ℝ := (1 - 6 * ξ) / (12 * π * ε)

/-- **Sakharov's induced Newton constant** (algebraic form). The `ε⁻¹`-coefficient of the
one-loop effective action `Γ = -(1/2) ∫_ε dt/t Tr e^{-tD}` is `-(1/2) a₁`; it equals the
Einstein–Hilbert term `-(1/(16πG)) ∫R` with `1/G = (1 - 6ξ)/(12π ε)`:
`(1/2) a₁ = (1/G) (V R)/(16π ε⁻¹...)`; precisely `(1/2) a₁ · (1/ε) = inducedInvG ξ ε/(16π) · V R`
after multiplying `a₁` by the cutoff factor `1/ε`. -/
theorem inducedInvG_spec (V R ric riem ξ : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    (1 / 2) * heatCoeffsE 4 V R ric riem (-(ξ * R)) 1 / ε =
      inducedInvG ξ ε / (16 * π) * (V * R) := by
  rw [heatCoeffsE_xi_one]
  have h : ((4 : ℕ) : ℝ) / 2 = 2 := by norm_num
  rw [h]
  have h2 : (4 * π) ^ (-(2 : ℝ)) = 1 / (16 * π ^ 2) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    field_simp
    ring
  rw [h2, inducedInvG]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end Lightlike.HeatKernel
