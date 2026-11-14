import Lightlike.Asymptotics.GammaBounds

/-!
# Trust checks for the uniform bounds on `1/Γ` and `Γ`

* **Known value.** The Stirling exponent `f(w) = w log w − w` has `Re f(i) = Re f(−i) = −π/2`
  (`re_stirF_I`), in agreement with `re_stirF_neg`: `Re f(−i) = −Re f(i) − π`. The reflection
  formula in midpoint form gives `Γ(½)² = π` at `w = 0` (`Gamma_half_mul_self`), the square of
  Mathlib's independent value `Γ(½) = √π` (`Complex.Gamma_one_half_eq`, from the Gaussian
  integral). The bounds are checked numerically on polar grids up to `|w| = 40`, the `1/Γ` bound
  in all four quadrants and next to the poles on the negative axis: the largest ratio of
  `‖1/Γ(w + ½)‖` to its bound is `0.78` (the limit `√(2π)/π = 0.80` on the negative axis), and of
  `‖Γ(w + ½)‖` to its bound `0.98`, which is `exp(−3/160)` at `|w| = 40`, so the constant
  `√(2π)` cannot be lowered (`scripts/asymptotics/gamma_bounds_check.py`).
* **Wrong input fails.** Without the term `π |Im w|`, the reflection of the exponent is false:
  `Re f(−i) ≠ −Re f(i)` (`re_stirF_neg_wrong`). This term is what cancels the growth
  `exp(π |Im w|)` of `cos(π w)` on the left half-plane. The script shows that the `Γ` bound fails
  on the left half-plane, near the poles at `w = −½ − n`, so its hypothesis `Re w ≥ 0` is needed.
* **Non-vacuity.** At `w = 2i`, with `‖w‖² = 4 ≥ 2` and `Re f(2i) = −π`, the two bounds give
  `‖1/Γ(½ + 2i)‖ ≤ exp(3/8 + π)` and `‖Γ(½ + 2i)‖ ≤ √(2π) exp(3/8 − π)`
  (`norm_Gamma_bounds_two_I`).
* **Junk values.** Lean's `log 0 = 0` gives `f(0) = 0` (`stirF_zero`), which is also the limit
  of `w log w − w` at `0`, so `abs_re_stirF_le` holds at `0` for the right reason. Mathlib's
  `Γ(−n) = 0` gives `1/Γ(−n) = 0` (`inv_Gamma_neg_nat`), the true value of the entire function
  `1/Γ`; the bound on `1/Γ` is trivially true there. The bound on `Γ` is stated only for
  `Re w ≥ 0`, where `Γ(w + ½)` has no poles, so the junk value `Γ(−n) = 0` never enters it.
-/

open Complex
open scoped Real

namespace Lightlike.Asymptotics

/-- **Known value**: `Re f(i) = −π/2` and `Re f(−i) = −π/2`. -/
theorem re_stirF_I : (stirF I).re = -(π / 2) ∧ (stirF (-I)).re = -(π / 2) := by
  constructor
  · rw [re_stirF, arg_I]
    simp
  · rw [re_stirF, arg_neg_I]
    simp

/-- **Known value**: the reflection formula at `w = 0` gives `Γ(½) Γ(½) = π`, the square of
Mathlib's value `Γ(½) = √π`. -/
theorem Gamma_half_mul_self : Gamma (1 / 2) * Gamma (1 / 2) = π := by
  have h := Gamma_half_add_mul_Gamma_half_sub 0
  simpa using h

/-- **Wrong input fails**: without the term `π |Im w|`, the reflection of the Stirling exponent
would be `Re f(−w) = −Re f(w)`, which is false at `w = i`. -/
theorem re_stirF_neg_wrong : (stirF (-I)).re ≠ -(stirF I).re := by
  rw [re_stirF_I.1, re_stirF_I.2]
  intro h
  linarith [Real.pi_pos]

/-- The norm of `2i` is `2`. -/
lemma norm_two_I : ‖2 * I‖ = 2 := by
  rw [norm_mul, Complex.norm_two, norm_I, mul_one]

/-- `Re f(2i) = −π`. -/
lemma re_stirF_two_I : (stirF (2 * I)).re = -π := by
  have harg : arg (2 * I) = π / 2 := by
    rw [show (2 : ℂ) * I = ((2 : ℝ) : ℂ) * I by norm_num, arg_real_mul I (by norm_num), arg_I]
  rw [re_stirF, harg, norm_two_I]
  simp
  ring

/-- **Non-vacuity** of `norm_inv_Gamma_half_add_le` and `norm_Gamma_half_add_le` at `w = 2i`:
`‖1/Γ(½ + 2i)‖ ≤ exp(3/8 + π)` and `‖Γ(½ + 2i)‖ ≤ √(2π) exp(3/8 − π)`. -/
theorem norm_Gamma_bounds_two_I :
    ‖(Gamma (2 * I + 1 / 2))⁻¹‖ ≤ Real.exp (3 / 8 + π) ∧
      ‖Gamma (2 * I + 1 / 2)‖ ≤ √(2 * π) * Real.exp (3 / 8 - π) := by
  have hR : 2 ≤ ‖2 * I‖ ^ 2 := by
    rw [norm_two_I]
    norm_num
  have hre : 0 ≤ (2 * I).re := by simp
  have h1 := norm_inv_Gamma_half_add_le hR
  have h2 := norm_Gamma_half_add_le hre hR
  rw [norm_two_I, re_stirF_two_I] at h1 h2
  constructor
  · convert h1 using 2
    ring
  · convert h2 using 3
    ring

/-- **Junk value**: Lean's `log 0 = 0` gives `f(0) = 0`, which is also the limit of
`w log w − w` at `0`. -/
theorem stirF_zero : stirF 0 = 0 := by
  simp [stirF]

/-- **Junk value**: Mathlib's `Γ(−n) = 0` gives `1/Γ(−n) = 0`, the true value of the entire
function `1/Γ`. -/
theorem inv_Gamma_neg_nat (n : ℕ) : (Gamma (-(n : ℂ)))⁻¹ = 0 := by
  rw [Complex.Gamma_neg_nat_eq_zero, inv_zero]

end Lightlike.Asymptotics
