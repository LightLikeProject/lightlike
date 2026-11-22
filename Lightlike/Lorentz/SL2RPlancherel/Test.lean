import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.Link
import Lightlike.Lorentz.SL2RPlancherel.NoInvariantForm

/-!
# Trust checks for HA3 (`SL(2,ℝ)` series and Plancherel density)

* Casimir values: principal `-(1+ν²)/4 ≤ -1/4`, discrete `n/2 (n/2 - 1) ≥ 0`, complementary
  `(τ²-1)/4`; the dictionary `ρ = ν/2`.
* The density `ρ tanh(πρ)` is positive for `ρ ≠ 0`, even, and `≈ ρ` at large `ρ`
  (here: `< ρ` for `ρ > 0` since `tanh < 1`).
* A complementary parameter `|τ| > 1` has no invariant positive form.
-/

open Complex
open Lightlike.Lorentz.SL2RPlancherel

example (ν : ℝ) : (-(1 + (ν : ℂ) ^ 2) / 4).re ≤ -1 / 4 :=
  Lightlike.Lorentz.SL2R.casimir_principal_le ν

-- Casimir at ν = 0 (the most degenerate principal series) is -1/4, i.e. ρ = 0.
example : (-(1 + ((0 : ℝ) : ℂ) ^ 2) / 4) = -(1 / 4) := by simp; ring

-- Casimir of the discrete series of weight 2 (n = 2): 0.
example : ((2 : ℝ) / 2) * ((2 : ℝ) / 2 - 1) = 0 := by norm_num

-- Casimir of the discrete series of weight 4 (n = 4): 2.
example : ((4 : ℝ) / 2) * ((4 : ℝ) / 2 - 1) = 2 := by norm_num

-- ν = 2ρ, ρ = 1/2: Casimir -(1+1)/4 = -1/2 = -(1/4+1/4).
example : (-(1 + ((1 : ℝ) : ℂ) ^ 2) / 4) = -(1 / 4 + (((1 / 2 : ℝ)) : ℂ) ^ 2) := by
  simpa using casimir_principal_eq_rho 1

example (ρ : ℝ) (h : 0 < ρ) : 0 < ρ * Real.tanh (Real.pi * ρ) := density_pos h.ne'

example (ρ : ℝ) (h : 0 < ρ) : ρ * Real.tanh (Real.pi * ρ) < ρ := by
  have := Real.tanh_lt_one (Real.pi * ρ)
  nlinarith

-- the complementary series at τ = 2 (outside (-1,1)) has positive Casimir value 3/4
example : 0 < ((2 : ℝ) ^ 2 - 1) / 4 := by norm_num
example : (1 : ℝ) < |(2 : ℝ)| := by norm_num [abs_of_pos]

example (B : smoothFns →ₛₗ[starRingEnd ℂ] smoothFns →ₗ[ℂ] ℂ)
    (hBE : ∀ u w, B (opE 2 u) w + B u (opE 2 w) = 0) (hBF : ∀ u w, B (opF u) w + B u (opF w) = 0)
    (hBH : ∀ u w, B (opH 2 u) w + B u (opH 2 w) = 0) :
    ¬ ∀ u, u ≠ 0 → 0 < (B u u).re :=
  no_invariant_form_smooth 2 (by norm_num [abs_of_pos]) B hBE hBF hBH
