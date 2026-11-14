import Lightlike.Asymptotics.Stirling

/-!
# Trust checks for the complex Stirling formula

* **Known value.** At `w = ½`, `Γ(1) = 1` gives `√(2π) exp(f(½) + μ(½)) = 1` (`stir_half`).
* **The remainder is needed.** Without `μ` the formula fails at `w = ½`: it would say
  `√π e^{−½} = 1`, that is `π = e` (`not_Gamma_half_add_without_mu`).
* **The midpoint shift is needed.** With `Γ(w)` in place of `Γ(w + ½)` the formula fails at
  `w = ½`, since `Γ(½) = √π ≠ 1` (`not_Gamma_without_half`).

`scripts/asymptotics/stirling_check.py` compares `μ(w)` with `log Γ(w + ½) − f(w) − ½ log 2π` and
with the bound `norm_stirMu_le` at complex points (numerical evidence).
-/

open Complex

namespace Lightlike.Asymptotics

/-- `½` lies in the slit plane. -/
lemma half_mem_slitPlane : (1 / 2 : ℂ) ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left; norm_num

/-- **Known value**: `Γ(1) = 1` gives `√(2π) exp(f(½) + μ(½)) = 1`. -/
theorem stir_half : ((√(2 * Real.pi) : ℝ) : ℂ) * exp (stirF (1 / 2) + stirMu (1 / 2)) = 1 := by
  rw [← Gamma_half_add half_mem_slitPlane, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num,
    Complex.Gamma_one]

/-- **Wrong input fails: no remainder.** `Γ(w + ½) = √(2π) exp(w log w − w)` is false at `w = ½`:
it would give `√π e^{−½} = 1`, i.e. `π = e`. -/
theorem not_Gamma_half_add_without_mu :
    Gamma (1 / 2 + 1 / 2) ≠ ((√(2 * Real.pi) : ℝ) : ℂ) * exp (stirF (1 / 2)) := by
  rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Complex.Gamma_one]
  have hF : stirF (1 / 2) = (((1 / 2 : ℝ) * Real.log (1 / 2) - 1 / 2 : ℝ) : ℂ) := by
    rw [stirF, ← show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by push_cast; ring,
      ← ofReal_log (by norm_num)]
    push_cast; ring
  rw [hF, ← ofReal_exp]
  intro h
  have hr : (1 : ℝ) = √(2 * Real.pi) * Real.exp ((1 / 2) * Real.log (1 / 2) - 1 / 2) := by
    exact_mod_cast h
  have hx2 : Real.exp ((1 / 2) * Real.log (1 / 2) - 1 / 2) ^ 2 = (1 / 2) / Real.exp 1 := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * ((1 / 2) * Real.log (1 / 2) - 1 / 2) =
      Real.log (1 / 2) - 1 by push_cast; ring, Real.exp_sub, Real.exp_log (by norm_num)]
  have hs : √(2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have h1 : (1 : ℝ) = 2 * Real.pi * ((1 / 2) / Real.exp 1) := by
    calc (1 : ℝ) = (√(2 * Real.pi) * Real.exp ((1 / 2) * Real.log (1 / 2) - 1 / 2)) ^ 2 := by
          rw [← hr]; norm_num
      _ = 2 * Real.pi * ((1 / 2) / Real.exp 1) := by rw [mul_pow, hs, hx2]
  have he : Real.exp 1 = Real.pi := by
    have := Real.exp_pos 1
    field_simp at h1
    linarith
  linarith [Real.pi_gt_three, Real.exp_one_lt_d9]

/-- **Wrong input fails: no midpoint shift.** `Γ(w) = √(2π) exp(f(w) + μ(w))` is false at
`w = ½`, since `Γ(½) = √π` while the right side is `Γ(1) = 1`. -/
theorem not_Gamma_without_half :
    Gamma (1 / 2) ≠ ((√(2 * Real.pi) : ℝ) : ℂ) * exp (stirF (1 / 2) + stirMu (1 / 2)) := by
  rw [stir_half]
  have hG : Gamma (1 / 2 : ℂ) = ((√Real.pi : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
      Real.Gamma_one_half_eq]
  rw [hG]
  intro h
  have h1 : √Real.pi = 1 := by exact_mod_cast h
  rw [Real.sqrt_eq_one] at h1
  linarith [Real.pi_gt_three]

end Lightlike.Asymptotics
