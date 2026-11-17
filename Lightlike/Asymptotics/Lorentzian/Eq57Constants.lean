import Lightlike.Asymptotics.Lorentzian.Amplitude
import Lightlike.Asymptotics.Lorentzian.Parity

/-!
# The numerical factor of the Lorentzian asymptotic formula (BDFHP eq. (57))

Barrett, Dowdall, Fairbairn, Hellmann, Pereira (arXiv:0907.2440, `bdfhp-2010`), Sec. 6.4, p. 30, give
the asymptotic formula (53) of the 4-simplex amplitude with the numerical factors
`N|crit = (2π)²² · 2⁴ / √(det H|crit) · ∏_{a<b} 2 k_ab c_ab Ω_ab|crit` (eq. (57), first line) and, for
`p_ab = γ k_ab`, `N|crit = 2³⁶ π¹² ((1 + iγ)/(1 - iγ))⁵ (1/√(det H|crit)) ∏ k_ab Ω_ab|crit`
(eq. (57), second line). Here `(2π)²²` is the stationary phase in `6 × 4 + 20 = 44` real
dimensions, `2⁴` counts the two spin lifts `X_a ↦ -X_a` of each of the four group elements (Sec. 4.1,
p. 16, "spin lift" symmetry), `c_ab = √(k_ab² + p_ab²)/(π (k_ab - i p_ab))` is the constant of the
propagator (Sec. 3, p. 15; equal to `π⁻¹ √((1 + iγ)/(1 - iγ))` for `p = γ k`, p. 31), `2 k_ab` comes from
`d_{k_ab} ∼ 2 λ k_ab` for large `λ` (p. 30), `H` is the Hessian of the action (17) at the critical point
(Appendix A, p. 32) and `Ω_ab|crit` the measure term (a choice of coordinates is needed; only the ratio
`∏ Ω_ab / √det H` is independent of it, p. 31).

This file defines `bdfhpC` and `bdfhpN`, the two expressions as written by the source with the
square root of the determinant as a given number (`sqrtDetH`: BDFHP write `√det H` without a branch,
and the branch is the one of `invSqrtDet`), proves that the first line equals the second
(`bdfhpN_eq`: algebra with `c_ab`, `(√(1 + γ²))¹⁰ = ((1 + iγ)(1 - iγ))⁵`), and the scaling
`Ω_e ↦ |κ|⁻⁴ Ω_e` of the density under `z_e ↦ κ z_e` (`lorEdgeDensity_smul`), which relates `Ω` at
the unit critical spinors to `Ω` in the chart `z = (w, 1)`.

Not here: the identification of `N|crit` with the coefficient of `lorVertex_asymptotics_fixChart` (it
needs the Haar normalisation `s` against the normalisation of `c_ab dk_ab Ω_ab` in BDFHP, the
transition Jacobian between the chart of the Hessian and the fixed chart, and the phase
`((1 + iγ)/(1 - iγ))^(1/2)` per edge that our constants `c_e = (n_e + 1)/π` do not have), and the sign
`(-1)^χ` of (53).

## Main results

* `bdfhpC`, `bdfhpN`: the constant `c_ab` and the factor `N|crit` of eq. (57), first line.
* `bdfhpN_eq`: the second line of (57) for `p = γ k`.
* `lorEdgeDensity_smul`: `Ω_e` under `z_e ↦ κ z_e`.

## References

* `bdfhp-2010`, eq. (57), Sec. 6.4 p. 30; `c_ab`, Sec. 3 p. 15; the factor `2⁴`, Sec. 4.1 p. 16.
-/

open Complex MeasureTheory
open scoped ComplexConjugate Matrix NNReal
open Lightlike.Lorentz (SL2C)
open Lightlike.Asymptotics.EPRL

namespace Lightlike.Asymptotics.Lorentzian

/-- **BDFHP's constant `c_ab`** (arXiv:0907.2440, Sec. 3 p. 15, below the formula for `P_ab`):
`c_ab = √(k² + p²) / (π (k - i p))`; for `p = γ k` it is `π⁻¹ √((1 + iγ)/(1 - iγ))` (p. 31). -/
noncomputable def bdfhpC (k p : ℝ) : ℂ :=
  ((Real.sqrt (k ^ 2 + p ^ 2) : ℝ) : ℂ) / ((Real.pi : ℂ) * ((k : ℂ) - Complex.I * p))

/-- **The numerical factor of BDFHP eq. (57)** (Sec. 6.4 p. 30), first line:
`N = (2π)²² · 2⁴ / √(det H) · ∏_{a<b} 2 k_ab c_ab Ω_ab`, with `det H` the determinant of the Hessian,
`Ω_ab` the measure term at the critical point and `2⁴` the two spin lifts `X_a ↦ -X_a` of each of the
four group elements. Here the square root of the determinant is the given number `sqrtDetH` (BDFHP
write `√det H` without a branch). -/
noncomputable def bdfhpN (k p : Fin 10 → ℝ) (Ω : Fin 10 → ℝ) (sqrtDetH : ℂ) : ℂ :=
  (2 * Real.pi) ^ 22 * 2 ^ 4 / sqrtDetH * ∏ e, (2 * (k e : ℂ) * bdfhpC (k e) (p e) * Ω e)

/-- **Eq. (57), second line** (p. 30): for `p = γ k`, `k > 0`,
`N = 2³⁶ π¹² ((1 + iγ)/(1 - iγ))⁵ (1/√det H) ∏ k_ab Ω_ab`. -/
theorem bdfhpN_eq (γ : ℝ) (k Ω : Fin 10 → ℝ) (hk : ∀ e, 0 < k e) (sqrtDetH : ℂ) :
    bdfhpN k (fun e => γ * k e) Ω sqrtDetH =
      2 ^ 36 * (Real.pi : ℂ) ^ 12 * ((1 + Complex.I * γ) / (1 - Complex.I * γ)) ^ 5 / sqrtDetH *
        ∏ e, ((k e : ℂ) * Ω e) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hg : (1 - Complex.I * γ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  set u : ℂ := 2 * ((Real.sqrt (1 + γ ^ 2) : ℝ) : ℂ) / ((Real.pi : ℂ) * (1 - Complex.I * γ)) with hu
  have hc : ∀ e, 2 * (k e : ℂ) * bdfhpC (k e) (γ * k e) * Ω e = u * ((k e : ℂ) * Ω e) := by
    intro e
    have hke : (k e : ℂ) ≠ 0 := by exact_mod_cast (hk e).ne'
    have hsq : Real.sqrt (k e ^ 2 + (γ * k e) ^ 2) = k e * Real.sqrt (1 + γ ^ 2) := by
      rw [show k e ^ 2 + (γ * k e) ^ 2 = (k e) ^ 2 * (1 + γ ^ 2) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (hk e).le]
    unfold bdfhpC
    rw [hsq]
    push_cast
    have : (k e : ℂ) - Complex.I * (γ * k e) = (k e : ℂ) * (1 - Complex.I * γ) := by ring
    rw [this, hu]
    field_simp
  unfold bdfhpN
  simp only [hc]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hu10 : u ^ 10 = 2 ^ 10 / (Real.pi : ℂ) ^ 10 * ((1 + Complex.I * γ) / (1 - Complex.I * γ)) ^ 5 := by
    have hs2 : ((Real.sqrt (1 + γ ^ 2) : ℝ) : ℂ) ^ 2 = (1 + Complex.I * γ) * (1 - Complex.I * γ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
      push_cast
      ring_nf
      simp [Complex.I_sq]
    have : ((Real.sqrt (1 + γ ^ 2) : ℝ) : ℂ) ^ 10 =
        ((1 + Complex.I * γ) * (1 - Complex.I * γ)) ^ 5 := by
      rw [show (10 : ℕ) = 2 * 5 by norm_num, pow_mul, hs2]
    rw [hu, div_pow, mul_pow, mul_pow, this, mul_pow, div_pow]
    field_simp
  rw [hu10]
  field_simp

/-- `Ω_e = 1/(‖Z_ab‖²‖Z_ba‖²)` scales by `|κ|⁻⁴` under `z_e ↦ κ z_e`. -/
theorem lorEdgeDensity_smul (X : Fin 5 → SL2C) (z : Fin 10 → Spinor) (e : Fin 10) {κ : ℂ} :
    lorEdgeDensity X (Function.update z e (κ • z e)) e = ‖κ‖⁻¹ ^ 4 * lorEdgeDensity X z e := by
  unfold lorEdgeDensity
  simp only [Function.update_self, spinAct_smul, norm_smul]
  by_cases hκ : ‖κ‖ = 0
  · simp [hκ]
  · field_simp

end Lightlike.Asymptotics.Lorentzian
