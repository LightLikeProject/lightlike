import Mathlib
import Lightlike.TuraevViro.QSixJGenericKL

/-!
# The generic Biedenharn–Elliott identity from the Temperley–Lieb pentagon

This file proves `GenBE θ` (`Lightlike.TV.GenBE`, the generic Biedenharn–Elliott identity at the angle
`θ`, without square roots) from the pentagon identity `TemperleyLieb.pentagon` of the recoupling
coefficients `Fc` of the Temperley–Lieb model at `q = e^{iθ}`, given that `Fc` is the Kauffman–Lins
coefficient `klCoef` on its admissible indices (`TemperleyLieb.FcEqKL ℂ`, taken as a hypothesis until
it is proved).

Part 1: the side conditions of the pentagon at `q = e^{iθ}` from `sin (nθ) ≠ 0`:
`qE_pow_ne_one` (`q^{2n} ≠ 1`), `loopVal_qE_ne_zero`, `chebD_qE_ne_zero`, `qfG_ne_zero`.
-/

open Complex Finset

namespace Lightlike.TV

open Lightlike.TemperleyLieb

/-! ## The side conditions at `q = e^{iθ}` -/

/-- `q^{2n} ≠ 1` at `q = e^{iθ}` when `sin (nθ) ≠ 0`. -/
theorem qE_pow_ne_one {θ : ℝ} {n : ℕ} (h : Real.sin (n * θ) ≠ 0) :
    ((qE θ : ℂˣ) : ℂ) ^ (2 * n) ≠ 1 := by
  rw [coe_qE, ← exp_nat_mul]
  intro h1
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h1
  apply h
  have him := congrArg Complex.im hk
  simp only [mul_im, mul_re, natCast_re, natCast_im, ofReal_re, ofReal_im, I_re, I_im, intCast_re,
    intCast_im, re_ofNat, im_ofNat] at him
  push_cast at him
  have h3 : n * θ = k * Real.pi := by linarith
  rw [h3, Real.sin_int_mul_pi]

/-- `q - q⁻¹ = 2 i sin θ` at `q = e^{iθ}`. -/
theorem qE_sub_inv (θ : ℝ) : ((qE θ : ℂˣ) : ℂ) - ((qE θ : ℂˣ) : ℂ)⁻¹ = 2 * I * (Real.sin θ : ℂ) := by
  rw [coe_qE, show (θ : ℂ) * I = ((θ : ℝ) : ℂ) * I from rfl, exp_sub_exp_neg]

theorem qE_sub_inv_ne_zero {θ : ℝ} (h : Real.sin θ ≠ 0) :
    ((qE θ : ℂˣ) : ℂ) - ((qE θ : ℂˣ) : ℂ)⁻¹ ≠ 0 := by
  rw [qE_sub_inv]
  exact mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (ofReal_ne_zero.2 h)

/-- `[n]_θ ≠ 0` when `sin (nθ) ≠ 0` and `sin θ ≠ 0`. -/
theorem qnG_ne_zero {θ : ℝ} {n : ℕ} (h1 : Real.sin θ ≠ 0) (hn : Real.sin (n * θ) ≠ 0) :
    qnG θ n ≠ 0 :=
  div_ne_zero hn h1

/-- The quantum factorials up to `N` do not vanish when `sin (nθ) ≠ 0` for `1 ≤ n ≤ N`. -/
theorem qfG_ne_zero {θ : ℝ} {N : ℕ} (hθ : ∀ n, 1 ≤ n → n ≤ N → Real.sin (n * θ) ≠ 0)
    (h1 : Real.sin θ ≠ 0) : ∀ m, m ≤ N → qfG θ m ≠ 0 := by
  intro m hm
  induction m with
  | zero => simp [qfG]
  | succ m ih =>
    rw [qfG_succ]
    exact mul_ne_zero (ih (by omega)) (qnG_ne_zero h1 (by exact_mod_cast hθ (m + 1) (by omega) hm))

/-- The loop value `-(q + q⁻¹) = -2 cos θ` does not vanish when `sin (2θ) ≠ 0`. -/
theorem loopVal_qE_ne_zero {θ : ℝ} (h : Real.sin (2 * θ) ≠ 0) : loopVal (qE θ) ≠ 0 := by
  rw [loopVal_eq, coe_qE, ← exp_neg]
  have hc : exp (θ * I) + exp (-(θ * I)) = 2 * (Real.cos θ : ℂ) := by
    rw [ofReal_cos, cos]; ring_nf
  rw [hc, neg_ne_zero]
  refine mul_ne_zero two_ne_zero (ofReal_ne_zero.2 fun hc0 => h ?_)
  rw [Real.sin_two_mul, hc0, mul_zero]

/-- The Chebyshev values `chebD (loopVal q) n = (-1)^n [n+1]` do not vanish. -/
theorem chebD_qE_ne_zero {θ : ℝ} {n : ℕ} (h1 : Real.sin θ ≠ 0) (hn : Real.sin ((n + 1 : ℕ) * θ) ≠ 0) :
    chebD (loopVal (qE θ)) n ≠ 0 := by
  rw [chebD_eq_qb _ (qE_sub_inv_ne_zero h1), qb_qE]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ofReal_ne_zero.2 (qnG_ne_zero h1 hn))

end Lightlike.TV
