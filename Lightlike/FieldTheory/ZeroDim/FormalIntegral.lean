import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Zero-dimensional field theory as a formal power series (Borinsky 2018, Definition 3.1.1)

For `S(x) = -x²/(2a) + V(x)` with `V ∈ x³ ℝ[[x]]`, Borinsky's formal integral is
`F[S](ħ) = √a ∑_{n ≥ 0} (aħ)^n (2n - 1)!! [x^{2n}] e^{V(x)/ħ}` (eq. (3.1.2)). Expanding
`e^{V/ħ} = ∑_m V^m / (m! ħ^m)`, the coefficient of `ħ^k` is
`√a ∑_{m} a^{k+m} (2(k+m) - 1)!! [x^{2(k+m)}] V^m / m!`, and only `m ≤ 2k` contribute because
`[x^{2(k+m)}] V^m = 0` for `3m > 2(k+m)` (`formalIntegral`, `coeff_formalIntegral`).

Check: for `V = λ x⁴/4!` and `a = 1`, the coefficient of `ħ²` is `35 λ²/384` (Borinsky (3.1.8), p. 24;
`= 1/128 + 1/16 + 1/48` from the three vacuum graphs).
-/

namespace Lightlike.FieldTheory

open PowerSeries Nat

/-- **Borinsky's formal integral** (Definition 3.1.1), as the power series in `ħ` with the coefficients
`√a ∑_{m ≤ 2k} a^{k+m} (2(k+m) - 1)!! [x^{2(k+m)}] V^m / m!`. -/
noncomputable def formalIntegral (a : ℝ) (V : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => Real.sqrt a * ∑ m ∈ Finset.range (2 * k + 1),
    a ^ (k + m) * ((2 * (k + m) - 1)‼ : ℝ) * coeff (2 * (k + m)) (V ^ m) / (m ! : ℝ)

/-- The terms beyond `m = 2k` vanish for `V ∈ x³ ℝ[[x]]`. -/
lemma coeff_pow_eq_zero {V : PowerSeries ℝ} (hV : ∀ d < 3, coeff d V = 0) {m j : ℕ} (hj : j < 3 * m) :
    coeff j (V ^ m) = 0 := by
  obtain ⟨W, hW⟩ : (X : PowerSeries ℝ) ^ 3 ∣ V := PowerSeries.X_pow_dvd_iff.2 fun d hd => hV d hd
  rw [hW, mul_pow, ← pow_mul, coeff_X_pow_mul', if_neg (by omega)]

/-- **The `ħ²` coefficient of the quartic theory**: `35 λ² / 384`. -/
theorem formalIntegral_quartic_two (lam : ℝ) :
    coeff 2 (formalIntegral 1 (PowerSeries.C (lam / 24) * X ^ 4)) = 35 / 384 * lam ^ 2 := by
  simp only [formalIntegral, coeff_mk, Real.sqrt_one, one_mul, one_pow]
  rw [show 2 * 2 + 1 = 5 by rfl, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp only [mul_pow, ← map_pow, ← pow_mul, coeff_C_mul_X_pow]
  norm_num [Nat.doubleFactorial, Nat.factorial]
  ring

/-- **Trust check, order `λ²`**: the symmetry factors `1/128`, `1/16`, `1/48` of the three vacuum graphs
(two figure-eights, the double-bubble chain, the sunset) sum to the coefficient `35/384` (Borinsky (3.1.8)). -/
example : (1 : ℚ) / 128 + 1 / 16 + 1 / 48 = 35 / 384 := by norm_num

/-- **Trust check**: a wrong symmetry factor for the sunset (`1/24` instead of `1/48`) does not give the
coefficient. -/
example : (1 : ℚ) / 128 + 1 / 16 + 1 / 24 ≠ 35 / 384 := by norm_num

end Lightlike.FieldTheory
