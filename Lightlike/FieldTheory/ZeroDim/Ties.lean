import Lightlike.FieldTheory.ZeroDim.GraphRules
import Lightlike.FieldTheory.ZeroDim.FormalIntegral
import Lightlike.FieldTheory.ZeroDim.Quartic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The formal partition function, the formal integral and the Gaussian moments

`formalZ μ` (`GraphRules.lean`, Borinsky p. 116) records the coefficient `(n - 1)!! [x^n] (Σ_d μ_d x^d/d!)^k / k!`
of `X^n Y^k`, standing for `ħ^{n/2 - k}`. Here:

* `dfact_eq_integral`: the factor `(n - 1)!!` (`0` for odd `n`) is the Gaussian moment `∫ x^n dγ` of the standard
  Gaussian measure, so `coeff_formalZ_eq_integral`: the coefficient is `(∫ x^n dγ) / k! · [x^n] V^k`, the term of
  `∫ dγ (V(x))^k / k!` with `x^n`;
* `coeff_formalIntegral_eq_formalZ`: Borinsky's formal integral (Definition 3.1.1, `a = 1`) is `formalZ` read along
  `n = 2(K + m)`, `k = m`: its `ħ^K` coefficient is the sum of the `formalZ` coefficients with `n/2 - k = K`;
* `tendsto_quartic_div`: the explicit bound of `quartic_expansion` gives the asymptotic expansion of the quartic
  integral in Skinner's sense (eq. (2.20)): after `N + 1` terms the error is `o(g^N)` as `g → 0⁺`.
-/

open MeasureTheory ProbabilityTheory PowerSeries Finset Filter Real
open scoped Topology Nat

namespace Lightlike.FieldTheory

open GraphAlg

/-- **The double factorial of `formalZ` is a Gaussian moment**: `∫ x^n dγ = (n - 1)!!` for even `n` and `0` for odd
`n`, `γ` the standard Gaussian measure. -/
theorem dfact_eq_integral (n : ℕ) : ((dfact n : ℕ) : ℝ) = ∫ x, x ^ n ∂(gaussianReal 0 1) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h := integral_pow_mul_gauss k
    have hk : k + k = 2 * k := by ring
    rw [hk]
    have e : (fun x : ℝ => (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) * x ^ (2 * k)) =
        fun x => (√(2 * π))⁻¹ * (x ^ (2 * k) * rexp (-(x ^ 2 / 2))) := by
      funext x; rw [neg_div]; ring
    rw [e, integral_const_mul, h, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    simp [dfact]
  · have hodd : ∀ x : ℝ, (√(2 * π))⁻¹ * rexp (-(-x) ^ 2 / 2) * (-x) ^ (2 * k + 1) =
        -((√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) * x ^ (2 * k + 1)) := fun x => by
      rw [neg_sq, Odd.neg_pow ⟨k, rfl⟩]; ring
    have hneg := integral_neg_eq_self (fun x : ℝ => (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) * x ^ (2 * k + 1)) volume
    simp only [hodd, integral_neg] at hneg
    have h0 : ∫ x : ℝ, (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) * x ^ (2 * k + 1) = 0 := by linarith
    rw [h0]
    have : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.2 ⟨k, rfl⟩
    simp [dfact, this]

/-- **The coefficients of `formalZ` as Gaussian integrals**: the coefficient of `X^n Y^k` is
`(∫ x^n dγ) / k! · [x^n] V^k`, `V = Σ_d μ_d x^d/d!`. -/
theorem coeff_formalZ_eq_integral (μ : ℕ → ℝ) (n k : ℕ) :
    coeff k (coeff n (formalZ μ)) =
      (∫ x, x ^ n ∂(gaussianReal 0 1)) / (k.factorial : ℝ) * coeff n (egf μ ^ k) := by
  rw [← dfact_eq_integral]
  simp [formalZ, div_eq_mul_inv]

/-- **Borinsky's formal integral is `formalZ` read along `n = 2(K + m)`, `k = m`** (Definition 3.1.1 with `a = 1`,
`V = Σ_d μ_d x^d/d!`): the `ħ^K` coefficient of the formal integral is the sum of the coefficients of `formalZ` with
`n/2 - k = K`, `k ≤ 2K`. -/
theorem coeff_formalIntegral_eq_formalZ (μ : ℕ → ℝ) (K : ℕ) :
    coeff K (formalIntegral 1 (egf μ)) =
      ∑ m ∈ range (2 * K + 1), coeff m (coeff (2 * (K + m)) (formalZ μ)) := by
  simp only [formalIntegral, coeff_mk, Real.sqrt_one, one_mul, one_pow, formalZ]
  refine Finset.sum_congr rfl fun m _ => ?_
  have he : Even (2 * (K + m)) := even_two_mul _
  simp only [dfact, he, ite_true, eq_ratCast, Rat.cast_div, Rat.cast_natCast]
  ring

/-- **The quartic integral has the asymptotic expansion** of Skinner's (2.28) in the sense of (2.20): for every
`N`, `(Z(g) - √(2π) Σ_{m ≤ N} (-g/24)^m (4m - 1)!!/m!) / g^N → 0` as `g → 0⁺`. -/
theorem tendsto_quartic_div (N : ℕ) :
    Tendsto (fun g : ℝ => ((∫ x : ℝ, Real.exp (-(x ^ 2 / 2) - g * x ^ 4 / 24)) -
        √(2 * π) * ∑ m ∈ range (N + 1), (-g / 24) ^ m * ((4 * m - 1)‼ : ℕ) / (m.factorial : ℝ)) / g ^ N)
      (𝓝[>] 0) (𝓝 0) := by
  set C : ℝ := √(2 * π) * ((1 / 24) ^ (N + 1) * ((4 * (N + 1) - 1)‼ : ℕ) / ((N + 1).factorial : ℝ))
  have hbound : ∀ g : ℝ, 0 < g → |((∫ x : ℝ, Real.exp (-(x ^ 2 / 2) - g * x ^ 4 / 24)) -
      √(2 * π) * ∑ m ∈ range (N + 1), (-g / 24) ^ m * ((4 * m - 1)‼ : ℕ) / (m.factorial : ℝ)) / g ^ N| ≤ C * g := by
    intro g hg
    have h := quartic_expansion hg.le (N + 1)
    have hgN : 0 < g ^ N := pow_pos hg N
    rw [abs_div, abs_of_pos hgN, div_le_iff₀ hgN]
    calc _ ≤ √(2 * π) * ((g / 24) ^ (N + 1) * ((4 * (N + 1) - 1)‼ : ℕ) / ((N + 1).factorial : ℝ)) := h
      _ = C * g * g ^ N := by simp only [C, div_pow, pow_succ]; ring
  have hC : Tendsto (fun g : ℝ => C * g) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun g : ℝ => C * g) (𝓝 0) (𝓝 (C * 0)) := (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hC
  filter_upwards [self_mem_nhdsWithin] with g hg
  exact hbound g hg

end Lightlike.FieldTheory
