import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.DiscreteCasimir
import Lightlike.Lorentz.SL2RPlancherel.CasimirSymmetry
import Lightlike.Lorentz.SL2RPlancherel.PrincipalCasimir
import Lightlike.Lorentz.SL2RPlancherel.PrincipalDecay

/-!
# The principal-series coefficients are orthogonal to the discrete directions

Behaviour of the discrete directions `φ_i = (cosh ξ - 1)^{i+s} / sinh^{l+s} ξ` of the block
`(l, -s)`, `l - s ≤ i < l`: on `ξ > 0`,
`φ_i = 2^{i+s} / 2^{l+s} · sinh(ξ/2)^{2i+s-l} / cosh(ξ/2)^{l+s}`, a function continuous on all of `ℝ`
(`phiN_eq_phiHalf`), and `φ_i sinh ξ ≤ 1` for `ξ ≥ 1` (`phiN_mul_sinh_le_one`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (opposite-sign blocks), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The continuous extension `2^{i+s}/2^{l+s} sinh(ξ/2)^{2(i+s)-(l+s)} / cosh(ξ/2)^{l+s}` of `φ_i`. -/
def phiHalf (s l i : ℕ) (ξ : ℝ) : ℝ :=
  (2 : ℝ) ^ (i + s) / 2 ^ (l + s) * Real.sinh (ξ / 2) ^ (2 * (i + s) - (l + s)) /
    Real.cosh (ξ / 2) ^ (l + s)

lemma continuous_phiHalf (s l i : ℕ) : Continuous (phiHalf s l i) := by
  unfold phiHalf
  exact (continuous_const.mul ((Real.continuous_sinh.comp (continuous_id.div_const 2)).pow _)).div
    ((Real.continuous_cosh.comp (continuous_id.div_const 2)).pow _)
    fun ξ => pow_ne_zero _ (Real.cosh_pos _).ne'

/-- On `ξ > 0`, `φ_i` is its continuous extension. -/
theorem phiN_eq_phiHalf (s l i : ℕ) (hli : l ≤ i + s) {ξ : ℝ} (hξ : 0 < ξ) :
    phiN s l i ξ = phiHalf s l i ξ := by
  have hsh : Real.sinh (ξ / 2) ≠ 0 := (Real.sinh_pos_iff.2 (by linarith)).ne'
  have hch : Real.cosh (ξ / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have h1 : Real.cosh ξ - 1 = 2 * Real.sinh (ξ / 2) ^ 2 := by
    have := Real.cosh_two_mul (ξ / 2)
    rw [show 2 * (ξ / 2) = ξ by ring] at this
    have hc := Real.cosh_sq_sub_sinh_sq (ξ / 2)
    nlinarith
  have h2 : Real.sinh ξ = 2 * Real.sinh (ξ / 2) * Real.cosh (ξ / 2) := by
    have := Real.sinh_two_mul (ξ / 2)
    rwa [show 2 * (ξ / 2) = ξ by ring] at this
  have hk : Real.sinh (ξ / 2) ^ (2 * (i + s)) =
      Real.sinh (ξ / 2) ^ (2 * (i + s) - (l + s)) * Real.sinh (ξ / 2) ^ (l + s) := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  rw [phiN, phiHalf, h1, h2, mul_pow, mul_pow, mul_pow, ← pow_mul, hk]
  field_simp

/-- `φ_i sinh ξ ≤ 1` for `ξ ≥ 1` and `i < l`. -/
theorem phiN_mul_sinh_le_one (s l i : ℕ) (hil : i < l) {ξ : ℝ} (hξ : 1 ≤ ξ) :
    phiN s l i ξ * Real.sinh ξ ≤ 1 := by
  have hsh1 : 1 ≤ Real.sinh ξ := by
    have h1 : 1 ≤ Real.sinh 1 := by
      rw [Real.sinh_eq, Real.exp_neg]
      have he := Real.exp_one_gt_d9
      have hinv : (Real.exp 1)⁻¹ < 1 / 2 := by
        rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]; norm_num; linarith
      linarith
    exact h1.trans (Real.sinh_le_sinh.2 hξ)
  have hsh0 : 0 < Real.sinh ξ := by linarith
  have hc1 : 0 ≤ Real.cosh ξ - 1 := by linarith [Real.one_le_cosh ξ]
  have hcs : Real.cosh ξ - 1 ≤ Real.sinh ξ := by
    have := Real.cosh_sub_sinh ξ
    have := Real.exp_le_one_iff.2 (show -ξ ≤ 0 by linarith)
    linarith
  have hb : l + s = (l + s - 1) + 1 := by omega
  rw [phiN, hb, pow_succ, div_mul_eq_mul_div, mul_div_mul_right _ _ hsh0.ne',
    div_le_one (pow_pos hsh0 _)]
  calc (Real.cosh ξ - 1) ^ (i + s) ≤ Real.sinh ξ ^ (i + s) := pow_le_pow_left₀ hc1 hcs _
    _ ≤ Real.sinh ξ ^ (l + s - 1) := pow_le_pow_right₀ hsh1 (by omega)

end Lightlike.Lorentz.SL2RPlancherel
