import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.LadderOppositeOrth

/-!
# The radial Casimir on the discrete directions of an opposite-sign block

The discrete directions `φ_i = (cosh ξ - 1)^{i+s} / sinh^{l+s} ξ` of the block `(l, -s)` have the
logarithmic derivative `((i - l) cosh ξ + (i + s)) / sinh ξ` (`hasDerivAt_phiN`), and the radial
Casimir acts on them triangularly:
`radialCasimir_{l,-s} φ_i = -(l - i)(l - i - 1) φ_i - 2i(i - l + s) φ_{i-1}`.
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (opposite-sign blocks), milestone HA3.
-/

open MeasureTheory Set

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

lemma natCast_mul_pow_sub_one {x : ℝ} (hx : x ≠ 0) (a : ℕ) :
    (a : ℝ) * x ^ (a - 1) = a * x ^ a / x := by
  cases a with
  | zero => simp
  | succ a => simp only [Nat.cast_succ, Nat.add_sub_cancel, pow_succ]; field_simp

/-- The logarithmic derivative `((i - l) cosh ξ + (i + s)) / sinh ξ` of `φ_i`. -/
def phiLog (s l i : ℕ) (ξ : ℝ) : ℝ := (((i : ℝ) - l) * Real.cosh ξ + (i + s)) / Real.sinh ξ

lemma sinh_sq_eq_mul (ξ : ℝ) : Real.sinh ξ ^ 2 = (Real.cosh ξ - 1) * (Real.cosh ξ + 1) := by
  have := Real.cosh_sq_sub_sinh_sq ξ
  nlinarith

/-- `φ_i' = φ_i · ((i - l) cosh ξ + (i + s)) / sinh ξ` on `ξ > 0`. -/
theorem hasDerivAt_phiN (s l i : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (phiN s l i) (phiN s l i ξ * phiLog s l i ξ) ξ := by
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  have hc1 : Real.cosh ξ - 1 ≠ 0 := (sub_pos.2 (Real.one_lt_cosh.2 hξ.ne')).ne'
  have h1 := ((Real.hasDerivAt_cosh ξ).sub_const 1).pow (i + s)
  have h2 := (Real.hasDerivAt_sinh ξ).pow (l + s)
  have h := h1.div h2 (pow_ne_zero _ hs)
  have hsq := sinh_sq_eq_mul ξ
  convert h using 1
  · funext x
    simp only [phiN, Pi.div_apply, Pi.pow_apply]
  · simp only [Pi.pow_apply]
    rw [natCast_mul_pow_sub_one hc1, natCast_mul_pow_sub_one hs, phiN, phiLog]
    field_simp
    push_cast
    linear_combination (-((i : ℝ) + s)) * hsq

/-- The derivative of the logarithmic derivative. -/
lemma hasDerivAt_phiLog (s l i : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (phiLog s l i) ((-((i : ℝ) - l) - (i + s) * Real.cosh ξ) / Real.sinh ξ ^ 2) ξ := by
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  have h := (((Real.hasDerivAt_cosh ξ).const_mul ((i : ℝ) - l)).add_const ((i : ℝ) + s)).div
    (Real.hasDerivAt_sinh ξ) hs
  have hc := Real.cosh_sq_sub_sinh_sq ξ
  convert h using 1
  · funext x
    simp only [phiLog, Pi.div_apply]
  · field_simp
    linear_combination ((i : ℝ) - l) * hc

/-- The real form of the Casimir identity for `φ_i`. -/
lemma casimir_phiN_real (s l i : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    -(phiN s l i ξ * phiLog s l i ξ * phiLog s l i ξ + phiN s l i ξ *
        ((-((i : ℝ) - l) - (i + s) * Real.cosh ξ) / Real.sinh ξ ^ 2)) -
      Real.cosh ξ / Real.sinh ξ * (phiN s l i ξ * phiLog s l i ξ) +
      ((l : ℝ) ^ 2 + (-(s : ℝ)) ^ 2 + 2 * l * (-(s : ℝ)) * Real.cosh ξ) / Real.sinh ξ ^ 2 *
        phiN s l i ξ =
    -(((l : ℝ) - i) * ((l : ℝ) - i - 1)) * phiN s l i ξ -
      2 * i * ((i : ℝ) - l + s) * (phiN s l i ξ / (Real.cosh ξ - 1)) := by
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  have hc1 : Real.cosh ξ - 1 ≠ 0 := (sub_pos.2 (Real.one_lt_cosh.2 hξ.ne')).ne'
  have hsq := sinh_sq_eq_mul ξ
  simp only [phiLog]
  field_simp
  linear_combination phiN s l i ξ * (Real.cosh ξ * (i : ℝ) ^ 2 - 2 * Real.cosh ξ * i * l +
    Real.cosh ξ * i + Real.cosh ξ * (l : ℝ) ^ 2 - Real.cosh ξ * l + (i : ℝ) ^ 2 + 2 * i * s - i -
    (l : ℝ) ^ 2 + l) * hsq

/-- **The radial Casimir on the discrete directions**: on `ξ > 0`,
`radialCasimir_{l,-s} φ_i = -(l - i)(l - i - 1) φ_i - 2i(i - l + s) φ_i / (cosh ξ - 1)`. -/
theorem radialCasimir_phiN (s l i : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    radialCasimir l (-(s : ℝ)) (fun t => ((phiN s l i t : ℝ) : ℂ)) ξ =
      ((-(((l : ℝ) - i) * ((l : ℝ) - i - 1)) * phiN s l i ξ -
        2 * i * ((i : ℝ) - l + s) * (phiN s l i ξ / (Real.cosh ξ - 1)) : ℝ) : ℂ) := by
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  have hc1 : Real.cosh ξ - 1 ≠ 0 := (sub_pos.2 (Real.one_lt_cosh.2 hξ.ne')).ne'
  have hd1 : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t => ((phiN s l i t : ℝ) : ℂ))
      (((phiN s l i t * phiLog s l i t : ℝ) : ℂ)) t :=
    fun t ht => (hasDerivAt_phiN s l i ht).ofReal_comp
  have hderiv : deriv (fun t => ((phiN s l i t : ℝ) : ℂ)) =ᶠ[nhds ξ]
      fun t => ((phiN s l i t * phiLog s l i t : ℝ) : ℂ) := by
    filter_upwards [Ioi_mem_nhds hξ] with t ht using (hd1 t ht).deriv
  have hd2 : HasDerivAt (fun t => ((phiN s l i t * phiLog s l i t : ℝ) : ℂ))
      (((phiN s l i ξ * phiLog s l i ξ * phiLog s l i ξ + phiN s l i ξ *
        ((-((i : ℝ) - l) - (i + s) * Real.cosh ξ) / Real.sinh ξ ^ 2) : ℝ) : ℂ)) ξ :=
    ((hasDerivAt_phiN s l i hξ).mul (hasDerivAt_phiLog s l i hξ)).ofReal_comp
  unfold radialCasimir
  rw [hderiv.deriv_eq, hd2.deriv, (hd1 ξ hξ).deriv]
  have key := congrArg (fun x : ℝ => (x : ℂ)) (casimir_phiN_real s l i hξ)
  push_cast at key ⊢
  linear_combination key

end Lightlike.Lorentz.SL2RPlancherel
