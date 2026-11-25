import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Hawking radiation from a collapse geometry: the Bogoliubov coefficients and the Planck law (SC4, part 1)

Row G1-068 (milestone SC4).  In the 1+1-dimensional collapse model of Hawking's calculation (Carlip 2014,
§3.2; Hollands–Wald 2015, §2.2) the late-time outgoing null coordinate `u` is related to the affine
coordinate `v` on the ingoing null infinity by the exponential redshift `u = -(1/κ) log (-v/C)`, so the
outgoing mode `e^{-iωu} = (-v/C)^{iω/κ}`.  Its Bogoliubov coefficients against the ingoing modes `e^{∓iω'v}`
are Mellin–Fourier integrals `∫₀^∞ x^{is - 1} e^{± iω'x} dx` with `s = ω/κ`, whose value is
`Γ(is) (∓ iω')^{-is}`.  The two signs differ in the phase of `∓iω'`, and this gives
`|β_{ωω'}|² = e^{-2πω/κ} |α_{ωω'}|²`, hence, with the normalisation `|α|² - |β|² = 1`, the Planck law
`⟨N_ω⟩ = 1/(e^{2πω/κ} - 1)`, a thermal spectrum at `T = κ/2π`.

## Main statements

* `norm_kernelMinus_sq`: `|kernelMinus s w|² = e^{-2π s} |kernelPlus s w|²`.
* `planck_of_ratio`: from `a - b = 1` and `b = e^{-y} a` follows `b = 1/(e^y - 1)`.

The Mellin–Fourier integrals are *not* evaluated here: `kernelPlus`/`kernelMinus` are the closed forms.
-/

open Complex

namespace Lightlike.GR.HawkingRadiation

noncomputable section

/-- The closed form `Γ(is) (iw)^{-is}` of the Mellin–Fourier integral `∫₀^∞ x^{is-1} e^{iwx} dx`
(`w > 0`): the `α` Bogoliubov kernel of the collapse model, `s = ω/κ`, `w = ω'`. -/
def kernelPlus (s w : ℝ) : ℂ := Complex.Gamma (I * s) * ((w : ℂ) * I) ^ (-(I * s))

/-- The closed form `Γ(is) (-iw)^{-is}` of `∫₀^∞ x^{is-1} e^{-iwx} dx` (`w > 0`): the `β` Bogoliubov
kernel of the collapse model. -/
def kernelMinus (s w : ℝ) : ℂ := Complex.Gamma (I * s) * ((w : ℂ) * (-I)) ^ (-(I * s))

/-- The modulus of `(iw)^{-is}` is `e^{πs/2}`. -/
theorem norm_cpow_plus {s w : ℝ} (hw : 0 < w) :
    ‖((w : ℂ) * I) ^ (-(I * s))‖ = Real.exp (Real.pi * s / 2) := by
  have hne : ((w : ℂ) * I) ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hw.ne') I_ne_zero
  rw [norm_cpow_of_ne_zero hne, arg_real_mul I hw, arg_I]
  simp
  rw [Real.exp_neg]
  field_simp

/-- The modulus of `(-iw)^{-is}` is `e^{-πs/2}`. -/
theorem norm_cpow_minus {s w : ℝ} (hw : 0 < w) :
    ‖((w : ℂ) * (-I)) ^ (-(I * s))‖ = Real.exp (-(Real.pi * s / 2)) := by
  have hne : ((w : ℂ) * (-I)) ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr hw.ne') (neg_ne_zero.mpr I_ne_zero)
  rw [norm_cpow_of_ne_zero hne, arg_real_mul (-I) hw, arg_neg_I]
  simp
  rw [← Real.exp_neg]
  congr 1
  ring

/-- **The thermal ratio of the Bogoliubov kernels**: `|β|² = e^{-2πs} |α|²`, `s = ω/κ`, for every
`ω' = w > 0`. -/
theorem norm_kernelMinus_sq {s w : ℝ} (hw : 0 < w) :
    ‖kernelMinus s w‖ ^ 2 = Real.exp (-(2 * Real.pi * s)) * ‖kernelPlus s w‖ ^ 2 := by
  unfold kernelMinus kernelPlus
  rw [norm_mul, norm_mul, norm_cpow_plus hw, norm_cpow_minus hw]
  have h : Real.exp (-(Real.pi * s / 2)) ^ 2 =
      Real.exp (-(2 * Real.pi * s)) * Real.exp (Real.pi * s / 2) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [mul_pow, mul_pow, h]
  ring

/-- **The Planck law from the thermal ratio.**  If the occupation `b = |β|²` and `a = |α|²` satisfy
`a - b = 1` and `b = e^{-y} a` with `y > 0`, then `b = 1/(e^y - 1)`. -/
theorem planck_of_ratio {a b y : ℝ} (hy : 0 < y) (hab : a - b = 1) (hb : b = Real.exp (-y) * a) :
    b = 1 / (Real.exp y - 1) := by
  have h1 : y + 1 < Real.exp y := Real.add_one_lt_exp hy.ne'
  have hexp : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have ha : a = 1 + b := by linarith
  rw [ha] at hb
  have e : b * Real.exp y = Real.exp (-y) * (1 + b) * Real.exp y := by rw [← hb]
  have : b * (Real.exp y - 1) = 1 := by
    have e2 : Real.exp (-y) * (1 + b) * Real.exp y = 1 + b := by
      calc Real.exp (-y) * (1 + b) * Real.exp y = (Real.exp (-y) * Real.exp y) * (1 + b) := by ring
        _ = 1 + b := by rw [hexp, one_mul]
    linarith
  have hne : Real.exp y - 1 ≠ 0 := by linarith
  field_simp
  linarith

end

end Lightlike.GR.HawkingRadiation

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_068.kernelMinus := _root_.Lightlike.GR.HawkingRadiation.kernelMinus
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_068.kernelPlus := _root_.Lightlike.GR.HawkingRadiation.kernelPlus
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_068.norm_cpow_minus := _root_.Lightlike.GR.HawkingRadiation.norm_cpow_minus
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_068.norm_cpow_plus := _root_.Lightlike.GR.HawkingRadiation.norm_cpow_plus
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_068.norm_kernelMinus_sq := _root_.Lightlike.GR.HawkingRadiation.norm_kernelMinus_sq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_068.planck_of_ratio := _root_.Lightlike.GR.HawkingRadiation.planck_of_ratio
