import Lightlike.Asymptotics.AiryFunctions.HH
import Lightlike.Asymptotics.AiryFunctions.WKB

/-!
# WKB forms of the Hartle–Hawking and Vilenkin wave functions (row G2-019)

For `x > 0` the WKB (Liouville–Green) forms are
`ψ_HH^WKB = ψ₋/(2√π)` (decaying, the large-`x` form of `Ai`) and
`ψ_V^WKB = ψ₋/(2√π) + i ψ₊/√π` (decaying plus `i` times growing, the large-`x` form of `Ai + iBi`),
with `ψ_± = x^{-1/4} exp(± (2/3) x^{3/2})`.

We prove that they solve `ψ'' = (x + 5/(16x²)) ψ`, i.e. the Airy equation up to the relative
error `5/(16 x³) → 0`, and that their probability currents `Im(ψ̄ ψ')` are exactly those of
`hhWave` (`0`) and `vilenkinWave` (`1/π`).  The analytic statement `Ai ∼ ψ₋/(2√π)` is not
proved here.
-/

noncomputable section

namespace Lightlike.Airy

open Complex ComplexConjugate

/-- Decaying WKB amplitude `ψ₋/(2√π)`. -/
def hhWKB (x : ℝ) : ℝ := wkbAmp (-1) x / (2 * Real.sqrt Real.pi)

/-- Its derivative. -/
def hhWKBDeriv (x : ℝ) : ℝ := wkbDeriv (-1) x / (2 * Real.sqrt Real.pi)

/-- Growing WKB amplitude `ψ₊/√π`. -/
def growWKB (x : ℝ) : ℝ := wkbAmp 1 x / Real.sqrt Real.pi

/-- Its derivative. -/
def growWKBDeriv (x : ℝ) : ℝ := wkbDeriv 1 x / Real.sqrt Real.pi

/-- WKB form of the Vilenkin wave function. -/
def vilenkinWKB (x : ℝ) : ℂ := (hhWKB x : ℂ) + I * (growWKB x : ℂ)

/-- Derivative of the WKB form of the Vilenkin wave function. -/
def vilenkinWKBDeriv (x : ℝ) : ℂ := (hhWKBDeriv x : ℂ) + I * (growWKBDeriv x : ℂ)

/-- The residual of the WKB equation relative to the Airy potential `x`: `5/(16 x³) → 0`. -/
theorem wkb_relative_residual_tendsto :
    Filter.Tendsto (fun x : ℝ => (5 / (16 * x ^ 2)) / x) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun x : ℝ => x ^ 3) Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (by norm_num)
  have h2 := (h.const_mul_atTop (by norm_num : (0:ℝ) < 16)).inv_tendsto_atTop
  have h3 := h2.const_mul (5 : ℝ)
  simp only [mul_zero] at h3
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with x hx
  simp only [Pi.inv_apply]
  field_simp

theorem hhWKB_hasDerivAt {x : ℝ} (hx : 0 < x) : HasDerivAt hhWKB (hhWKBDeriv x) x :=
  (wkbAmp_hasDerivAt (-1) hx).div_const _ |>.congr_deriv (by unfold hhWKBDeriv wkbDeriv; ring)

theorem growWKB_hasDerivAt {x : ℝ} (hx : 0 < x) : HasDerivAt growWKB (growWKBDeriv x) x :=
  (wkbAmp_hasDerivAt 1 hx).div_const _ |>.congr_deriv (by unfold growWKBDeriv wkbDeriv; ring)

/-- The decaying WKB form solves `ψ'' = (x + 5/(16x²)) ψ`. -/
theorem hhWKBDeriv_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt hhWKBDeriv ((x + 5 / (16 * x ^ 2)) * hhWKB x) x :=
  ((wkbDeriv_hasDerivAt (by norm_num) hx).div_const (2 * Real.sqrt Real.pi)).congr_deriv
    (by unfold hhWKB; ring)

/-- The growing WKB form solves `ψ'' = (x + 5/(16x²)) ψ`. -/
theorem growWKBDeriv_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt growWKBDeriv ((x + 5 / (16 * x ^ 2)) * growWKB x) x :=
  ((wkbDeriv_hasDerivAt (by norm_num) hx).div_const (Real.sqrt Real.pi)).congr_deriv
    (by unfold growWKB; ring)

/-- The Vilenkin WKB form solves the same equation. -/
theorem vilenkinWKB_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt vilenkinWKB (vilenkinWKBDeriv x) x := by
  have h1 := (hhWKB_hasDerivAt hx).ofReal_comp
  have h2 := ((growWKB_hasDerivAt hx).ofReal_comp).const_mul I
  exact h1.add h2

theorem vilenkinWKBDeriv_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt vilenkinWKBDeriv (((x + 5 / (16 * x ^ 2) : ℝ) : ℂ) * vilenkinWKB x) x := by
  have h1 := (hhWKBDeriv_hasDerivAt hx).ofReal_comp
  have h2 := ((growWKBDeriv_hasDerivAt hx).ofReal_comp).const_mul I
  refine (h1.add h2).congr_deriv ?_
  unfold vilenkinWKB
  push_cast
  ring

/-- The Hartle–Hawking WKB form is real, so its current vanishes (as for `hhWave`). -/
theorem hhWKB_current (x : ℝ) :
    (conj ((hhWKB x : ℝ) : ℂ) * ((hhWKBDeriv x : ℝ) : ℂ)).im = 0 := by
  simp [Complex.mul_im]

/-- The current of the Vilenkin WKB form is `1/π`, equal to that of `vilenkinWave`
(`vilenkinWave_current`): the normalisations `Ai ∼ ψ₋/(2√π)`, `Bi ∼ ψ₊/√π` are
Wronskian-consistent. -/
theorem vilenkinWKB_current {x : ℝ} (hx : 0 < x) :
    (conj (vilenkinWKB x) * vilenkinWKBDeriv x).im = 1 / Real.pi := by
  have hw := wkb_wronskian hx
  have hpi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  simp only [vilenkinWKB, vilenkinWKBDeriv, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.I_re, Complex.I_im]
  unfold hhWKB hhWKBDeriv growWKB growWKBDeriv
  field_simp
  nlinarith [hw, hpi]

end Lightlike.Airy
