import Mathlib
import Lightlike.Lorentz.SL2ROddPlancherel.OddAssembly
import Lightlike.Lorentz.SL2ROddPlancherel.OddMehler

/-!
# The odd Plancherel identity for the weight-`(1,1)` block

For `F` smooth with compact support and `ĥ(ρ) = ∫ e^{iρt} 2cosh(t/2) 𝒜G(t) dt`, `G(v) = F(v)/√(2(1+|v|))`
(`oddTransform F`),

  `π² ∫_{v>1} ‖F(v)‖² dv = ¼ ∫_{ρ>0} ρ coth(πρ) ‖ĥ(ρ)‖² dρ`   (`odd_plancherel`).

The function `G` is not smooth at `v = -1`; the Abel transform only sees the values at `v ≥ 1`, so it is replaced
by `F · oddW` with a smooth cutoff `oddW` that equals `(2(1+v))^{-1/2}` for `v ≥ 0` and vanishes for `v ≤ -1/2`.
The identity for the smooth function is `odd_plancherel_G`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2ROddPlancherel

open Lightlike.Lorentz.SL2RPlancherel

/-- The smooth cutoff `oddW(v) = smoothTransition(2v + 1) / √(2(1 + v))`: it is `(2(1 + v))^{-1/2}` for `v ≥ 0` and
`0` for `v ≤ -1/2`. -/
def oddW (v : ℝ) : ℝ := Real.smoothTransition (2 * v + 1) * (Real.sqrt (2 * (1 + v)))⁻¹

lemma contDiff_oddW : ContDiff ℝ ∞ oddW := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : -1 < v
  · have h1 : ContDiffAt ℝ ∞ (fun v : ℝ => Real.smoothTransition (2 * v + 1)) v :=
      (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)).contDiffAt
    have h0 : ContDiffAt ℝ ∞ (fun v : ℝ => 2 * (1 + v)) v :=
      (contDiff_const.mul (contDiff_const.add contDiff_id)).contDiffAt
    have hne : 2 * (1 + v) ≠ 0 := by linarith
    have h2 : ContDiffAt ℝ ∞ (fun v : ℝ => Real.sqrt (2 * (1 + v))) v := h0.sqrt hne
    have hne2 : Real.sqrt (2 * (1 + v)) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    exact h1.mul (h2.inv hne2)
  · have : oddW =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds (show v < -1 / 2 by linarith)] with y hy
      simp only [oddW]
      rw [Real.smoothTransition.zero_of_nonpos (by simp only [mem_Iio] at hy; linarith), zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq this

lemma oddW_of_nonneg {v : ℝ} (hv : 0 ≤ v) : oddW v = (Real.sqrt (2 * (1 + v)))⁻¹ := by
  simp only [oddW]
  rw [Real.smoothTransition.one_of_one_le (by linarith), one_mul]

/-- The smooth function `F · oddW` has the same Abel transform as `oddG F` (the Abel transform only uses the values
of the function on `[1, ∞)`). -/
lemma abelTransform_oddW (F : ℝ → ℂ) :
    abelTransform (fun v => F v * (oddW v : ℂ)) = abelTransform (oddG F) := by
  funext t
  unfold abelTransform
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  have hv : 1 ≤ Real.cosh t + w ^ 2 / 2 := by linarith [Real.one_le_cosh t, sq_nonneg w]
  simp only [oddG]
  rw [oddW_of_nonneg (by linarith), abs_of_nonneg (by linarith), Complex.ofReal_inv]

lemma norm_sq_oddW {F : ℝ → ℂ} {v : ℝ} (hv : 0 ≤ v) :
    (1 + v) * ‖F v * (oddW v : ℂ)‖ ^ 2 = (1 / 2 : ℝ) * ‖F v‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, oddW_of_nonneg hv, inv_pow,
    Real.sq_sqrt (by linarith)]
  have : (0 : ℝ) < 1 + v := by linarith
  field_simp

/-- `∫ e^{iρt} 2cosh(t/2) g(t) dt = a(ρ - i/2) + a(ρ + i/2)`. -/
lemma integral_two_cosh_half {g : ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g) (ρ : ℝ) :
    ∫ t : ℝ, Complex.exp (ρ * t * I) * (((2 * Real.cosh (t / 2) : ℝ) : ℂ) * g t) =
      ftC g ((ρ : ℂ) - I / 2) + ftC g ((ρ : ℂ) + I / 2) := by
  unfold ftC
  rw [← integral_add (integrable_exp_mul hg hc _) (integrable_exp_mul hg hc _)]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have e1 : ((ρ : ℂ) - I / 2) * t * I = ρ * t * I + ((t / 2 : ℝ) : ℂ) := by
    push_cast; linear_combination (-(t : ℂ) / 2) * Complex.I_mul_I
  have e2 : ((ρ : ℂ) + I / 2) * t * I = ρ * t * I + ((-(t / 2) : ℝ) : ℂ) := by
    push_cast; linear_combination ((t : ℂ) / 2) * Complex.I_mul_I
  beta_reduce
  rw [e1, e2, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, ← Complex.ofReal_exp,
    Real.cosh_eq]
  push_cast
  ring_nf

/-- **The odd Plancherel identity for the weight-`(1,1)` block.** -/
theorem odd_plancherel {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    Real.pi ^ 2 * ∫ v in Ioi (1 : ℝ), ‖F v‖ ^ 2 =
      (1 / 4 : ℝ) * ∫ ρ in Ioi (0 : ℝ), ρ * (Real.cosh (Real.pi * ρ) / Real.sinh (Real.pi * ρ)) *
        ‖oddTransform F ρ‖ ^ 2 := by
  have hG : ContDiff ℝ ∞ (fun v => F v * (oddW v : ℂ)) :=
    hF.mul (Complex.ofRealCLM.contDiff.comp contDiff_oddW)
  have hGc : HasCompactSupport (fun v => F v * (oddW v : ℂ)) := hc.mul_right
  have h := odd_plancherel_G hG hGc
  have hT : ∀ ρ : ℝ, oddTransform F ρ = oddHat (abelTransform fun v => F v * (oddW v : ℂ)) ρ := by
    intro ρ
    rw [abelTransform_oddW]
    unfold oddTransform oddAbel oddHat
    have hg := contDiff_abelTransform (fun v => F v * (oddW v : ℂ)) hG hGc
    have hgc := hasCompactSupport_abelTransform (fun v => F v * (oddW v : ℂ)) hGc
    rw [abelTransform_oddW] at hg hgc
    exact integral_two_cosh_half hg.continuous hgc ρ
  simp_rw [hT]
  have hint : ∫ v in Ioi (1 : ℝ), (1 + v) * ‖F v * (oddW v : ℂ)‖ ^ 2 =
      (1 / 2 : ℝ) * ∫ v in Ioi (1 : ℝ), ‖F v‖ ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun v hv => norm_sq_oddW (by simp only [mem_Ioi] at hv; linarith)
  rw [hint] at h
  linear_combination h

end Lightlike.Lorentz.SL2ROddPlancherel
