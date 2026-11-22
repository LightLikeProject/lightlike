module

public import Mathlib
public import Lightlike.Lorentz.SL2R
public import Lightlike.Lorentz.SL2RPlancherel.CoshDist
public import Lightlike.Lorentz.SL2RPlancherel.UpperHalfPlaneIntegral
public import Lightlike.Lorentz.SL2RPlancherel.UpperHalfPlaneSubstitution
public import Lightlike.Lorentz.SL2RPlancherel.RadialIntegral

/-!
# The radial integral formula for the Haar measure of `SL(2,ℝ)`

For measurable `Φ : ℝ → [0,∞]`,
`∫_{SL(2,ℝ)} Φ(cosh d(g)) dg = 4π² ∫_{t>1} Φ(t) dt`
where `cosh d(g) = (a² + b² + c² + d²)/2` (`coshDistR`) and `dg` is `haarR`.  Substituting
`t = cosh r` this reads `4π² ∫_0^∞ Φ(cosh r) sinh r dr`, the polar form of the Haar measure
used for the spherical Plancherel formula.  Milestone HA3.
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- **Radial integral formula**: for measurable `Φ : ℝ → [0,∞]`,
`∫ Φ(coshDistR g) d haarR = 2π · 2π · ∫_{t>1} Φ(t) dt`. -/
lemma lintegral_coshDistR {Φ : ℝ → ENNReal} (hΦ : Measurable Φ) :
    ∫⁻ g, Φ (coshDistR g) ∂haarR =
      (2 * ENNReal.ofReal π) * (2 * ENNReal.ofReal π) * ∫⁻ t in Ioi (1 : ℝ), Φ t := by
  have hF : Measurable fun g => Φ (coshDistR g) := hΦ.comp continuous_coshDistR.measurable
  rw [lintegral_haarR hF]
  have h1 : ∀ z : UpperHalfPlane,
      ∫⁻ θ in Ioc 0 (2 * π), Φ (coshDistR (z.toSL2R * rot θ)) =
        Φ ((z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im)) * (2 * ENNReal.ofReal π) := by
    intro z
    have : ∀ θ, coshDistR (z.toSL2R * rot θ) = (z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im) := fun θ =>
      coshDistR_iwasawa (z, θ)
    simp only [this, setLIntegral_const, Real.volume_Ioc]
    rw [sub_zero, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  simp only [h1]
  have hG : Measurable fun z : UpperHalfPlane =>
      Φ ((z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im)) := by fun_prop
  rw [lintegral_mul_const _ hG, lintegral_upperHalfPlane_prod hG]
  have h2 : ∫⁻ y in Ioi (0 : ℝ), ∫⁻ x : ℝ,
      Φ (((UpperHalfPlane.ofComplex ⟨x, y⟩ : UpperHalfPlane).re ^ 2 +
        (UpperHalfPlane.ofComplex ⟨x, y⟩ : UpperHalfPlane).im ^ 2 + 1) /
        (2 * (UpperHalfPlane.ofComplex ⟨x, y⟩ : UpperHalfPlane).im)) *
        ENNReal.ofReal (1 / y ^ 2) =
      ∫⁻ y in Ioi (0 : ℝ), ∫⁻ x : ℝ,
        Φ ((x ^ 2 + y ^ 2 + 1) / (2 * y)) * ENNReal.ofReal (1 / y ^ 2) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    refine lintegral_congr fun x => ?_
    have hy' : (0 : ℝ) < y := hy
    have := UpperHalfPlane.ofComplex_apply_of_im_pos (z := (⟨x, y⟩ : ℂ)) hy'
    simp [this]
  rw [h2, lintegral_radial_step hΦ, lintegral_radial_cosh hΦ]
  ring

end Lightlike.Lorentz.SL2R
