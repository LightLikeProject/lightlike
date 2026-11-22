module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.AbelOperator

/-!
# The derivative of the Abel transform

For `F` of class `C¹` with compact support, the Abel transform `g = 𝒜F` of the hyperbolic plane
satisfies `g'(t) = √2 · sinh t · halfAbel F' (cosh t)`. This is the first step of the Plancherel
identity for SL(2,ℝ) with density `ρ tanh(πρ)` (milestone HA3).
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `halfAbel f` has derivative `halfAbel (deriv f)` for `f` of class `C¹` with compact support. -/
theorem hasDerivAt_halfAbel' (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (x : ℝ) : HasDerivAt (halfAbel f) (halfAbel (deriv f) x) x :=
  Lightlike.Lorentz.SL2R.hasDerivAt_halfAbel f hf hc x

/-- **Derivative of the Abel transform**: for `F` of class `C¹` with compact support,
`(𝒜F)'(t) = √2 · sinh t · halfAbel F' (cosh t)`. -/
theorem hasDerivAt_abelTransform (F : ℝ → ℂ) (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F)
    (t : ℝ) :
    HasDerivAt (abelTransform F)
      ((√2 : ℂ) * (Real.sinh t : ℂ) * halfAbel (deriv F) (Real.cosh t)) t := by
  have h1 := hasDerivAt_halfAbel' F hF hc (Real.cosh t)
  have h2 : HasDerivAt (fun s : ℝ => Real.cosh s) (Real.sinh t) t := Real.hasDerivAt_cosh t
  have h3 := (h1.scomp t h2).const_mul (√2 : ℂ)
  have hfun : abelTransform F = fun s => (√2 : ℂ) * (halfAbel F ∘ Real.cosh) s := by
    funext s
    exact abelTransform_eq_halfAbel F s
  rw [hfun]
  convert h3 using 1
  rw [Complex.real_smul]
  ring

end Lightlike.Lorentz.SL2RPlancherel
