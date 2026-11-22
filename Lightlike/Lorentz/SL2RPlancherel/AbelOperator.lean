module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.AbelHalfIntegral
public import Lightlike.Lorentz.SL2RPlancherel.AbelCompose
public import Lightlike.Lorentz.SL2RPlancherel.AbelDeriv

/-!
# The half-order Abel operator and its square

`halfAbel f v = ∫_{w > 0} w^{-1/2} f (v + w) dw`. The Abel transform of the hyperbolic plane is
`√2` times `halfAbel` at `cosh t`, and for a `C¹` function of compact support
`halfAbel (halfAbel f') = -π f`. This is the Abel inversion used in the SL(2,ℝ) Plancherel formula
with density `ρ tanh(πρ)` (milestone HA3).
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The half-order Abel operator `v ↦ ∫_{w > 0} w^{-1/2} f (v + w) dw`. -/
def halfAbel (f : ℝ → ℂ) (v : ℝ) : ℂ :=
  ∫ w in Ioi (0 : ℝ), (w ^ (-(1 / 2 : ℝ)) : ℝ) • f (v + w)

/-- `halfAbel f v = ∫_{a > v} f a / √(a - v) da`. -/
theorem halfAbel_eq (f : ℝ → ℂ) (v : ℝ) :
    halfAbel f v = ∫ a in Ioi v, f a / ((√(a - v) : ℝ) : ℂ) := by
  unfold halfAbel
  rw [← integral_Ioi_add_left (fun a => f a / ((√(a - v) : ℝ) : ℂ)) v]
  refine setIntegral_congr_fun measurableSet_Ioi (fun w hw => ?_)
  have hw' : 0 < w := hw
  simp only [add_sub_cancel_left, Real.rpow_neg hw'.le, Real.sqrt_eq_rpow, Complex.real_smul,
    div_eq_inv_mul]
  push_cast
  rfl

/-- `𝒜F(t) = √2 · halfAbel F (cosh t)`. -/
theorem abelTransform_eq_halfAbel (F : ℝ → ℂ) (t : ℝ) :
    abelTransform F t = (√2 : ℂ) * halfAbel F (Real.cosh t) := by
  rw [abelTransform_eq, halfAbel_eq]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  rw [Complex.real_smul, div_eq_inv_mul]
  push_cast
  rfl

/-- Two half-order Abel operators compose to `π` times the tail integral. -/
theorem halfAbel_halfAbel (F : ℝ → ℂ) (hF : Measurable F) (hI : Integrable F) (v : ℝ) :
    halfAbel (halfAbel F) v = (π : ℂ) * ∫ a in Ioi v, F a := by
  rw [halfAbel_eq]
  simp only [halfAbel_eq]
  exact Lightlike.Lorentz.SL2R.integral_halfAbel_comp F hF hI v

/-- **Abel inversion for the half-order operator**: for `f` of class `C¹` with compact support,
`halfAbel (halfAbel f') = -π f`. -/
theorem halfAbel_halfAbel_deriv (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (v : ℝ) : halfAbel (halfAbel (deriv f)) v = -(π : ℂ) * f v := by
  have hd'cont : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hI : Integrable (deriv f) := hd'cont.integrable_of_hasCompactSupport hc.deriv
  rw [halfAbel_halfAbel _ hd'cont.measurable hI]
  have htend : Filter.Tendsto f Filter.atTop (nhds 0) := by
    obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop R] with x hx
    symm
    refine image_eq_zero_of_notMem_tsupport (fun h => ?_)
    have := hR h
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    have := le_abs_self x
    linarith
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => (hdiff x).hasDerivAt) hI.integrableOn
    htend]
  ring

end Lightlike.Lorentz.SL2RPlancherel
