module

public import Mathlib

/-!
# The kernel of the Abel-transform norm

For `1 ≤ a < b`,
`∫_1^a dv/√((a-v)(b-v)) = 2 log ((√(a-1) + √(b-1))/√(b-a))`.
Antiderivative: `v ↦ -2 log (√(a-v) + √(b-v))`.  This is step (B) of the Plancherel route for
`SL(2,ℝ)`: the norm `‖F‖²` is a double integral of `g' ⊗ g'` against this kernel.
-/

@[expose] public section

namespace Lightlike.Lorentz.SL2RPlancherel

open MeasureTheory Set

/-- The antiderivative `v ↦ -2 log (√(a-v) + √(b-v))`. -/
noncomputable def abelKernelPrim (a b v : ℝ) : ℝ :=
  -2 * Real.log (Real.sqrt (a - v) + Real.sqrt (b - v))

/-- The integrand `1/√((a-v)(b-v))`, written as `(√(a-v) √(b-v))⁻¹`. -/
noncomputable def abelKernelIntegrand (a b v : ℝ) : ℝ :=
  (Real.sqrt (a - v) * Real.sqrt (b - v))⁻¹

lemma hasDerivAt_abelKernelPrim {a b v : ℝ} (ha : v < a) (hb : v < b) :
    HasDerivAt (abelKernelPrim a b) (abelKernelIntegrand a b v) v := by
  have h1 : 0 < a - v := by linarith
  have h2 : 0 < b - v := by linarith
  have s1 : 0 < Real.sqrt (a - v) := Real.sqrt_pos.2 h1
  have s2 : 0 < Real.sqrt (b - v) := Real.sqrt_pos.2 h2
  have d1 : HasDerivAt (fun v => Real.sqrt (a - v)) (-(1 : ℝ) / (2 * Real.sqrt (a - v))) v := by
    have := ((hasDerivAt_id v).const_sub a).sqrt h1.ne'
    simpa using this
  have d2 : HasDerivAt (fun v => Real.sqrt (b - v)) (-(1 : ℝ) / (2 * Real.sqrt (b - v))) v := by
    have := ((hasDerivAt_id v).const_sub b).sqrt h2.ne'
    simpa using this
  have d3 := ((d1.add d2).log (by simp only [Pi.add_apply]; positivity)).const_mul (-2)
  simp only [Pi.add_apply] at d3
  unfold abelKernelPrim abelKernelIntegrand
  convert d3 using 1
  generalize Real.sqrt (a - v) = x at *
  generalize Real.sqrt (b - v) = y at *
  field_simp
  ring

lemma continuousOn_abelKernelPrim {a b c : ℝ} (hab : a < b) :
    ContinuousOn (abelKernelPrim a b) (Icc c a) := by
  unfold abelKernelPrim
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.log (by fun_prop)
  intro v hv
  have : 0 < Real.sqrt (b - v) := Real.sqrt_pos.2 (by linarith [hv.2])
  positivity

/-- **The kernel integral.** For `1 ≤ a < b`,
`∫_1^a dv/√((a-v)(b-v)) = 2 log (√(a-1)+√(b-1)) - 2 log √(b-a)`. -/
theorem integral_abelKernel {a b : ℝ} (h1 : 1 ≤ a) (hab : a < b) :
    ∫ v in (1 : ℝ)..a, abelKernelIntegrand a b v =
      2 * Real.log (Real.sqrt (a - 1) + Real.sqrt (b - 1)) - 2 * Real.log (Real.sqrt (b - a)) := by
  rcases h1.eq_or_lt with rfl | h1'
  · simp
  have hc := continuousOn_abelKernelPrim (c := 1) hab
  have hd : ∀ x ∈ Ioo (1 : ℝ) a, HasDerivAt (abelKernelPrim a b) (abelKernelIntegrand a b x) x :=
    fun x hx => hasDerivAt_abelKernelPrim hx.2 (by linarith [hx.2])
  have hnn : ∀ x ∈ Ioo (1 : ℝ) a, 0 ≤ abelKernelIntegrand a b x := by
    intro x _
    unfold abelKernelIntegrand; positivity
  have hint : IntervalIntegrable (abelKernelIntegrand a b) volume 1 a :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h1'.le).2
      (intervalIntegral.integrableOn_deriv_of_nonneg hc hd hnn)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h1'.le hc hd hint]
  unfold abelKernelPrim
  simp only [sub_self, Real.sqrt_zero, zero_add]
  ring

end Lightlike.Lorentz.SL2RPlancherel
