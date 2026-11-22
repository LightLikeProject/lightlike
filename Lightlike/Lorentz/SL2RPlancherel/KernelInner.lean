module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.AbelTruncation
public import Lightlike.Lorentz.SL2RPlancherel.AbelKernel

/-!
# The inner `v`-integral of the Abel slices is the Abel kernel

For `φ ψ : ℝ → ℂ` and all real `a b`,
`∫_{v > 1} (φ a / √(a - v)) (ψ b / √(b - v)) dv = φ a ψ b ∫_{1}^{min a b} dv / √((a-v)(b-v))`
(`integral_abelSlice_mul`): the integrand vanishes for `v ≥ min a b` because `√` of a nonpositive
number is `0` in Lean.  For `1 ≤ a < b` the kernel is evaluated by `integral_abelKernel`
(`integral_abelSlice_mul_of_lt`).  This is step (ii)(a) of the Plancherel route for `SL(2,ℝ)`
(milestone HA3, density `ρ tanh(πρ)`).
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

lemma abelSlice_mul_eq (φ ψ : ℝ → ℂ) (a b v : ℝ) :
    abelSlice φ v a * abelSlice ψ v b = φ a * ψ b * ((abelKernelIntegrand a b v : ℝ) : ℂ) := by
  unfold abelSlice abelKernelIntegrand
  rw [mul_inv]
  push_cast
  ring

lemma abelKernelIntegrand_eq_zero {a b v : ℝ} (h : min a b ≤ v) : abelKernelIntegrand a b v = 0 := by
  unfold abelKernelIntegrand
  rcases min_le_iff.1 h with h | h
  · rw [Real.sqrt_eq_zero_of_nonpos (by linarith)]
    simp
  · rw [Real.sqrt_eq_zero_of_nonpos (by linarith : b - v ≤ 0)]
    simp

/-- The inner `v`-integral of a product of two Abel slices. -/
theorem integral_abelSlice_mul (φ ψ : ℝ → ℂ) (a b : ℝ) :
    ∫ v in Ioi (1 : ℝ), abelSlice φ v a * abelSlice ψ v b =
      φ a * ψ b * ((∫ v in Ioc (1 : ℝ) (min a b), abelKernelIntegrand a b v : ℝ) : ℂ) := by
  simp only [abelSlice_mul_eq]
  have : ∫ v in Ioi (1 : ℝ), φ a * ψ b * ((abelKernelIntegrand a b v : ℝ) : ℂ) =
      ∫ v in Ioc (1 : ℝ) (min a b), φ a * ψ b * ((abelKernelIntegrand a b v : ℝ) : ℂ) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self ?_
    intro v hv
    have : min a b ≤ v := by
      by_contra hc
      exact hv.2 ⟨hv.1, (not_le.1 hc).le⟩
    simp [abelKernelIntegrand_eq_zero this]
  rw [this, integral_const_mul, integral_complex_ofReal]

/-- For `1 ≤ a < b` the kernel of `integral_abelSlice_mul` is `2 log (√(a-1)+√(b-1)) - 2 log √(b-a)`. -/
theorem integral_abelSlice_mul_of_lt (φ ψ : ℝ → ℂ) {a b : ℝ} (h1 : 1 ≤ a) (hab : a < b) :
    ∫ v in Ioi (1 : ℝ), abelSlice φ v a * abelSlice ψ v b =
      φ a * ψ b * ((2 * Real.log (Real.sqrt (a - 1) + Real.sqrt (b - 1)) -
        2 * Real.log (Real.sqrt (b - a)) : ℝ) : ℂ) := by
  rw [integral_abelSlice_mul, min_eq_left hab.le, ← intervalIntegral.integral_of_le h1,
    integral_abelKernel h1 hab]

end Lightlike.Lorentz.SL2RPlancherel
