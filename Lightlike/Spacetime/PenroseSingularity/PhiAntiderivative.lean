import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The correction function `φ` (G1-012, step D4)

A smooth function `b` on an open interval has a smooth antiderivative; `φ t = c - ∫_t^e (b/2 + κ)` has derivative
`b t / 2 + κ`, vanishes at the right end when `c = 0`, and has the prescribed value `φ a` at the left end when
`c` is chosen accordingly.
-/

open Set Filter Topology intervalIntegral MeasureTheory

namespace Lightlike.Penrose

/-- The antiderivative of a smooth function on all of `ℝ`: `F t = ∫₀^t f` is smooth with `F' = f`. -/
theorem contDiff_integral_of_contDiff {f : ℝ → ℝ} {k : ℕ∞} (hf : ContDiff ℝ k f) :
    ContDiff ℝ (k + 1) (fun t => ∫ x in (0 : ℝ)..t, f x) := by
  have hd : ∀ t, HasDerivAt (fun t => ∫ x in (0 : ℝ)..t, f x) (f t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hf.continuous.intervalIntegrable _ _)
      (hf.continuous.stronglyMeasurableAtFilter _ _) hf.continuous.continuousAt
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun t => (hd t).differentiableAt, by simp, ?_⟩
  have : deriv (fun t => ∫ x in (0 : ℝ)..t, f x) = f := funext fun t => (hd t).deriv
  rw [this]; exact hf

end Lightlike.Penrose
