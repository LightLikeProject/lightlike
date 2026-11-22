import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.AbelTruncation

/-!
# The Abel transform of a test function is an even Schwartz function

For `F` smooth with compact support, `halfAbel F` is smooth (it is differentiated under the integral
sign, `halfAbel F' = (halfAbel F)'`), vanishes to the right of the support of `F`, and the Abel
transform `𝒜F (t) = √2 · halfAbel F (cosh t)` of the hyperbolic plane is therefore an even
compactly supported smooth function, i.e. an even Schwartz function.  This puts `𝒜F` in the scope
of `integral_logTanhKernel_deriv_quadrant` (milestone HA3, density `ρ tanh(πρ)`).
-/

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `halfAbel F` is `C^n` for every finite `n`, when `F` is smooth with compact support. -/
theorem contDiff_halfAbel_nat (n : ℕ) :
    ∀ F : ℝ → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F → ContDiff ℝ n (halfAbel F) := by
  induction n with
  | zero =>
    intro F hF hc
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_halfAbel F (hF.of_le (by norm_num)) hc
  | succ n ih =>
    intro F hF hc
    have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_halfAbel' F hF1 hc x).differentiableAt,
      fun h => absurd h (by simp), ?_⟩
    have : deriv (halfAbel F) = halfAbel (deriv F) :=
      funext fun x => (hasDerivAt_halfAbel' F hF1 hc x).deriv
    rw [this]
    exact ih (deriv F) (contDiff_infty_iff_deriv.1 hF).2 hc.deriv

/-- `halfAbel F` is smooth for `F` smooth with compact support. -/
theorem contDiff_halfAbel (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ContDiff ℝ ∞ (halfAbel F) :=
  contDiff_infty.2 fun n => contDiff_halfAbel_nat n F hF hc

/-- `halfAbel F a = 0` to the right of the support of `F`. -/
theorem halfAbel_eq_zero_of_support {F : ℝ → ℂ} {R : ℝ} (hR : ∀ x : ℝ, R ≤ ‖x‖ → F x = 0)
    {a : ℝ} (ha : R ≤ a) : halfAbel F a = 0 := by
  unfold halfAbel
  have : ∀ w ∈ Ioi (0 : ℝ), (w ^ (-(1 / 2 : ℝ)) : ℝ) • F (a + w) = 0 := by
    intro w hw
    have hw' : (0 : ℝ) < w := hw
    have : R ≤ ‖a + w‖ := by
      rw [Real.norm_eq_abs]
      exact le_trans (by linarith) (le_abs_self _)
    simp [hR _ this]
  rw [setIntegral_congr_fun measurableSet_Ioi this]
  simp

/-- The Abel transform of a smooth compactly supported function is smooth. -/
theorem contDiff_abelTransform (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ContDiff ℝ ∞ (abelTransform F) := by
  have hfun : abelTransform F = fun s => (√2 : ℂ) * (halfAbel F ∘ Real.cosh) s := by
    funext s
    exact abelTransform_eq_halfAbel F s
  rw [hfun]
  exact contDiff_const.mul ((contDiff_halfAbel F hF hc).comp Real.contDiff_cosh)

/-- The Abel transform of a compactly supported function is compactly supported. -/
theorem hasCompactSupport_abelTransform (F : ℝ → ℂ) (hc : HasCompactSupport F) :
    HasCompactSupport (abelTransform F) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hF0 : ∀ x : ℝ, R + 1 ≤ ‖x‖ → F x = 0 := by
    intro x hx
    by_contra hne
    have := hR (subset_tsupport _ hne)
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  set R' : ℝ := |R + 1| with hR'
  have hcosh : R + 1 ≤ Real.cosh R' := by
    have h1 : R + 1 ≤ R' := le_abs_self _
    have h2 : R' ≤ Real.sinh R' := Real.self_le_sinh_iff.2 (abs_nonneg _)
    have h3 := Real.sinh_lt_cosh R'
    linarith
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R') (fun t ht => ?_)
  have ht' : R' < |t| := by
    simpa [Metric.mem_closedBall, dist_zero_right] using ht
  have h1 : Real.cosh R' ≤ Real.cosh t := Real.cosh_le_cosh.2 (by rw [abs_abs]; exact ht'.le)
  rw [abelTransform_eq_halfAbel, halfAbel_eq_zero_of_support hF0 (by linarith)]
  simp

/-- The Abel transform of a smooth compactly supported function is even. -/
theorem abelTransform_neg (F : ℝ → ℂ) (t : ℝ) : abelTransform F (-t) = abelTransform F t := by
  rw [abelTransform_eq_halfAbel, abelTransform_eq_halfAbel, Real.cosh_neg]

/-- **The Abel transform as an even Schwartz function**, for `F` smooth with compact support. -/
def abelSchwartz (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    SchwartzMap ℝ ℂ :=
  (hasCompactSupport_abelTransform F hc).toSchwartzMap (contDiff_abelTransform F hF hc)

theorem abelSchwartz_apply (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    (abelSchwartz F hF hc : ℝ → ℂ) = abelTransform F := rfl

end Lightlike.Lorentz.SL2RPlancherel
