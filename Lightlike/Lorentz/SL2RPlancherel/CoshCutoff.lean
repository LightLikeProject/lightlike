import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.CoshApprox

/-!
# Compactly supported approximation by functions of `cosh t`

For a smooth even `h` supported in `[-T₀, T₀]`, the polynomial approximation of
`CoshApprox.lean` is cut off by a bump function in the variable `v = cosh t`.  The result is
`P ∘ cosh`, with `P` smooth with compact support, such that `h - P ∘ cosh` is supported in a fixed
interval `[-T, T]` and is bounded, together with its derivative, by `C ε`, where `T, C` do not
depend on `ε` (`exists_cosh_cutoff_approx`).  This is a step in the surjectivity of the spherical
Plancherel isometry for `SL(2,ℝ)` (milestone HA3): it gives `L²` approximation of `h` and `h'`
by the functions `P ∘ cosh`, which are in the range of the Abel transform.
-/

open Set Real Polynomial Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- A real polynomial is smooth. -/
theorem contDiff_polynomial_eval (q : ℝ[X]) : ContDiff ℝ ∞ (fun v : ℝ => q.eval v) := by
  simp only [Polynomial.eval_eq_sum_range]
  exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_id.pow i)

/-- **Cutoff approximation by `P ∘ cosh`**: a smooth even `h`, vanishing for `|t| > T₀`, is
approximated by `P ∘ cosh` with `P` smooth of compact support.  The error `h - P ∘ cosh` vanishes
for `|t| > T` and is bounded, with its derivative, by `C ε`; `T` and `C` do not depend on `ε`. -/
theorem exists_cosh_cutoff_approx (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (he : ∀ t, h (-t) = h t)
    (T0 : ℝ) (hs : ∀ t, T0 < |t| → h t = 0) :
    ∃ T C : ℝ, 0 ≤ T ∧ 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∃ P : ℝ → ℝ, ContDiff ℝ ∞ P ∧
      HasCompactSupport P ∧ ∀ t : ℝ, (T < |t| → h t - P (Real.cosh t) = 0) ∧
        |h t - P (Real.cosh t)| ≤ C * ε ∧
        |deriv h t - deriv (fun s => P (Real.cosh s)) t| ≤ C * ε := by
  set V : ℝ := Real.cosh T0 with hV
  have hV1 : 1 ≤ V := Real.one_le_cosh T0
  let X : ContDiffBump (0 : ℝ) := ⟨V + 1, V + 2, by linarith, by linarith⟩
  have hXc : ContDiff ℝ ∞ X := X.contDiff
  have hXs : HasCompactSupport X := X.hasCompactSupport
  obtain ⟨B, hB⟩ := (hXc.continuous_deriv (by simp)).bounded_above_of_compact_support hXs.deriv
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set T : ℝ := Real.arcosh (V + 2) with hT
  have hcT : Real.cosh T = V + 2 := Real.cosh_arcosh (by linarith)
  have hT0le : 0 ≤ T := Real.arcosh_nonneg (by linarith)
  set S : ℝ := Real.sinh T with hS
  have hS0 : 0 ≤ S := Real.sinh_nonneg_iff.2 hT0le
  have hT0T : T0 < |T| := by
    have : Real.cosh T0 < Real.cosh T := by rw [hcT]; linarith
    have h2 := Real.cosh_lt_cosh.1 this
    exact lt_of_le_of_lt (le_abs_self T0) h2
  refine ⟨T, 1 + B * S, hT0le, by positivity, fun ε hε => ?_⟩
  obtain ⟨q, hq⟩ := exists_poly_cosh_approx h hh he T ε hT0le hε
  have hqc := contDiff_polynomial_eval q
  refine ⟨fun v => q.eval v * X v, hqc.mul hXc, ?_, fun t => ?_⟩
  · exact HasCompactSupport.mul_left (f := fun v : ℝ => q.eval v) (f' := X) hXs
  -- the function `s ↦ q (cosh s)` and its derivative
  have hG : ∀ x, DifferentiableAt ℝ (fun s => q.eval (Real.cosh s)) x := fun x =>
    ((q.hasDerivAt (Real.cosh x)).comp x (Real.hasDerivAt_cosh x)).differentiableAt
  have hXd : ∀ x, HasDerivAt (fun s => X (Real.cosh s)) (deriv X (Real.cosh x) * Real.sinh x) x :=
    fun x => ((hXc.differentiable (by simp)) (Real.cosh x)).hasDerivAt.comp x
      (Real.hasDerivAt_cosh x)
  have hdP : ∀ x, deriv (fun s => q.eval (Real.cosh s) * X (Real.cosh s)) x =
      deriv (fun s => q.eval (Real.cosh s)) x * X (Real.cosh x) +
        q.eval (Real.cosh x) * (deriv X (Real.cosh x) * Real.sinh x) := fun x =>
    ((hG x).hasDerivAt.mul (hXd x)).deriv
  have hXzero : ∀ s : ℝ, T ≤ |s| → X (Real.cosh s) = 0 := by
    intro s hs'
    apply X.zero_of_le_dist
    have : Real.cosh T ≤ Real.cosh s := Real.cosh_le_cosh.2 (by rwa [abs_of_nonneg hT0le])
    rw [Real.dist_eq, sub_zero, abs_of_pos (Real.cosh_pos s)]
    show V + 2 ≤ _
    linarith
  have hhzero : ∀ s : ℝ, T < |s| → h s = 0 := fun s hs' => hs s (lt_trans hT0T (by
    rw [abs_of_nonneg hT0le]; exact hs'))
  beta_reduce
  by_cases hout : T < |t|
  · have h1 : h t - q.eval (Real.cosh t) * X (Real.cosh t) = 0 := by
      rw [hhzero t hout, hXzero t hout.le]; simp
    have hev : ∀ᶠ s in 𝓝 t, T < |s| := (isOpen_lt continuous_const continuous_abs).mem_nhds hout
    have h2 : deriv h t = 0 := by
      have : h =ᶠ[𝓝 t] fun _ => (0 : ℝ) := hev.mono fun s hs' => hhzero s hs'
      rw [this.deriv_eq]; simp
    have h3 : deriv (fun s => q.eval (Real.cosh s) * X (Real.cosh s)) t = 0 := by
      have : (fun s => q.eval (Real.cosh s) * X (Real.cosh s)) =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
        hev.mono fun s hs' => by simp [hXzero s hs'.le]
      rw [this.deriv_eq]; simp
    refine ⟨fun _ => h1, ?_, ?_⟩
    · simp only [h1, abs_zero]; positivity
    · simp only [h2, h3, sub_zero, abs_zero]; positivity
  · push Not at hout
    have ht : t ∈ Icc (-T) T := abs_le.1 hout
    obtain ⟨hq1, hq2⟩ := hq t ht
    have hC : ε ≤ (1 + B * S) * ε := by nlinarith [mul_nonneg hB0 hS0]
    refine ⟨fun h' => absurd h' (not_lt.2 hout), ?_⟩
    by_cases hin : |t| ≤ T0
    · have hcb : Real.cosh t < V + 1 := by
        have := Real.cosh_le_cosh.2 (show |t| ≤ |T0| from hin.trans (le_abs_self T0))
        rw [hV]; linarith
      have hev : ∀ᶠ s in 𝓝 t, X (Real.cosh s) = 1 :=
        (Real.continuous_cosh.tendsto t).eventually
          (X.eventuallyEq_one_of_mem_ball (by
            rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos t)]
            exact hcb)) |>.mono fun s hs' => by simpa using hs'
      have hX1 : X (Real.cosh t) = 1 := by simpa using hev.self_of_nhds
      have hd : deriv (fun s => q.eval (Real.cosh s) * X (Real.cosh s)) t =
          deriv (fun s => q.eval (Real.cosh s)) t := by
        have : (fun s => q.eval (Real.cosh s) * X (Real.cosh s)) =ᶠ[𝓝 t]
            fun s => q.eval (Real.cosh s) := hev.mono fun s hs' => by simp [hs']
        rw [this.deriv_eq]
      rw [hX1, mul_one, hd]
      constructor
      · rw [abs_sub_comm]; exact hq1.trans hC
      · rw [abs_sub_comm]; exact hq2.trans hC
    · push Not at hin
      have hh0 : h t = 0 := hs t hin
      have hevh : ∀ᶠ s in 𝓝 t, T0 < |s| :=
        (isOpen_lt continuous_const continuous_abs).mem_nhds hin
      have hdh : deriv h t = 0 := by
        have : h =ᶠ[𝓝 t] fun _ => (0 : ℝ) := hevh.mono fun s hs' => hs s hs'
        rw [this.deriv_eq]; simp
      rw [hh0] at hq1
      rw [hdh] at hq2
      have hX0 : 0 ≤ X (Real.cosh t) := X.nonneg
      have hX1 : X (Real.cosh t) ≤ 1 := X.le_one
      have hsinh : |Real.sinh t| ≤ S := by
        rw [Real.abs_sinh, hS]; exact Real.sinh_le_sinh.2 (by simpa using hout)
      have hq1' : |q.eval (Real.cosh t)| ≤ ε := by simpa using hq1
      have hq2' : |deriv (fun s => q.eval (Real.cosh s)) t| ≤ ε := by simpa using hq2
      have hXd' : |deriv X (Real.cosh t)| ≤ B := by simpa using hB (Real.cosh t)
      constructor
      · rw [hh0, zero_sub, abs_neg, abs_mul, abs_of_nonneg hX0]
        calc |q.eval (Real.cosh t)| * X (Real.cosh t) ≤ ε * 1 :=
              mul_le_mul hq1' hX1 hX0 hε.le
          _ ≤ _ := by linarith
      · rw [hdh, hdP, zero_sub, abs_neg]
        have e1 : |deriv (fun s => q.eval (Real.cosh s)) t * X (Real.cosh t)| ≤ ε := by
          rw [abs_mul, abs_of_nonneg hX0]
          calc _ ≤ ε * 1 := mul_le_mul hq2' hX1 hX0 hε.le
            _ = ε := mul_one ε
        have e2 : |q.eval (Real.cosh t) * (deriv X (Real.cosh t) * Real.sinh t)| ≤ ε * (B * S) := by
          rw [abs_mul, abs_mul]
          exact mul_le_mul hq1' (mul_le_mul hXd' hsinh (abs_nonneg _) hB0) (by positivity)
            hε.le
        calc _ ≤ _ := abs_add_le _ _
          _ ≤ ε + ε * (B * S) := add_le_add e1 e2
          _ = (1 + B * S) * ε := by ring

end Lightlike.Lorentz.SL2RPlancherel
