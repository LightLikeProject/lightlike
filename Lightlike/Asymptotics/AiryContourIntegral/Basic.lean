import Mathlib

/-!
# Airy integrand on a horizontal line (row G2-020)

For `α > 0` and `z : ℂ` the Airy function is the absolutely convergent contour integral
`Ai z = (1/2π) ∫ exp(i (t³/3 + z t)) dt` along the line `t = u + iα`.  This file defines the
integrand, computes its modulus, and gives the Gaussian domination used for every
differentiation under the integral sign in the later files.
-/

namespace Lightlike.Asymptotics.AiryContourIntegral

open Complex MeasureTheory

/-- The phase `i (t³/3 + z t)` of the Airy integral. -/
noncomputable def airyPhase (z t : ℂ) : ℂ := I * (t ^ 3 / 3 + z * t)

/-- The Airy integrand `exp (i (t³/3 + z t))` on the line `t = u + i α`. -/
noncomputable def airyIntegrand (α : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (airyPhase z ((u : ℂ) + α * I))

lemma re_airyPhase (α : ℝ) (z : ℂ) (u : ℝ) :
    (airyPhase z ((u : ℂ) + α * I)).re = -α * u ^ 2 + α ^ 3 / 3 - α * z.re - z.im * u := by
  simp [airyPhase, pow_succ, Complex.mul_re, Complex.mul_im]
  ring

/-- The modulus of the Airy integrand. -/
lemma norm_airyIntegrand (α : ℝ) (z : ℂ) (u : ℝ) :
    ‖airyIntegrand α z u‖ = Real.exp (-α * u ^ 2 + α ^ 3 / 3 - α * z.re - z.im * u) := by
  rw [airyIntegrand, Complex.norm_exp, re_airyPhase]

/-- Gaussian domination: `exp (-α u² + d |u|) ≤ exp (d² / (2α)) exp (-(α/2) u²)`. -/
lemma exp_gauss_le {α : ℝ} (hα : 0 < α) (d u : ℝ) :
    Real.exp (-α * u ^ 2 + d * |u|) ≤ Real.exp (d ^ 2 / (2 * α)) * Real.exp (-(α / 2) * u ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h : d * |u| ≤ α * u ^ 2 / 2 + d ^ 2 / (2 * α) := by
    have h1 : 0 ≤ (α * |u| - d) ^ 2 := sq_nonneg _
    have h2 : |u| ^ 2 = u ^ 2 := sq_abs u
    rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
    have h3 : α ^ 2 * |u| ^ 2 = α ^ 2 * u ^ 2 := by rw [h2]
    nlinarith [h1, h3]
  nlinarith [h]

lemma continuous_airyIntegrand (α : ℝ) (z : ℂ) : Continuous (airyIntegrand α z) := by
  unfold airyIntegrand airyPhase
  fun_prop

/-- Pointwise bound on the weighted integrand by a Gaussian. -/
lemma norm_pow_airyIntegrand_le {α : ℝ} (hα : 0 < α) (n : ℕ) (z : ℂ) (u : ℝ) :
    ‖((u : ℂ) + α * I) ^ n * airyIntegrand α z u‖ ≤
      (n.factorial * Real.exp α * Real.exp (α ^ 3 / 3 - α * z.re) *
        Real.exp ((|z.im| + 1) ^ 2 / (2 * α))) * Real.exp (-(α / 2) * u ^ 2) := by
  have ht : ‖(u : ℂ) + α * I‖ ≤ |u| + α := by
    calc ‖(u : ℂ) + α * I‖ ≤ ‖(u : ℂ)‖ + ‖(α : ℂ) * I‖ := norm_add_le _ _
      _ = |u| + α := by simp [abs_of_pos hα]
  have hp : ‖(u : ℂ) + α * I‖ ^ n ≤ n.factorial * Real.exp (|u| + α) := by
    have h1 : ‖(u : ℂ) + α * I‖ ^ n ≤ (|u| + α) ^ n := pow_le_pow_left₀ (norm_nonneg _) ht n
    have h2 := Real.pow_div_factorial_le_exp (|u| + α) (by positivity) n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    rw [div_le_iff₀ hf] at h2
    linarith
  rw [norm_mul, norm_pow, norm_airyIntegrand]
  have hE : Real.exp (-α * u ^ 2 + α ^ 3 / 3 - α * z.re - z.im * u) ≤
      Real.exp (α ^ 3 / 3 - α * z.re) * Real.exp (-α * u ^ 2 + (|z.im| + 1) * |u| - |u|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h' : -(z.im * u) ≤ |z.im| * |u| := by
      rw [← abs_mul]; exact neg_le_abs _
    nlinarith [h', abs_nonneg u]
  have hG := exp_gauss_le hα (|z.im| + 1) u
  have key : Real.exp (|u| + α) * Real.exp (-α * u ^ 2 + (|z.im| + 1) * |u| - |u|) =
      Real.exp α * Real.exp (-α * u ^ 2 + (|z.im| + 1) * |u|) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hf : (0 : ℝ) ≤ n.factorial := by positivity
  calc ‖(u : ℂ) + α * I‖ ^ n * Real.exp (-α * u ^ 2 + α ^ 3 / 3 - α * z.re - z.im * u)
      ≤ (n.factorial * Real.exp (|u| + α)) *
          (Real.exp (α ^ 3 / 3 - α * z.re) *
            Real.exp (-α * u ^ 2 + (|z.im| + 1) * |u| - |u|)) :=
        mul_le_mul hp hE (Real.exp_pos _).le (by positivity)
    _ = n.factorial * Real.exp α * Real.exp (α ^ 3 / 3 - α * z.re) *
          Real.exp (-α * u ^ 2 + (|z.im| + 1) * |u|) := by
        linear_combination (n.factorial : ℝ) * Real.exp (α ^ 3 / 3 - α * z.re) * key
    _ ≤ n.factorial * Real.exp α * Real.exp (α ^ 3 / 3 - α * z.re) *
          (Real.exp ((|z.im| + 1) ^ 2 / (2 * α)) * Real.exp (-(α / 2) * u ^ 2)) := by
        gcongr
    _ = _ := by ring

/-- The weighted Airy integrand is integrable on each horizontal line `Im t = α > 0`. -/
lemma integrable_pow_airyIntegrand {α : ℝ} (hα : 0 < α) (n : ℕ) (z : ℂ) :
    Integrable fun u : ℝ => ((u : ℂ) + α * I) ^ n * airyIntegrand α z u := by
  refine Integrable.mono' ((integrable_exp_neg_mul_sq (by positivity : 0 < α / 2)).const_mul _)
    ?_ (Filter.Eventually.of_forall (norm_pow_airyIntegrand_le hα n z))
  have := continuous_airyIntegrand α z
  exact (by fun_prop : Continuous fun u : ℝ => ((u : ℂ) + α * I) ^ n).mul this |>.aestronglyMeasurable

end Lightlike.Asymptotics.AiryContourIntegral

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_020.airyIntegrand := _root_.Lightlike.Asymptotics.AiryContourIntegral.airyIntegrand
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_020.airyPhase := _root_.Lightlike.Asymptotics.AiryContourIntegral.airyPhase
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_020.continuous_airyIntegrand := _root_.Lightlike.Asymptotics.AiryContourIntegral.continuous_airyIntegrand
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_020.exp_gauss_le := _root_.Lightlike.Asymptotics.AiryContourIntegral.exp_gauss_le
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_020.integrable_pow_airyIntegrand := _root_.Lightlike.Asymptotics.AiryContourIntegral.integrable_pow_airyIntegrand
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_020.norm_airyIntegrand := _root_.Lightlike.Asymptotics.AiryContourIntegral.norm_airyIntegrand
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_020.norm_pow_airyIntegrand_le := _root_.Lightlike.Asymptotics.AiryContourIntegral.norm_pow_airyIntegrand_le
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_020.re_airyPhase := _root_.Lightlike.Asymptotics.AiryContourIntegral.re_airyPhase
