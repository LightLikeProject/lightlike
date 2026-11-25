import Lightlike.Asymptotics.AiryContourIntegral.Basic

/-!
# Differentiation of the Airy moments (row G2-020)

`airyMoment α n z = ∫ (u + iα)^n exp(i((u+iα)³/3 + z (u+iα))) du`.  We show it is complex
differentiable in `z` with derivative `i · airyMoment α (n+1) z`.
-/

namespace Lightlike.Rows.G2_020

open Complex MeasureTheory Metric

/-- The `n`-th moment of the Airy integrand on the line `Im t = α`. -/
noncomputable def airyMoment (α : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, ((u : ℂ) + α * I) ^ n * airyIntegrand α z u

/-- Derivative of the integrand in `z`. -/
lemma hasDerivAt_airyIntegrand (α : ℝ) (n : ℕ) (u : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => ((u : ℂ) + α * I) ^ n * airyIntegrand α w u)
      (I * (((u : ℂ) + α * I) ^ (n + 1) * airyIntegrand α z u)) z := by
  set t : ℂ := (u : ℂ) + α * I with ht
  have h1 : HasDerivAt (fun w : ℂ => airyPhase w t) (I * t) z := by
    unfold airyPhase
    have := ((hasDerivAt_id z).mul_const t).add_const (t ^ 3 / 3) |>.const_mul I
    convert this using 1
    · ext w; simp; ring
    · simp
  have h2 := (h1.cexp).const_mul (t ^ n)
  have : airyIntegrand α z u = Complex.exp (airyPhase z t) := rfl
  exact h2.congr_deriv (by rw [this, pow_succ]; ring)

/-- Uniform Gaussian bound for the derivative on the unit ball. -/
lemma norm_deriv_airyIntegrand_le {α : ℝ} (hα : 0 < α) (n : ℕ) (z0 z : ℂ) (hz : z ∈ ball z0 1)
    (u : ℝ) :
    ‖I * (((u : ℂ) + α * I) ^ (n + 1) * airyIntegrand α z u)‖ ≤
      ((n + 1).factorial * Real.exp α * Real.exp (α ^ 3 / 3 - α * z0.re + α) *
        Real.exp ((|z0.im| + 2) ^ 2 / (2 * α))) * Real.exp (-(α / 2) * u ^ 2) := by
  rw [norm_mul, Complex.norm_I, one_mul]
  refine (norm_pow_airyIntegrand_le hα (n + 1) z u).trans ?_
  have hd : ‖z - z0‖ < 1 := by simpa [dist_eq_norm] using hz
  have hre : |z.re - z0.re| ≤ 1 := (Complex.abs_re_le_norm _).trans (by simpa using hd.le)
  have him : |z.im - z0.im| ≤ 1 := (Complex.abs_im_le_norm _).trans (by simpa using hd.le)
  have h1 : -α * z.re ≤ -α * z0.re + α := by
    have := (abs_le.mp hre).1
    nlinarith
  have h2 : |z.im| + 1 ≤ |z0.im| + 2 := by
    have : |z.im| ≤ |z0.im| + |z.im - z0.im| := by
      calc |z.im| = |z0.im + (z.im - z0.im)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith
  have h3 : Real.exp (α ^ 3 / 3 - α * z.re) ≤ Real.exp (α ^ 3 / 3 - α * z0.re + α) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4 : Real.exp ((|z.im| + 1) ^ 2 / (2 * α)) ≤ Real.exp ((|z0.im| + 2) ^ 2 / (2 * α)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (by positivity) h2 2
  gcongr

/-- The moments are complex differentiable in `z`, with derivative `i` times the next moment. -/
lemma hasDerivAt_airyMoment {α : ℝ} (hα : 0 < α) (n : ℕ) (z : ℂ) :
    HasDerivAt (airyMoment α n) (I * airyMoment α (n + 1) z) z := by
  have hmeas : ∀ m : ℕ, ∀ w : ℂ, AEStronglyMeasurable
      (fun u : ℝ => ((u : ℂ) + α * I) ^ m * airyIntegrand α w u) volume := fun m w =>
    (integrable_pow_airyIntegrand hα m w).aestronglyMeasurable
  have hF' : AEStronglyMeasurable
      (fun u : ℝ => I * (((u : ℂ) + α * I) ^ (n + 1) * airyIntegrand α z u)) volume :=
    (integrable_pow_airyIntegrand hα (n + 1) z).aestronglyMeasurable.const_mul I
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (w : ℂ) (u : ℝ) => ((u : ℂ) + α * I) ^ n * airyIntegrand α w u)
    (F' := fun (w : ℂ) (u : ℝ) => I * (((u : ℂ) + α * I) ^ (n + 1) * airyIntegrand α w u))
    (x₀ := z) (s := ball z 1) (μ := volume)
    (bound := fun u => ((n + 1).factorial * Real.exp α * Real.exp (α ^ 3 / 3 - α * z.re + α) *
        Real.exp ((|z.im| + 2) ^ 2 / (2 * α))) * Real.exp (-(α / 2) * u ^ 2))
    (ball_mem_nhds z one_pos) (Filter.Eventually.of_forall (hmeas n))
    (integrable_pow_airyIntegrand hα n z) hF'
    (Filter.Eventually.of_forall fun u w hw => norm_deriv_airyIntegrand_le hα n z w hw u)
    ((integrable_exp_neg_mul_sq (by positivity : 0 < α / 2)).const_mul _)
    (Filter.Eventually.of_forall fun u w _ => hasDerivAt_airyIntegrand α n u w)
  have := key.2
  unfold airyMoment
  rw [integral_const_mul] at this
  exact this

end Lightlike.Rows.G2_020
