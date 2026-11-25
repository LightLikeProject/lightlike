import Lightlike.Asymptotics.AiryContourIntegral.Calculus

/-!
# The Airy equation for the contour integral (row G2-020)

`∫ (t² + z) exp(i(t³/3 + z t)) du = 0` on every line `Im t = α > 0` (the integral of the
`u`-derivative of the integrand), hence `Ai'' = z Ai` for `Ai z = (1/2π) airyMoment α 0 z`.
-/

namespace Lightlike.Rows.G2_020

open Complex MeasureTheory Filter Topology

/-- `u`-derivative of the Airy integrand. -/
lemma hasDerivAt_airyIntegrand_u (α : ℝ) (z : ℂ) (u : ℝ) :
    HasDerivAt (airyIntegrand α z)
      (I * ((((u : ℂ) + α * I) ^ 2 + z) * airyIntegrand α z u)) u := by
  set t : ℂ := (u : ℂ) + α * I with ht
  have h1 : HasDerivAt (fun w : ℂ => airyPhase z (w + α * I)) (I * (t ^ 2 + z)) (u : ℂ) := by
    unfold airyPhase
    have hw : HasDerivAt (fun w : ℂ => w + α * I) 1 (u : ℂ) := (hasDerivAt_id _).add_const _
    have h3 : HasDerivAt (fun w : ℂ => (w + α * I) ^ 3 / 3 + z * (w + α * I))
        (3 * t ^ 2 * 1 / 3 + z * 1) (u : ℂ) :=
      ((hw.pow 3).div_const 3).add (hw.const_mul z) |>.congr_deriv (by simp [ht])
    have := h3.const_mul I
    refine this.congr_deriv ?_
    ring
  have h2 := (h1.cexp).comp_ofReal
  refine h2.congr_deriv ?_
  show _ = _
  simp only [airyIntegrand, ht]
  ring

/-- The integrand tends to zero along any filter on which `u²` tends to `+∞`. -/
lemma tendsto_airyIntegrand_zero {α : ℝ} (hα : 0 < α) (z : ℂ) {l : Filter ℝ}
    (hl : Tendsto (fun u : ℝ => u ^ 2) l atTop) :
    Tendsto (airyIntegrand α z) l (𝓝 0) := by
  have hg : Tendsto (fun u : ℝ => Real.exp (-(α / 2) * u ^ 2)) l (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => (α / 2) * u ^ 2) l atTop :=
      hl.const_mul_atTop (by positivity)
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    refine this.congr (fun u => ?_)
    simp only [Function.comp]
    congr 1; ring
  have hg' := hg.const_mul ((((0 : ℕ).factorial : ℝ) * Real.exp α *
    Real.exp (α ^ 3 / 3 - α * z.re) * Real.exp ((|z.im| + 1) ^ 2 / (2 * α))))
  rw [mul_zero] at hg'
  refine squeeze_zero_norm (fun u => ?_) hg'
  have := norm_pow_airyIntegrand_le hα 0 z u
  simpa using this

/-- The Airy equation in integral form: `∫ (t² + z) E = 0`, i.e. `M₂ + z M₀ = 0`. -/
lemma airyMoment_two_add {α : ℝ} (hα : 0 < α) (z : ℂ) :
    airyMoment α 2 z + z * airyMoment α 0 z = 0 := by
  have hint : Integrable fun u : ℝ =>
      I * ((((u : ℂ) + α * I) ^ 2 + z) * airyIntegrand α z u) := by
    have h2 := integrable_pow_airyIntegrand hα 2 z
    have h0 := (integrable_pow_airyIntegrand hα 0 z).const_mul z
    simp only [pow_zero, one_mul] at h0
    refine (h2.add h0).const_mul I |>.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [Pi.add_apply]
    ring
  have key := integral_of_hasDerivAt_of_tendsto (f := airyIntegrand α z)
    (f' := fun u : ℝ => I * ((((u : ℂ) + α * I) ^ 2 + z) * airyIntegrand α z u))
    (hasDerivAt_airyIntegrand_u α z) hint
    (tendsto_airyIntegrand_zero hα z (by
      have : Tendsto (fun u : ℝ => |u|) atBot atTop := tendsto_abs_atBot_atTop
      refine ((tendsto_pow_atTop (n := 2) (by norm_num)).comp this).congr (fun u => ?_)
      simp [sq_abs]))
    (tendsto_airyIntegrand_zero hα z (tendsto_pow_atTop (by norm_num)))
  have h2 := integrable_pow_airyIntegrand hα 2 z
  have h0 := (integrable_pow_airyIntegrand hα 0 z).const_mul z
  simp only [pow_zero, one_mul] at h0
  have : ∫ u : ℝ, I * ((((u : ℂ) + α * I) ^ 2 + z) * airyIntegrand α z u) =
      I * (airyMoment α 2 z + z * airyMoment α 0 z) := by
    have e : ∀ u : ℝ, (((u : ℂ) + α * I) ^ 2 + z) * airyIntegrand α z u =
        ((u : ℂ) + α * I) ^ 2 * airyIntegrand α z u + z * airyIntegrand α z u := fun u => by ring
    simp_rw [e]
    rw [integral_const_mul, integral_add h2 h0, integral_const_mul]
    simp [airyMoment]
  rw [this] at key
  simp only [sub_zero] at key
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h Complex.I_ne_zero
  · exact h

/-- The Airy function computed on the line `Im t = α`: `(1/2π) ∫ exp(i(t³/3 + z t)) du`.
(Independence of `α > 0` is proved separately.) -/
noncomputable def airyAiLine (α : ℝ) (z : ℂ) : ℂ := airyMoment α 0 z / (2 * Real.pi)

/-- Its derivative in `z`, as an integral: `(i/2π) ∫ t E du`. -/
noncomputable def airyAiLineDeriv (α : ℝ) (z : ℂ) : ℂ := I * airyMoment α 1 z / (2 * Real.pi)

lemma hasDerivAt_airyAiLine {α : ℝ} (hα : 0 < α) (z : ℂ) :
    HasDerivAt (airyAiLine α) (airyAiLineDeriv α z) z := by
  have := (hasDerivAt_airyMoment hα 0 z).div_const (2 * (Real.pi : ℂ))
  unfold airyAiLine airyAiLineDeriv
  simpa using this

/-- `Ai'' = z Ai`, on the line representation. -/
lemma hasDerivAt_airyAiLineDeriv {α : ℝ} (hα : 0 < α) (z : ℂ) :
    HasDerivAt (airyAiLineDeriv α) (z * airyAiLine α z) z := by
  have h := ((hasDerivAt_airyMoment hα 1 z).const_mul I).div_const (2 * (Real.pi : ℂ))
  have hz := airyMoment_two_add hα z
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  unfold airyAiLineDeriv
  refine h.congr_deriv ?_
  unfold airyAiLine
  have : airyMoment α 2 z = -(z * airyMoment α 0 z) := by linear_combination hz
  rw [this]
  field_simp
  ring_nf
  simp

end Lightlike.Rows.G2_020
