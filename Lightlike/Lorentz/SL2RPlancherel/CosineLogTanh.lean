import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.TanhSeries

/-!
# The cosine transform of `-log tanh (x/4)`

`∫_0^∞ cos (ρ x) (-log tanh (x/4)) dx = (π/(2ρ)) tanh (πρ)` for `ρ > 0`.

This is the Fourier side of the Abel kernel: by `abelKernel_eq_log_tanh` the kernel of the
Plancherel route is `K(t,s) = log (tanh ((s+t)/4) / tanh ((s-t)/4))`, a difference of two values of
`L(x) = -log tanh (|x|/4)`, and this theorem says that the Fourier transform of `L` is
`(π/ρ) tanh (πρ)`, which gives the density `ρ tanh (πρ)` after multiplying by `ρ²` (derivatives of
the Abel transform).  Proof: `-log tanh (x/4) = log (1+q) - log (1-q)` with `q = e^{-x/2}`, the
series `Real.hasSum_log_sub_log_of_abs_lt_one`, termwise `∫ cos (ρ x) e^{-a x} = a/(ρ²+a²)`,
`hasSum_tanh_series` at `2ρ`, and the interchange of sum and integral.
-/

namespace Lightlike.Lorentz.SL2RPlancherel

open MeasureTheory Set

private lemma re_neg_lt' (a : ℝ) (ha : 0 < a) (ρ : ℝ) :
    (-(a : ℂ) + ρ * Complex.I).re < 0 := by simp [ha]

private lemma integral_cexp' (a : ℝ) (ha : 0 < a) (ρ : ℝ) :
    ∫ t : ℝ in Ioi 0, Complex.exp ((-(a : ℂ) + ρ * Complex.I) * t) = 1 / (a - ρ * Complex.I) := by
  rw [integral_exp_mul_complex_Ioi (re_neg_lt' a ha ρ)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have : (a : ℂ) - ρ * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2 : -(a : ℂ) + ρ * Complex.I ≠ 0 := by
    intro h
    apply this
    linear_combination -h
  rw [div_eq_div_iff h2 this]
  ring

/-- Laplace transform of the cosine: `∫_{t>0} cos (ρ t) e^{-a t} = a/(ρ² + a²)` for `a > 0`. -/
theorem integral_cos_mul_exp (a : ℝ) (ha : 0 < a) (ρ : ℝ) :
    ∫ t : ℝ in Ioi 0, Real.cos (ρ * t) * Real.exp (-(a * t)) = a / (ρ ^ 2 + a ^ 2) := by
  have hint : IntegrableOn (fun t : ℝ => Complex.exp ((-(a : ℂ) + ρ * Complex.I) * t)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (re_neg_lt' a ha ρ) 0
  have hfun : ∀ t : ℝ, (Complex.exp ((-(a : ℂ) + ρ * Complex.I) * t)).re
      = Real.cos (ρ * t) * Real.exp (-(a * t)) := by
    intro t
    have : (-(a : ℂ) + ρ * Complex.I) * t = ((-(a * t) : ℝ) : ℂ) + ((ρ * t : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_add, ← Complex.ofReal_exp, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re, mul_comm]
  have h : ∫ t : ℝ in Ioi 0, (Complex.exp ((-(a : ℂ) + ρ * Complex.I) * t)).re
      = (∫ t : ℝ in Ioi 0, Complex.exp ((-(a : ℂ) + ρ * Complex.I) * t)).re := integral_re hint
  have h2 : ∫ t : ℝ in Ioi 0, Real.cos (ρ * t) * Real.exp (-(a * t))
      = ∫ t : ℝ in Ioi 0, (Complex.exp ((-(a : ℂ) + ρ * Complex.I) * t)).re := by
    congr 1; funext t; exact (hfun t).symm
  rw [h2, h, integral_cexp' a ha ρ]
  have : (1 : ℂ) / (a - ρ * Complex.I) = ((a : ℂ) + ρ * Complex.I) / ((ρ ^ 2 + a ^ 2 : ℝ) : ℂ) := by
    have hpos : ((ρ ^ 2 + a ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : (0:ℝ) < ρ ^ 2 + a ^ 2 := by positivity
      exact_mod_cast this.ne'
    have hne : (a : ℂ) - ρ * Complex.I ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    rw [div_eq_div_iff hne hpos]
    push_cast
    linear_combination ((ρ : ℂ) ^ 2) * Complex.I_sq
  rw [this, Complex.div_ofReal_re]
  simp

/-- The `m`-th term `cos (ρ x) · (2/(2m+1)) e^{-((2m+1)/2) x}`. -/
private noncomputable def cterm (ρ : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  Real.cos (ρ * x) * (2 / (2 * m + 1) * Real.exp (-(((2 * m + 1 : ℝ) / 2) * x)))

private lemma cterm_cont (ρ : ℝ) (m : ℕ) : Continuous (cterm ρ m) := by
  unfold cterm; fun_prop

private lemma cexp_integrable (m : ℕ) :
    IntegrableOn (fun x : ℝ => Real.exp (-(((2 * m + 1 : ℝ) / 2) * x))) (Ioi 0) := by
  have := exp_neg_integrableOn_Ioi (0 : ℝ) (b := ((2 * m + 1 : ℝ) / 2)) (by positivity)
  exact this.congr_fun (fun t _ => by simp only [neg_mul]) measurableSet_Ioi

private lemma cexp_integral (m : ℕ) :
    ∫ x : ℝ in Ioi 0, Real.exp (-(((2 * m + 1 : ℝ) / 2) * x)) = 2 / (2 * m + 1) := by
  have ha : (0:ℝ) < (2 * m + 1 : ℝ) / 2 := by positivity
  have h := integral_exp_mul_Ioi (a := -(((2 * m + 1 : ℝ) / 2))) (by linarith) 0
  simp only [neg_mul] at h ⊢
  rw [h]
  field_simp
  simp

private lemma cterm_integrable (ρ : ℝ) (m : ℕ) : IntegrableOn (cterm ρ m) (Ioi 0) := by
  refine Integrable.mono' ((cexp_integrable m).const_mul (2 / (2 * m + 1)))
    (cterm_cont ρ m).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  unfold cterm
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (by positivity : (0:ℝ) < 2 / (2 * m + 1))]
  have := Real.abs_cos_le_one (ρ * x)
  have hp : 0 < 2 / (2 * (m:ℝ) + 1) * Real.exp (-(((2 * m + 1 : ℝ) / 2) * x)) := by positivity
  nlinarith

private lemma norm_cterm_integral_le (ρ : ℝ) (m : ℕ) :
    ∫ x in Ioi (0:ℝ), ‖cterm ρ m x‖ ≤ 4 / (2 * m + 1) ^ 2 := by
  have hle : ∀ x ∈ Ioi (0:ℝ), ‖cterm ρ m x‖
      ≤ 2 / (2 * m + 1) * Real.exp (-(((2 * m + 1 : ℝ) / 2) * x)) := by
    intro x _
    unfold cterm
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < 2 / (2 * (m:ℝ) + 1) *
      Real.exp (-(((2 * m + 1 : ℝ) / 2) * x)))]
    have := Real.abs_cos_le_one (ρ * x)
    have hp : 0 < 2 / (2 * (m:ℝ) + 1) * Real.exp (-(((2 * m + 1 : ℝ) / 2) * x)) := by positivity
    nlinarith
  calc ∫ x in Ioi (0:ℝ), ‖cterm ρ m x‖
      ≤ ∫ x in Ioi (0:ℝ), 2 / (2 * m + 1) * Real.exp (-(((2 * m + 1 : ℝ) / 2) * x)) :=
        setIntegral_mono_on (cterm_integrable ρ m).norm ((cexp_integrable m).const_mul _)
          measurableSet_Ioi hle
    _ = 4 / (2 * m + 1) ^ 2 := by
        rw [integral_const_mul, cexp_integral]; field_simp; ring

/-- `-log tanh (x/4) = ∑ (2/(2m+1)) e^{-((2m+1)/2) x}` for `x > 0`. -/
private lemma hasSum_neg_log_tanh (x : ℝ) (hx : 0 < x) :
    HasSum (fun m : ℕ => 2 / (2 * m + 1) * Real.exp (-(((2 * m + 1 : ℝ) / 2) * x)))
      (-Real.log (Real.tanh (x / 4))) := by
  set q := Real.exp (-(x / 2)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hq, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := q) (by rw [abs_of_pos hq0]; exact hq1)
  have hT : Real.tanh (x / 4) = (1 - q) / (1 + q) := by
    set u := Real.exp (-(x / 4)) with hu
    have hu0 : 0 < u := Real.exp_pos _
    have e1 : q = u ^ 2 := by rw [hq, hu, ← Real.exp_nat_mul]; push_cast; ring_nf
    have e2 : Real.exp (x / 4) = 1 / u := by
      rw [hu, one_div, ← Real.exp_neg]; simp
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    have : Real.exp (-(x / 4)) = u := rfl
    rw [this, e2, e1]
    field_simp
  have hL : -Real.log (Real.tanh (x / 4)) = Real.log (1 + q) - Real.log (1 - q) := by
    rw [hT, Real.log_div (by linarith) (by linarith)]; ring
  rw [hL]
  convert h using 1
  funext m
  have : q ^ (2 * m + 1) = Real.exp (-(((2 * m + 1 : ℝ) / 2) * x)) := by
    rw [hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [this]; ring

/-- The cosine transform of `-log tanh (x/4)`:
`∫_{x>0} cos (ρ x) · (-log tanh (x/4)) = (π/(2ρ)) tanh (πρ)` for `ρ > 0`. -/
theorem integral_cos_mul_neg_log_tanh {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ x : ℝ in Ioi 0, Real.cos (ρ * x) * (-Real.log (Real.tanh (x / 4)))
      = Real.pi / (2 * ρ) * Real.tanh (Real.pi * ρ) := by
  have hsum : Summable fun m : ℕ => ∫ x in Ioi (0:ℝ), ‖cterm ρ m x‖ := by
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun t => norm_nonneg _)
      (norm_cterm_integral_le ρ) ?_
    have : Summable fun m : ℕ => 4 * (1 / ((m:ℝ) + 1) ^ 2) := by
      refine Summable.mul_left _ ?_
      have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
      simpa using this
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) this
    have : (0:ℝ) < (m:ℝ) + 1 := by positivity
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (m:ℝ), Nat.cast_nonneg (α := ℝ) m]
  have h := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun m t => cterm ρ m t) (fun m => cterm_integrable ρ m) hsum
  have hval : ∀ m : ℕ, ∫ x in Ioi (0:ℝ), cterm ρ m x = 1 / (ρ ^ 2 + ((2 * m + 1 : ℝ) / 2) ^ 2) := by
    intro m
    unfold cterm
    simp_rw [← mul_assoc, mul_comm _ (2 / (2 * (m:ℝ) + 1)), mul_assoc]
    rw [integral_const_mul, integral_cos_mul_exp _ (by positivity)]
    field_simp
  have hT := (hasSum_tanh_series (ρ := 2 * ρ) (by linarith)).mul_left (2 / ρ)
  have h2 : (∫ x in Ioi (0:ℝ), ∑' m, cterm ρ m x)
      = 2 / ρ * (Real.pi / 4 * Real.tanh (Real.pi * (2 * ρ) / 2)) := by
    refine h.unique ?_
    convert hT using 1
    funext m
    rw [hval]
    have hr : (0:ℝ) < (2 * m + 1 : ℝ) := by positivity
    field_simp
  have h3 : ∀ x ∈ Ioi (0:ℝ), ∑' m, cterm ρ m x
      = Real.cos (ρ * x) * (-Real.log (Real.tanh (x / 4))) := by
    intro x hx
    have hg := hasSum_neg_log_tanh x hx
    unfold cterm
    rw [tsum_mul_left, hg.tsum_eq]
  rw [setIntegral_congr_fun measurableSet_Ioi h3] at h2
  rw [h2]
  have : Real.pi * (2 * ρ) / 2 = Real.pi * ρ := by ring
  rw [this]
  field_simp
  ring

/-- `-log tanh (x/4)` is integrable on `(0, ∞)`: a logarithmic singularity at `0`, exponential
decay at `∞`.  Proof: it is the sum of the series `∑ (2/(2m+1)) e^{-((2m+1)/2) x}` whose terms have
integrals `4/(2m+1)²`, summable. -/
theorem integrableOn_neg_log_tanh :
    IntegrableOn (fun x : ℝ => -Real.log (Real.tanh (x / 4))) (Ioi 0) := by
  set F : ℕ → ℝ → ℝ := fun m x =>
    2 / (2 * m + 1) * Real.exp (-(((2 * m + 1 : ℝ) / 2) * x)) with hF
  have hFnn : ∀ m x, 0 ≤ F m x := fun m x => by simp only [hF]; positivity
  have hFint : ∀ m, IntegrableOn (F m) (Ioi 0) := fun m => (cexp_integrable m).const_mul _
  have hFval : ∀ m : ℕ, ∫ x in Ioi (0:ℝ), F m x = 4 / (2 * (m:ℝ) + 1) ^ 2 := by
    intro m
    simp only [hF]
    rw [integral_const_mul, cexp_integral]
    field_simp
    ring
  have hsum : Summable fun m : ℕ => 4 / (2 * (m:ℝ) + 1) ^ 2 := by
    have : Summable fun m : ℕ => 4 * (1 / ((m:ℝ) + 1) ^ 2) := by
      refine Summable.mul_left _ ?_
      have := (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
      simpa using this
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) this
    have : (0:ℝ) < (m:ℝ) + 1 := by positivity
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (m:ℝ), Nat.cast_nonneg (α := ℝ) m]
  have hmeas : Measurable (fun x : ℝ => -Real.log (Real.tanh (x / 4))) :=
    (Real.measurable_log.comp (by
      simp only [Real.tanh_eq_sinh_div_cosh]
      exact (Real.continuous_sinh.measurable.comp (measurable_id.div_const 4)).div
        (Real.continuous_cosh.measurable.comp (measurable_id.div_const 4)))).neg
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] fun x : ℝ => -Real.log (Real.tanh (x / 4)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hasSum_neg_log_tanh x hx).nonneg (fun m => hFnn m x)
  refine (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable hnn).mp ?_
  have h1 : ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (-Real.log (Real.tanh (x / 4)))
      = ∑' m, ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (F m x) := by
    rw [← lintegral_tsum (fun m => (hFint m).1.aemeasurable.ennreal_ofReal)]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hg := hasSum_neg_log_tanh x hx
    rw [← hg.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun m => hFnn m x) hg.summable]
  rw [h1]
  have h2 : ∀ m : ℕ, ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (F m x)
      = ENNReal.ofReal (4 / (2 * (m:ℝ) + 1) ^ 2) := by
    intro m
    rw [← hFval m, ofReal_integral_eq_lintegral_ofReal (hFint m)
      (Filter.Eventually.of_forall (hFnn m))]
  simp only [h2]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

end Lightlike.Lorentz.SL2RPlancherel
