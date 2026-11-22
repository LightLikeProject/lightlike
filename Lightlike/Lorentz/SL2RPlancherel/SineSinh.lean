import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.SineExp
import Lightlike.Lorentz.SL2RPlancherel.TanhSeries

/-!
# The sine transform of `1/sinh`

`∫_0^∞ sin (ρ t)/sinh t dt = (π/2) tanh (πρ/2)` for `ρ ≥ 0`.  Proof: `1/sinh t = 2 ∑ e^{-(2m+1)t}`
for `t > 0`, termwise `∫ sin (ρ t) e^{-a t} = ρ/(ρ²+a²)` (`integral_sin_mul_exp`), the sum
`hasSum_tanh_series`, and the interchange of sum and integral
(`hasSum_integral_of_summable_integral_norm`, dominated by `ρ t e^{-a t}`).
This is the step (C) of the Plancherel route: it produces the `tanh` of the density `ρ tanh (πρ)`.
-/

namespace Lightlike.Lorentz.SL2RPlancherel

open MeasureTheory Set

/-- The `m`-th term `2 sin (ρ t) e^{-(2m+1) t}`. -/
private noncomputable def term (ρ : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  2 * (Real.sin (ρ * t) * Real.exp (-((2 * m + 1 : ℝ) * t)))

private lemma term_cont (ρ : ℝ) (m : ℕ) : Continuous (term ρ m) := by
  unfold term; fun_prop

private lemma exp_integrable (m : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-((2 * m + 1 : ℝ) * t))) (Ioi 0) := by
  have := exp_neg_integrableOn_Ioi (0 : ℝ) (b := (2 * m + 1 : ℝ)) (by positivity)
  exact this.congr_fun (fun t _ => by simp only [neg_mul]) measurableSet_Ioi

private lemma term_integrable (ρ : ℝ) (m : ℕ) : IntegrableOn (term ρ m) (Ioi 0) := by
  refine Integrable.mono' ((exp_integrable m).const_mul 2) (term_cont ρ m).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  unfold term
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_two]
  have := Real.abs_sin_le_one (ρ * t)
  have hp := Real.exp_pos (-((2 * m + 1 : ℝ) * t))
  nlinarith

/-- `∫_{t>0} t e^{-a t} = 1/a²`. -/
private lemma integral_t_exp (a : ℝ) (ha : 0 < a) :
    ∫ t : ℝ in Ioi 0, t * Real.exp (-(a * t)) = 1 / a ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := a) (by norm_num) ha
  have e : ∀ t : ℝ, t ^ ((2:ℝ) - 1) = t := fun t => by norm_num
  simp_rw [e] at h
  rw [h, Real.Gamma_two]
  rw [Real.rpow_two, one_div, inv_pow]
  simp

private lemma t_exp_integrable (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(a * t))) (Ioi 0) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := a) (by norm_num) ha
  have e : ∀ t : ℝ, t ^ ((2:ℝ) - 1) = t := fun t => by norm_num
  simp_rw [e] at h
  refine Integrable.of_integral_ne_zero ?_
  rw [h, Real.Gamma_two]
  have : (0:ℝ) < (1 / a) ^ (2:ℝ) * 1 := by positivity
  exact this.ne'

private lemma norm_term_integral_le (ρ : ℝ) (hρ : 0 ≤ ρ) (m : ℕ) :
    ∫ t in Ioi (0:ℝ), ‖term ρ m t‖ ≤ 2 * ρ / (2 * m + 1) ^ 2 := by
  have ha : (0:ℝ) < 2 * m + 1 := by positivity
  have hle : ∀ t ∈ Ioi (0:ℝ), ‖term ρ m t‖ ≤ 2 * ρ * (t * Real.exp (-((2 * m + 1 : ℝ) * t))) := by
    intro t ht
    have ht : 0 < t := ht
    unfold term
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_two]
    have h1 : |Real.sin (ρ * t)| ≤ |ρ * t| := Real.abs_sin_le_abs
    rw [abs_of_nonneg (by positivity : 0 ≤ ρ * t)] at h1
    have hp := Real.exp_pos (-((2 * m + 1 : ℝ) * t))
    nlinarith [mul_le_mul_of_nonneg_right h1 hp.le]
  calc ∫ t in Ioi (0:ℝ), ‖term ρ m t‖
      ≤ ∫ t in Ioi (0:ℝ), 2 * ρ * (t * Real.exp (-((2 * m + 1 : ℝ) * t))) :=
        setIntegral_mono_on (term_integrable ρ m).norm ((t_exp_integrable _ ha).const_mul _)
          measurableSet_Ioi hle
    _ = 2 * ρ / (2 * m + 1) ^ 2 := by
        rw [integral_const_mul, integral_t_exp _ ha]; ring

private lemma geom (t : ℝ) (ht : 0 < t) :
    HasSum (fun m : ℕ => Real.exp (-((2 * m + 1 : ℝ) * t))) (1 / (2 * Real.sinh t)) := by
  have hr : Real.exp (-(2 * t)) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h := (hasSum_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left (Real.exp (-t))
  convert h using 1
  · funext m
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  · have hs : Real.sinh t = (Real.exp t - Real.exp (-t)) / 2 := Real.sinh_eq t
    have e1 : Real.exp (-(2 * t)) = Real.exp (-t) ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have hexp : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    have hp := Real.exp_pos (-t)
    have hp2 := Real.exp_pos t
    have hne : 1 - Real.exp (-t) ^ 2 ≠ 0 := by
      rw [← e1]; linarith
    have hne2 : Real.exp t - Real.exp (-t) ≠ 0 := by
      intro h0
      have : Real.sinh t = 0 := by rw [hs, h0]; simp
      have := Real.sinh_pos_iff.mpr ht
      linarith
    rw [e1, hs]
    field_simp
    nlinarith [hexp]

/-- The sine transform of `1/sinh`: `∫_{t>0} sin (ρ t)/sinh t = (π/2) tanh (πρ/2)` for `ρ ≥ 0`. -/
theorem integral_sin_div_sinh {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫ t : ℝ in Ioi 0, Real.sin (ρ * t) / Real.sinh t
      = Real.pi / 2 * Real.tanh (Real.pi * ρ / 2) := by
  have hsum : Summable fun m : ℕ => ∫ t in Ioi (0:ℝ), ‖term ρ m t‖ := by
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun t => norm_nonneg _)
      (norm_term_integral_le ρ hρ) ?_
    have : Summable fun m : ℕ => 2 * ρ * (1 / ((m:ℝ) + 1) ^ 2) := by
      refine Summable.mul_left _ ?_
      have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
      simpa using this
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) this
    have : (0:ℝ) < (m:ℝ) + 1 := by positivity
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (m:ℝ), mul_nonneg hρ (sq_nonneg (m:ℝ)), mul_nonneg hρ (Nat.cast_nonneg (α := ℝ) m)]
  have h := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun m t => term ρ m t) (fun m => term_integrable ρ m) hsum
  have hval : ∀ m : ℕ, ∫ t in Ioi (0:ℝ), term ρ m t = 2 * (ρ / (ρ ^ 2 + (2 * m + 1) ^ 2)) := by
    intro m
    unfold term
    rw [integral_const_mul, integral_sin_mul_exp _ (by positivity)]
  have hT := (hasSum_tanh_series hρ).mul_left 2
  have h2 : (∫ t in Ioi (0:ℝ), ∑' m, term ρ m t) = 2 * (Real.pi / 4 * Real.tanh (Real.pi * ρ / 2)) := by
    refine h.unique ?_
    simpa [hval] using hT
  have h3 : ∀ t ∈ Ioi (0:ℝ), ∑' m, term ρ m t = Real.sin (ρ * t) / Real.sinh t := by
    intro t ht
    have hg := geom t ht
    have : ∑' m : ℕ, term ρ m t = 2 * (Real.sin (ρ * t) * (1 / (2 * Real.sinh t))) := by
      unfold term
      rw [tsum_mul_left, tsum_mul_left, hg.tsum_eq]
    rw [this]
    have hs := Real.sinh_pos_iff.mpr (show 0 < t from ht)
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi h3] at h2
  linarith

end Lightlike.Lorentz.SL2RPlancherel
