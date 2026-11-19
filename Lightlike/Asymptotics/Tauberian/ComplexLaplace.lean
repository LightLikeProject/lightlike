import Lightlike.Asymptotics.Tauberian.Crossing
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The complex Laplace transform of the powers

`∫₀^∞ x^k e^{-z x} dx = k! / z^{k+1}` for `Re z > 0` (integration by parts and the case `k = 0` of
Mathlib's exponential integral). This gives the complex Laplace transform of the crossing density,
`∫₀^∞ ρ₀(x) e^{-z x} dx = e^{a/z} - 1`.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace Lightlike.Tauberian

lemma integrableOn_pow_cexp {z : ℂ} (hz : 0 < z.re) (k : ℕ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ k * Complex.exp (-(z * x))) (Ioi 0) := by
  have h1 := integrableOn_pow_exp (β := z.re) hz k
  refine (integrable_norm_iff ?_).mp ?_
  · exact (by fun_prop : Continuous fun x : ℝ => (x : ℂ) ^ k * Complex.exp (-(z * x))).aestronglyMeasurable
  · refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx' : (0 : ℝ) < x := hx
    simp [Complex.norm_exp, norm_pow, abs_of_pos hx']

/-- `∫₀^∞ x^k e^{-z x} dx = k! / z^{k+1}`. -/
theorem integral_pow_cexp {z : ℂ} (hz : 0 < z.re) (k : ℕ) :
    ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ k * Complex.exp (-(z * x)) = (k.factorial : ℂ) / z ^ (k + 1) := by
  induction k with
  | zero =>
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
    have := integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0
    simpa [neg_mul] using this
  | succ k ih =>
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
    set u : ℝ → ℂ := fun x => (x : ℂ) ^ (k + 1) with hu
    set u' : ℝ → ℂ := fun x => ((k : ℂ) + 1) * (x : ℂ) ^ k with hu'
    set v : ℝ → ℂ := fun x => -(Complex.exp (-(z * x))) / z with hv
    set v' : ℝ → ℂ := fun x => Complex.exp (-(z * x)) with hv'
    have hud : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (u' x) x := by
      intro x _
      have := (hasDerivAt_pow (k + 1) (x : ℂ)).comp_ofReal
      simpa [hu, hu'] using this
    have hvd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (v' x) x := by
      intro x _
      have h1 : HasDerivAt (fun w : ℂ => -(Complex.exp (-(z * w))) / z) (Complex.exp (-(z * (x : ℂ)))) (x : ℂ) := by
        have h0 : HasDerivAt (fun w : ℂ => -(z * w)) (-z) (x : ℂ) := by
          convert ((hasDerivAt_id (x : ℂ)).const_mul z).neg using 1
          · funext w; simp
          · simp
        have := (h0.cexp).neg.div_const z
        convert this using 1
        field_simp
      exact h1.comp_ofReal
    have huv' : IntegrableOn (u * v') (Ioi 0) := by
      have h0 := integrableOn_pow_cexp hz (k + 1)
      exact IntegrableOn.congr_fun h0 (fun x _ => by simp only [Pi.mul_apply, hu, hv']) measurableSet_Ioi
    have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
      have h0 := Integrable.const_mul (integrableOn_pow_cexp hz k) (-((k : ℂ) + 1) / z)
      refine IntegrableOn.congr_fun h0 (fun x _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply, hu', hv]
      field_simp
    have hzero : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (u * v) := by
        simp only [hu, hv]; fun_prop
      have : (u * v) 0 = 0 := by simp [hu]
      simpa [this] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have hinf : Tendsto (u * v) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k : ℝ) + 1) z.re hz
      have h2 := h1.div_const ‖z‖
      rw [zero_div] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      simp only [Pi.mul_apply, hu, hv, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hx, norm_div, norm_neg, Complex.norm_exp]
      have e1 : (-(z * (x : ℂ))).re = -z.re * x := by simp
      have e2 : x ^ ((k : ℝ) + 1) = x ^ (k + 1) := by
        rw [← Nat.cast_add_one, Real.rpow_natCast]
      rw [e1, e2]
      ring
    have h := integral_Ioi_mul_deriv_eq_deriv_mul hud hvd huv' hu'v hzero hinf
    have e1 : ∫ x in Ioi (0 : ℝ), u' x * v x =
        (-((k : ℂ) + 1) / z) * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ k * Complex.exp (-(z * x)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hu', hv]
      field_simp
    show ∫ x in Ioi (0 : ℝ), u x * v' x = _
    rw [h, e1, ih, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- **D1, complex form.** For `a > 0` and `Re z > 0`,
`∫₀^∞ ρ₀(x) e^{-z x} dx = e^{a/z} - 1`. -/
theorem integral_crossing_cexp {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.re) :
    ∫ x in Ioi (0 : ℝ), (crossingDensity a x : ℂ) * Complex.exp (-(z * x)) =
      Complex.exp ((a : ℂ) / z) - 1 := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  set F : ℕ → ℝ → ℂ := fun k x => (crossingTerm a k x : ℂ) * Complex.exp (-(z * x)) with hF
  have hFeq : ∀ k x, F k x = ((a ^ (k + 1) / (((k + 1).factorial : ℝ) * (k.factorial : ℝ)) : ℝ) : ℂ) *
      ((x : ℂ) ^ k * Complex.exp (-(z * x))) := by
    intro k x; simp only [hF, crossingTerm]; push_cast; ring
  have hint : ∀ k, Integrable (F k) (volume.restrict (Ioi (0 : ℝ))) := fun k => by
    have := Integrable.const_mul (integrableOn_pow_cexp hz k)
      ((a ^ (k + 1) / (((k + 1).factorial : ℝ) * (k.factorial : ℝ)) : ℝ) : ℂ)
    exact this.congr (Filter.Eventually.of_forall fun x => (hFeq k x).symm)
  have hval : ∀ k : ℕ, ∫ x in Ioi (0 : ℝ), F k x = ((a : ℂ) / z) ^ (k + 1) / ((k + 1).factorial : ℂ) := by
    intro k
    simp_rw [hFeq]
    rw [integral_const_mul, integral_pow_cexp hz k]
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
    have hk1 : ((k + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (k + 1)).ne'
    have hz1 : z ^ (k + 1) ≠ 0 := pow_ne_zero _ hz0
    push_cast
    rw [div_pow]
    field_simp
  have hnorm : ∀ k : ℕ, ∫ x in Ioi (0 : ℝ), ‖F k x‖ =
      ∫ x in Ioi (0 : ℝ), crossingTerm a k x * Real.exp (-z.re * x) := by
    intro k
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx' : (0 : ℝ) < x := hx
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    rw [abs_of_nonneg (crossingTerm_nonneg ha k hx'.le)]
    congr 2
    simp
  have hsum : Summable fun k : ℕ => ∫ x in Ioi (0 : ℝ), ‖F k x‖ := by
    simp_rw [hnorm]
    exact (hasSum_crossing_integral ha hz).summable
  have h := integral_tsum_of_summable_integral_norm hint hsum
  have hexp : HasSum (fun k : ℕ => ((a : ℂ) / z) ^ (k + 1) / ((k + 1).factorial : ℂ))
      (Complex.exp ((a : ℂ) / z) - 1) := by
    have := NormedSpace.expSeries_div_hasSum_exp ((a : ℂ) / z)
    rw [← hasSum_nat_add_iff' 1] at this
    rw [← Complex.exp_eq_exp_ℂ] at this
    simpa [Finset.sum_range_one] using this
  simp_rw [hval] at h
  rw [hexp.tsum_eq] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hF, crossingDensity]
  rw [Complex.ofReal_tsum, tsum_mul_right]

end Lightlike.Tauberian
