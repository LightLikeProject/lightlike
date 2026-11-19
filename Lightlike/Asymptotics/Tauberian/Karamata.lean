import Lightlike.Asymptotics.Tauberian.Functional
import Lightlike.Asymptotics.Tauberian.Ramp

/-!
# Karamata's theorem: the limit functional on the ramps

The values of `Phi` on the ramp functions of `Ramp.lean` are squeezed between the integrals of the
weight `x^{α-1} / Γ(α)` over `(0, s]`, `s = log (1/c)` resp. `log (1/d)`, which equal `s^α / Γ(α+1)`.
-/

open MeasureTheory Set Real Filter Topology intervalIntegral

noncomputable section

namespace Lightlike.Tauberian

/-- `∫_{(0,s]} x^{α-1}/Γ(α) dx = s^α / Γ(α+1)`. -/
lemma integral_weight_Ioc {α : ℝ} (hα : 0 < α) {s : ℝ} (hs : 0 ≤ s) :
    ∫ x in Ioc (0 : ℝ) s, x ^ (α - 1) / Real.Gamma α = s ^ α / Real.Gamma (α + 1) := by
  rw [← intervalIntegral.integral_of_le hs, intervalIntegral.integral_div,
    integral_rpow (Or.inl (by linarith))]
  have hΓ : Real.Gamma (α + 1) = α * Real.Gamma α := Real.Gamma_add_one hα.ne'
  rw [hΓ, show α - 1 + 1 = α by ring, Real.zero_rpow hα.ne']
  field_simp
  ring

/-- Upper bound: `Φ (rampUp c) ≤ (log (1/c))^α / Γ(α+1)`. -/
lemma phi_rampUp_le {α : ℝ} (hα : 0 < α) {c : ℝ} (hc0 : 0 < c) (hc : c < einv) :
    Phi α (rampUp c) ≤ (-Real.log c) ^ α / Real.Gamma (α + 1) := by
  have hs : 0 ≤ -Real.log c := by
    have : Real.log c < 0 := Real.log_neg hc0 (by
      have : einv < 1 := by simpa using Real.exp_lt_one (by norm_num : (-1 : ℝ) < 0)
      linarith)
    linarith
  rw [← integral_weight_Ioc hα hs]
  have hind : ∫ x in Ioc (0 : ℝ) (-Real.log c), x ^ (α - 1) / Real.Gamma α =
      ∫ x in Ioi (0 : ℝ), (Ioc (0 : ℝ) (-Real.log c)).indicator (fun x => x ^ (α - 1) / Real.Gamma α) x := by
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.2 Set.Ioc_subset_Ioi_self]
  rw [hind]
  have hw : ∀ x : ℝ, 0 < x → 0 ≤ x ^ (α - 1) / Real.Gamma α := fun x hx =>
    div_nonneg (Real.rpow_nonneg hx.le _) (Real.Gamma_pos_of_pos hα).le
  have hint : IntegrableOn ((Ioc (0 : ℝ) (-Real.log c)).indicator
      (fun x : ℝ => x ^ (α - 1) / Real.Gamma α)) (Ioi 0) := by
    have h0 : IntervalIntegrable (fun x : ℝ => x ^ (α - 1)) volume 0 (-Real.log c) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have h1 : IntegrableOn (fun x : ℝ => x ^ (α - 1) / Real.Gamma α) (Ioc 0 (-Real.log c)) :=
      (h0.1).div_const _
    exact (h1.integrable_indicator measurableSet_Ioc).integrableOn
  refine setIntegral_mono_on (integrableOn_phi hα (continuous_rampUp c)) hint measurableSet_Ioi ?_
  intro x hx
  have hx0 : 0 < x := hx
  by_cases hxs : x ≤ -Real.log c
  · rw [Set.indicator_of_mem (show x ∈ Ioc (0 : ℝ) (-Real.log c) from ⟨hx0, hxs⟩)]
    have h1 := mul_rampUp_le c (Real.exp_pos (-x)).le
    calc Real.exp (-x) * rampUp c (Real.exp (-x)) * (x ^ (α - 1) / Real.Gamma α)
        ≤ 1 * (x ^ (α - 1) / Real.Gamma α) := mul_le_mul_of_nonneg_right h1 (hw x hx0)
      _ = _ := one_mul _
  · rw [Set.indicator_of_notMem (fun h => hxs h.2)]
    have : Real.exp (-x) ≤ c := by
      have : -x ≤ Real.log c := by linarith [not_le.1 hxs]
      calc Real.exp (-x) ≤ Real.exp (Real.log c) := Real.exp_le_exp.2 this
        _ = c := Real.exp_log hc0
    rw [mul_rampUp_eq_zero this hc, zero_mul]

/-- Lower bound: `(log (1/d))^α / Γ(α+1) ≤ Φ (rampDown d)`. -/
lemma phi_rampDown_ge {α : ℝ} (hα : 0 < α) {d : ℝ} (hd : einv < d) (hd1 : d < 1) :
    (-Real.log d) ^ α / Real.Gamma (α + 1) ≤ Phi α (rampDown d) := by
  have hd0 : 0 < d := einv_pos.trans hd
  have hs : 0 ≤ -Real.log d := by linarith [Real.log_neg hd0 hd1]
  rw [← integral_weight_Ioc hα hs]
  have hind : ∫ x in Ioc (0 : ℝ) (-Real.log d), x ^ (α - 1) / Real.Gamma α =
      ∫ x in Ioi (0 : ℝ), (Ioc (0 : ℝ) (-Real.log d)).indicator (fun x => x ^ (α - 1) / Real.Gamma α) x := by
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.2 Set.Ioc_subset_Ioi_self]
  rw [hind]
  have hw : ∀ x : ℝ, 0 < x → 0 ≤ x ^ (α - 1) / Real.Gamma α := fun x hx =>
    div_nonneg (Real.rpow_nonneg hx.le _) (Real.Gamma_pos_of_pos hα).le
  have hint : IntegrableOn ((Ioc (0 : ℝ) (-Real.log d)).indicator
      (fun x : ℝ => x ^ (α - 1) / Real.Gamma α)) (Ioi 0) := by
    have h0 : IntervalIntegrable (fun x : ℝ => x ^ (α - 1)) volume 0 (-Real.log d) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have h1 : IntegrableOn (fun x : ℝ => x ^ (α - 1) / Real.Gamma α) (Ioc 0 (-Real.log d)) :=
      (h0.1).div_const _
    exact (h1.integrable_indicator measurableSet_Ioc).integrableOn
  refine setIntegral_mono_on hint (integrableOn_phi hα (continuous_rampDown d)) measurableSet_Ioi ?_
  intro x hx
  have hx0 : 0 < x := hx
  by_cases hxs : x ≤ -Real.log d
  · rw [Set.indicator_of_mem (show x ∈ Ioc (0 : ℝ) (-Real.log d) from ⟨hx0, hxs⟩)]
    have : d ≤ Real.exp (-x) := by
      calc d = Real.exp (Real.log d) := (Real.exp_log hd0).symm
        _ ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)
    rw [mul_rampDown_eq_one this hd, one_mul]
  · rw [Set.indicator_of_notMem (fun h => hxs h.2)]
    have h1 := mul_rampDown_le d (Real.exp_pos (-x)).le
    have h2 : 0 ≤ Real.exp (-x) * rampDown d (Real.exp (-x)) :=
      mul_nonneg (Real.exp_pos _).le (rampDown_nonneg _ _)
    exact mul_nonneg h2 (hw x hx0)

variable {ρ : Measure ℝ}

lemma counting_eq_integral [IsFiniteMeasureOnCompacts ρ] (X : ℝ) :
    counting ρ X = ∫ x, (Icc (0 : ℝ) X).indicator (fun _ => (1 : ℝ)) x ∂ρ := by
  rw [integral_indicator_const _ measurableSet_Icc]
  simp [counting, Measure.real]

/-- `ρ[0,t] ≤ ∫ e^{-x/t} rampUp c (e^{-x/t}) dρ`. -/
lemma counting_le_integral_rampUp [IsFiniteMeasureOnCompacts ρ] (hρ : ρ (Iio 0) = 0)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ) {c : ℝ} (hc : c < einv)
    {t : ℝ} (ht : 0 < t) :
    counting ρ t ≤ ∫ x, Real.exp (-(1 / t) * x) * rampUp c (Real.exp (-(1 / t) * x)) ∂ρ := by
  rw [counting_eq_integral]
  have h0 : ∀ᵐ x ∂ρ, x ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.1 hρ
  refine integral_mono_ae ?_ (integrable_lam hρ hint (continuous_rampUp c) ht) ?_
  · exact (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (measure_Icc_lt_top).ne)
  · filter_upwards [h0] with x hx
    have hx0 : 0 ≤ x := not_lt.1 hx
    by_cases hxt : x ≤ t
    · rw [Set.indicator_of_mem (show x ∈ Icc (0 : ℝ) t from ⟨hx0, hxt⟩)]
      have : einv ≤ Real.exp (-(1 / t) * x) := by
        refine Real.exp_le_exp.2 ?_
        have : x / t ≤ 1 := (div_le_one ht).2 hxt
        rw [neg_mul, one_div, inv_mul_eq_div]; linarith
      exact (mul_rampUp_eq_one this hc).ge
    · rw [Set.indicator_of_notMem (fun h => hxt h.2)]
      exact mul_nonneg (Real.exp_pos _).le (rampUp_nonneg _ _)

/-- `∫ e^{-x/t} rampDown d (e^{-x/t}) dρ ≤ ρ[0,t]`. -/
lemma integral_rampDown_le_counting [IsFiniteMeasureOnCompacts ρ] (hρ : ρ (Iio 0) = 0)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ) {d : ℝ} (hd : einv < d)
    {t : ℝ} (ht : 0 < t) :
    ∫ x, Real.exp (-(1 / t) * x) * rampDown d (Real.exp (-(1 / t) * x)) ∂ρ ≤ counting ρ t := by
  rw [counting_eq_integral]
  have h0 : ∀ᵐ x ∂ρ, x ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.1 hρ
  refine integral_mono_ae (integrable_lam hρ hint (continuous_rampDown d) ht) ?_ ?_
  · exact (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (measure_Icc_lt_top).ne)
  · filter_upwards [h0] with x hx
    have hx0 : 0 ≤ x := not_lt.1 hx
    by_cases hxt : x ≤ t
    · rw [Set.indicator_of_mem (show x ∈ Icc (0 : ℝ) t from ⟨hx0, hxt⟩)]
      exact mul_rampDown_le d (Real.exp_pos _).le
    · rw [Set.indicator_of_notMem (fun h => hxt h.2)]
      have : Real.exp (-(1 / t) * x) ≤ einv := by
        refine Real.exp_le_exp.2 ?_
        have : 1 < x / t := (one_lt_div ht).2 (not_le.1 hxt)
        rw [neg_mul, one_div, inv_mul_eq_div]; linarith
      exact (mul_rampDown_eq_zero this hd).le

lemma einv_lt_one : einv < 1 := by simpa using Real.exp_lt_one (by norm_num : (-1 : ℝ) < 0)

lemma continuousAt_weight {α : ℝ} (hα : 0 < α) :
    ContinuousAt (fun u : ℝ => (-Real.log u) ^ α / Real.Gamma (α + 1)) einv := by
  have hl : ContinuousAt (fun u : ℝ => -Real.log u) einv :=
    (Real.continuousAt_log einv_pos.ne').neg
  have h1 : (-Real.log einv) = 1 := by simp [einv]
  refine ContinuousAt.div_const (ContinuousAt.rpow_const hl (Or.inl ?_)) _
  rw [h1]; exact one_ne_zero

/-- **Karamata's Tauberian theorem** (power-law case with slowly varying correction). -/
theorem karamata [IsFiniteMeasureOnCompacts ρ] (hρ : ρ (Iio 0) = 0)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ) {α : ℝ} (hα : 0 < α)
    {ℓ : ℝ → ℝ} (hℓ : SlowlyVarying ℓ)
    (hL : Tendsto (fun β : ℝ => laplace ρ β / (β ^ (-α) * ℓ (1 / β))) (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun t : ℝ => counting ρ t / (t ^ α * ℓ t)) atTop (𝓝 (1 / Real.Gamma (α + 1))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcont := Metric.continuousAt_iff.1 (continuousAt_weight hα) (ε / 2) (by positivity)
  obtain ⟨δ, hδ, hδ'⟩ := hcont
  have hval : (-Real.log einv) ^ α / Real.Gamma (α + 1) = 1 / Real.Gamma (α + 1) := by
    simp [einv]
  set η := min δ (min einv (1 - einv)) / 2 with hη
  have hη0 : 0 < η := by
    have : 0 < 1 - einv := by linarith [einv_lt_one]
    positivity
  have hηδ : η < δ := by
    have := min_le_left δ (min einv (1 - einv)); linarith
  have hηe : η < einv := by
    have := (min_le_right δ (min einv (1 - einv))).trans (min_le_left _ _); linarith
  have hη1 : η < 1 - einv := by
    have := (min_le_right δ (min einv (1 - einv))).trans (min_le_right _ _); linarith
  set c := einv - η
  set d := einv + η
  have hc0 : 0 < c := by simp only [c]; linarith
  have hcl : c < einv := by simp only [c]; linarith
  have hdl : einv < d := by simp only [d]; linarith
  have hd1 : d < 1 := by simp only [d]; linarith
  have hcb := hδ' (x := c) (by rw [Real.dist_eq]; simp only [c]; rw [abs_lt]; constructor <;> linarith)
  have hdb := hδ' (x := d) (by rw [Real.dist_eq]; simp only [d]; rw [abs_lt]; constructor <;> linarith)
  rw [hval, Real.dist_eq] at hcb hdb
  have hup := tendsto_lam hρ hint hα hℓ hL (continuous_rampUp c)
  have hdown := tendsto_lam hρ hint hα hℓ hL (continuous_rampDown d)
  have hP1 := phi_rampUp_le hα hc0 hcl
  have hP2 := phi_rampDown_ge hα hdl hd1
  have hu := (Metric.tendsto_nhds.1 hup) (ε / 2) (by positivity)
  have hd := (Metric.tendsto_nhds.1 hdown) (ε / 2) (by positivity)
  have hm : ∀ᶠ t in atTop, 0 < t ^ α * ℓ t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hℓ.1] with t ht hℓt
    exact mul_pos (Real.rpow_pos_of_pos ht _) hℓt
  filter_upwards [hu, hd, hm, eventually_gt_atTop (0 : ℝ)] with t hut hdt htm ht
  rw [Real.dist_eq] at hut hdt ⊢
  have h1 := counting_le_integral_rampUp hρ hint hcl ht
  have h2 := integral_rampDown_le_counting hρ hint hdl ht
  have e1 : counting ρ t / (t ^ α * ℓ t) ≤ Lam ρ α ℓ (rampUp c) t := div_le_div_of_nonneg_right h1 htm.le
  have e2 : Lam ρ α ℓ (rampDown d) t ≤ counting ρ t / (t ^ α * ℓ t) := div_le_div_of_nonneg_right h2 htm.le
  rw [abs_lt] at hut hdt hcb hdb ⊢
  constructor <;> linarith [hcb.1, hcb.2, hdb.1, hdb.2, hut.1, hut.2, hdt.1, hdt.2]

end Lightlike.Tauberian
