import Lightlike.Asymptotics.Karamata.Counting

/-!
# Karamata's Tauberian theorem

Let `ρ` be a measure on `[0, ∞)`, finite on compact sets, with Laplace transform
`L β = ∫ exp (-β x) dρ` finite for every `β > 0`.

* `karamata_tauberian`: if `L β · β ^ α → C` as `β → 0⁺`, with `C > 0` and `α > 0`
  (that is `L β ~ C β ^ (-α)`), then `ρ [0, X] / X ^ α → C / Γ(α + 1)` as `X → ∞`
  (that is `ρ [0, X] ~ C X ^ α / Γ(α + 1)`).
* `karamata_tauberian_zero`: the case `α = 0`: if `L β → C > 0` then `ρ [0, X] → C`.

The proof is Karamata's: the moment ratios `L ((k+1) β) / L β` converge to `(k+1) ^ (-α)`, the moments of
the image under `t ↦ exp (-t)` of the Gamma distribution with shape `α` and rate `1` (Mathlib's
`ProbabilityTheory.gammaMeasure α 1`; the unit mass at `0` when `α = 0`), and
`tendsto_counting_div_laplace` applies.

## References

* M. Herdegen, G. Liang, O. Shelley, *A continuity theorem for generalised signed measures with an
  application to Karamata's Tauberian theorem*, arXiv:2205.13075v2, Theorem 3.1 (the statement, in the form
  with regular variation; its Tauberian direction with a power in place of a regularly varying function is
  the theorem here).
-/

open MeasureTheory Set Filter Topology ProbabilityTheory

noncomputable section

namespace Lightlike.Karamata

open Lightlike.Tauberian

/-- Integration against the Gamma distribution with shape `α` and rate `1`. -/
lemma integral_gammaMeasure {α : ℝ} (hα : 0 < α) (f : ℝ → ℝ) :
    ∫ t, f t ∂(gammaMeasure α 1) =
      ∫ t in Ioi 0, (1 / Real.Gamma α * t ^ (α - 1) * Real.exp (-t)) * f t := by
  have hmeas : Measurable (gammaPDF α 1) := (measurable_gammaPDFReal α 1).ennreal_ofReal
  unfold gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top),
    ← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : 0 ≤ x
  · rw [indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx)]
    show (gammaPDF α 1 x).toReal • f x = _
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg hα one_pos x), gammaPDFReal, if_pos hx,
      smul_eq_mul]
    simp
  · rw [indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx)]
    show (gammaPDF α 1 x).toReal • f x = 0
    rw [gammaPDF_of_neg (not_le.1 hx)]
    simp

/-- The moments of `exp (-t)` under the Gamma distribution: its Laplace transform at the integers. -/
lemma integral_exp_pow_gammaMeasure {α : ℝ} (hα : 0 < α) (k : ℕ) :
    ∫ t, Real.exp (-t) ^ k ∂(gammaMeasure α 1) = ((k : ℝ) + 1) ^ (-α) := by
  rw [integral_gammaMeasure hα]
  have h : ∀ t : ℝ, (1 / Real.Gamma α * t ^ (α - 1) * Real.exp (-t)) * Real.exp (-t) ^ k =
      1 / Real.Gamma α * (t ^ (α - 1) * Real.exp (-(((k : ℝ) + 1) * t))) := by
    intro t
    rw [← Real.exp_nat_mul, mul_assoc, mul_assoc, ← Real.exp_add]
    congr 3
    ring
  simp_rw [h]
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hG : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα).ne'
  have hkα : ((k : ℝ) + 1) ^ α ≠ 0 := (Real.rpow_pos_of_pos hk α).ne'
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hα hk, Real.rpow_neg hk.le, one_div,
    one_div, Real.inv_rpow hk.le]
  field_simp

lemma gammaMeasure_Iio_zero (α : ℝ) : gammaMeasure α 1 (Iio 0) = 0 := by
  unfold gammaMeasure
  rw [withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

lemma gammaMeasure_singleton (α x : ℝ) : gammaMeasure α 1 {x} = 0 :=
  (withDensity_absolutelyContinuous _ _) Real.volume_singleton

lemma gStep_exp_neg (t : ℝ) : gStep (Real.exp (-t)) = if t ≤ 1 then Real.exp t else 0 := by
  unfold gStep
  by_cases h : t ≤ 1
  · rw [if_pos (Real.exp_le_exp.2 (by linarith)), if_pos h, one_div, ← Real.exp_neg, neg_neg]
  · rw [if_neg (by rw [Real.exp_le_exp]; linarith [not_le.1 h]), if_neg h]

/-- The limit constant of Karamata's theorem: `∫ gStep (exp (-t)) dγ_α = 1 / Γ(α + 1)`. -/
lemma integral_gStep_gammaMeasure {α : ℝ} (hα : 0 < α) :
    ∫ t, gStep (Real.exp (-t)) ∂(gammaMeasure α 1) = 1 / Real.Gamma (α + 1) := by
  rw [integral_gammaMeasure hα]
  have h : EqOn (fun t : ℝ => (1 / Real.Gamma α * t ^ (α - 1) * Real.exp (-t)) * gStep (Real.exp (-t)))
      ((Ioc (0 : ℝ) 1).indicator fun t => 1 / Real.Gamma α * t ^ (α - 1)) (Ioi 0) := by
    intro t ht
    show (1 / Real.Gamma α * t ^ (α - 1) * Real.exp (-t)) * gStep (Real.exp (-t)) = _
    rw [gStep_exp_neg]
    by_cases h1 : t ≤ 1
    · rw [if_pos h1, indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, h1⟩), mul_assoc,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    · rw [if_neg h1, mul_zero, indicator_of_notMem (fun hm : t ∈ Ioc (0 : ℝ) 1 => h1 hm.2)]
  have hs : Ioi (0 : ℝ) ∩ Ioc 0 1 = Ioc 0 1 := inter_eq_right.2 fun t ht => ht.1
  have hG : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα).ne'
  rw [setIntegral_congr_fun measurableSet_Ioi h, setIntegral_indicator measurableSet_Ioc, hs,
    ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith)), Real.Gamma_add_one hα.ne']
  have hα0 : α ≠ 0 := hα.ne'
  simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow hα.ne', sub_zero]
  field_simp

lemma tendsto_const_mul_nhdsGT_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun β : ℝ => c * β) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun β : ℝ => c * β) (𝓝 0) (𝓝 (c * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    exact mul_pos hc hβ

lemma tendsto_one_div_atTop_nhdsGT_zero : Tendsto (fun X : ℝ => 1 / X) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · simpa [one_div] using tendsto_inv_atTop_zero (𝕜 := ℝ)
  · filter_upwards [eventually_gt_atTop 0] with X hX
    exact one_div_pos.2 hX

variable {ρ : Measure ℝ} [IsFiniteMeasureOnCompacts ρ]

/-- **Karamata's Tauberian theorem** (power case). Let `ρ` be a measure on `[0, ∞)`, finite on compact
sets, whose Laplace transform `L β = ∫ exp (-β x) dρ` is finite for all `β > 0`. If `L β ~ C β ^ (-α)` as
`β → 0⁺`, with `C > 0` and `α > 0`, then `ρ [0, X] ~ C X ^ α / Γ(α + 1)` as `X → ∞`. -/
theorem karamata_tauberian (hρ : ρ (Iio 0) = 0)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ) {C α : ℝ} (hC : 0 < C)
    (hα : 0 < α) (hL : Tendsto (fun β => laplace ρ β * β ^ α) (𝓝[>] 0) (𝓝 C)) :
    Tendsto (fun X => counting ρ X / X ^ α) atTop (𝓝 (C / Real.Gamma (α + 1))) := by
  have hprob := isProbabilityMeasure_gammaMeasure hα one_pos
  have hpos : ∀ᶠ β in 𝓝[>] (0 : ℝ), 0 < laplace ρ β := by
    filter_upwards [hL.eventually (lt_mem_nhds hC), self_mem_nhdsWithin] with β h1 hβ
    have hβ' : (0 : ℝ) < β := hβ
    exact (pos_iff_pos_of_mul_pos h1).2 (Real.rpow_pos_of_pos hβ' α)
  have hmom : ∀ k : ℕ, Tendsto (fun β => laplace ρ ((k + 1) * β) / laplace ρ β) (𝓝[>] 0)
      (𝓝 (∫ t, Real.exp (-t) ^ k ∂(gammaMeasure α 1))) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [integral_exp_pow_gammaMeasure hα]
    have h1 := (hL.comp (tendsto_const_mul_nhdsGT_zero hk)).div hL hC.ne'
    have h2 := h1.mul_const (((k : ℝ) + 1) ^ (-α))
    rw [div_self hC.ne', one_mul] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hpos] with β hβ hLβ
    have hβ' : (0 : ℝ) < β := hβ
    show (laplace ρ (((k : ℝ) + 1) * β) * (((k : ℝ) + 1) * β) ^ α) / (laplace ρ β * β ^ α) *
      ((k : ℝ) + 1) ^ (-α) = laplace ρ (((k : ℝ) + 1) * β) / laplace ρ β
    rw [Real.mul_rpow hk.le hβ'.le, Real.rpow_neg hk.le]
    have h3 : β ^ α ≠ 0 := (Real.rpow_pos_of_pos hβ' α).ne'
    have h4 : ((k : ℝ) + 1) ^ α ≠ 0 := (Real.rpow_pos_of_pos hk α).ne'
    have h5 : laplace ρ β ≠ 0 := hLβ.ne'
    field_simp
  have hmain := tendsto_counting_div_laplace hρ hint (gammaMeasure_Iio_zero α)
    (gammaMeasure_singleton α 1) hmom hpos
  rw [integral_gStep_gammaMeasure hα] at hmain
  have h7 := (hmain.mul hL).comp tendsto_one_div_atTop_nhdsGT_zero
  rw [show C / Real.Gamma (α + 1) = 1 / Real.Gamma (α + 1) * C by ring]
  refine h7.congr' ?_
  filter_upwards [eventually_gt_atTop 0, tendsto_one_div_atTop_nhdsGT_zero.eventually hpos]
    with X hX hLX
  show counting ρ (1 / (1 / X)) / laplace ρ (1 / X) * (laplace ρ (1 / X) * (1 / X) ^ α) =
    counting ρ X / X ^ α
  have hXα : X ^ α ≠ 0 := (Real.rpow_pos_of_pos hX α).ne'
  have hLne : laplace ρ (1 / X) ≠ 0 := hLX.ne'
  rw [one_div_one_div, Real.div_rpow zero_le_one hX.le, Real.one_rpow]
  field_simp

/-- **Karamata's Tauberian theorem, the case `α = 0`.** If the Laplace transform of `ρ` tends to `C > 0`
as `β → 0⁺`, then `ρ [0, X] → C` as `X → ∞`. -/
theorem karamata_tauberian_zero (hρ : ρ (Iio 0) = 0)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ) {C : ℝ} (hC : 0 < C)
    (hL : Tendsto (fun β => laplace ρ β) (𝓝[>] 0) (𝓝 C)) :
    Tendsto (fun X => counting ρ X) atTop (𝓝 C) := by
  have hpos : ∀ᶠ β in 𝓝[>] (0 : ℝ), 0 < laplace ρ β := hL.eventually (lt_mem_nhds hC)
  have hν0 : (Measure.dirac (0 : ℝ)) (Iio 0) = 0 := by simp
  have hν1 : (Measure.dirac (0 : ℝ)) {1} = 0 := by simp
  have hmom : ∀ k : ℕ, Tendsto (fun β => laplace ρ ((k + 1) * β) / laplace ρ β) (𝓝[>] 0)
      (𝓝 (∫ t, Real.exp (-t) ^ k ∂(Measure.dirac (0 : ℝ)))) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h1 := (hL.comp (tendsto_const_mul_nhdsGT_zero hk)).div hL hC.ne'
    rw [div_self hC.ne'] at h1
    have h2 : ∫ t, Real.exp (-t) ^ k ∂(Measure.dirac (0 : ℝ)) = 1 := by simp
    rw [h2]
    exact h1
  have hmain := tendsto_counting_div_laplace hρ hint hν0 hν1 hmom hpos
  have hval : ∫ t, gStep (Real.exp (-t)) ∂(Measure.dirac (0 : ℝ)) = 1 := by
    rw [integral_dirac, gStep_exp_neg, if_pos zero_le_one, Real.exp_zero]
  rw [hval] at hmain
  have h7 := (hmain.mul hL).comp tendsto_one_div_atTop_nhdsGT_zero
  rw [one_mul] at h7
  refine h7.congr' ?_
  filter_upwards [eventually_gt_atTop 0, tendsto_one_div_atTop_nhdsGT_zero.eventually hpos]
    with X hX hLX
  show counting ρ (1 / (1 / X)) / laplace ρ (1 / X) * laplace ρ (1 / X) = counting ρ X
  rw [one_div_one_div, div_mul_cancel₀ _ hLX.ne']

end Lightlike.Karamata
