import Lightlike.Asymptotics.Karamata.Karamata

/-!
# Karamata's Tauberian theorem with regular variation: the Tauberian direction

Let `ρ` be a measure on `[0, ∞)`, finite on compact sets, with Laplace transform `L` finite on `(0, ∞)`, and
`α ≥ 0`. If `L` is regularly varying at `0⁺` with index `-α`, that is

`L (τ λ) / L τ → λ ^ (-α)` as `τ → 0⁺`, for every `λ > 0`,

then

* `karamata_laplace_div_counting`: `L (1/t) / ρ [0, t] → Γ(α + 1)` as `t → ∞`;
* `karamata_counting_regularlyVarying`: `ρ [0, t x] / ρ [0, t] → x ^ α` as `t → ∞`, for every `x > 0`.

## References

* M. Herdegen, G. Liang, O. Shelley, *A continuity theorem for generalised signed measures with an
  application to Karamata's Tauberian theorem*, arXiv:2205.13075v2, Theorem 3.1: (3.1) implies (3.2), and
  (3.3).
-/

open MeasureTheory Set Filter Topology ProbabilityTheory

noncomputable section

namespace Lightlike.Karamata

open Lightlike.Tauberian

variable {ρ : Measure ℝ} [IsFiniteMeasureOnCompacts ρ]

section

variable (hρ : ρ (Iio 0) = 0)
  (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ) {α : ℝ} (hα : 0 ≤ α)
  (hRV : ∀ lam : ℝ, 0 < lam →
    Tendsto (fun τ => laplace ρ (τ * lam) / laplace ρ τ) (𝓝[>] 0) (𝓝 (lam ^ (-α))))
include hRV

omit [IsFiniteMeasureOnCompacts ρ] in
/-- Regular variation of the Laplace transform forces it to be positive near `0⁺`. -/
lemma eventually_laplace_pos_of_rv : ∀ᶠ β in 𝓝[>] (0 : ℝ), 0 < laplace ρ β := by
  have h := hRV 1 one_pos
  simp only [mul_one, Real.one_rpow] at h
  filter_upwards [h.eventually (lt_mem_nhds zero_lt_one)] with β hβ
  rcases (laplace_nonneg ρ β).eq_or_lt with h0 | h0
  · rw [← h0, div_zero] at hβ
    exact absurd hβ (lt_irrefl _)
  · exact h0

include hρ hint hα

/-- The core limit of Karamata's theorem: `ρ [0, 1/β] / L β → 1 / Γ(α + 1)` as `β → 0⁺`. -/
theorem tendsto_counting_div_laplace_of_rv :
    Tendsto (fun β => counting ρ (1 / β) / laplace ρ β) (𝓝[>] 0) (𝓝 (1 / Real.Gamma (α + 1))) := by
  have hpos := eventually_laplace_pos_of_rv hRV
  have hmomα : ∀ k : ℕ, Tendsto (fun β => laplace ρ ((k + 1) * β) / laplace ρ β) (𝓝[>] 0)
      (𝓝 (((k : ℝ) + 1) ^ (-α))) := by
    intro k
    have h := hRV ((k : ℝ) + 1) (by positivity)
    refine h.congr' (Filter.Eventually.of_forall fun β => ?_)
    show laplace ρ (β * ((k : ℝ) + 1)) / laplace ρ β = laplace ρ (((k : ℝ) + 1) * β) / laplace ρ β
    rw [mul_comm]
  rcases hα.eq_or_lt with h0 | h0
  · subst h0
    have hν0 : (Measure.dirac (0 : ℝ)) (Iio 0) = 0 := by simp
    have hν1 : (Measure.dirac (0 : ℝ)) {1} = 0 := by simp
    have hmom : ∀ k : ℕ, Tendsto (fun β => laplace ρ ((k + 1) * β) / laplace ρ β) (𝓝[>] 0)
        (𝓝 (∫ t, Real.exp (-t) ^ k ∂(Measure.dirac (0 : ℝ)))) := by
      intro k
      have h2 : ∫ t, Real.exp (-t) ^ k ∂(Measure.dirac (0 : ℝ)) = 1 := by simp
      rw [h2]
      have h := hmomα k
      rw [neg_zero, Real.rpow_zero] at h
      exact h
    have hmain := tendsto_counting_div_laplace hρ hint hν0 hν1 hmom hpos
    have hval : ∫ t, gStep (Real.exp (-t)) ∂(Measure.dirac (0 : ℝ)) = 1 := by
      rw [integral_dirac, gStep_exp_neg, if_pos zero_le_one, Real.exp_zero]
    rw [hval] at hmain
    rw [zero_add, Real.Gamma_one, div_one]
    exact hmain
  · have hprob := isProbabilityMeasure_gammaMeasure h0 one_pos
    have hmom : ∀ k : ℕ, Tendsto (fun β => laplace ρ ((k + 1) * β) / laplace ρ β) (𝓝[>] 0)
        (𝓝 (∫ t, Real.exp (-t) ^ k ∂(gammaMeasure α 1))) := by
      intro k
      rw [integral_exp_pow_gammaMeasure h0]
      exact hmomα k
    have hmain := tendsto_counting_div_laplace hρ hint (gammaMeasure_Iio_zero α)
      (gammaMeasure_singleton α 1) hmom hpos
    rw [integral_gStep_gammaMeasure h0] at hmain
    exact hmain

/-- **Karamata's Tauberian theorem, (3.3).** If the Laplace transform `L` of `ρ` is regularly varying at
`0⁺` with index `-α`, then `L (1/t) ~ ρ [0, t] Γ(α + 1)` as `t → ∞`. -/
theorem karamata_laplace_div_counting :
    Tendsto (fun t => laplace ρ (1 / t) / counting ρ t) atTop (𝓝 (Real.Gamma (α + 1))) := by
  have hG : 0 < Real.Gamma (α + 1) := Real.Gamma_pos_of_pos (by linarith)
  have h1 := (tendsto_counting_div_laplace_of_rv hρ hint hα hRV).comp
    tendsto_one_div_atTop_nhdsGT_zero
  have h2 := h1.inv₀ (one_div_ne_zero hG.ne')
  rw [one_div, inv_inv] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  show (counting ρ (1 / (1 / t)) / laplace ρ (1 / t))⁻¹ = laplace ρ (1 / t) / counting ρ t
  rw [one_div_one_div, inv_div]

/-- **Karamata's Tauberian theorem, (3.1) ⇒ (3.2).** If the Laplace transform of `ρ` is regularly varying
at `0⁺` with index `-α`, then the counting function `t ↦ ρ [0, t]` is regularly varying at `∞` with index
`α`. -/
theorem karamata_counting_regularlyVarying {x : ℝ} (hx : 0 < x) :
    Tendsto (fun t => counting ρ (t * x) / counting ρ t) atTop (𝓝 (x ^ α)) := by
  have hG : 0 < Real.Gamma (α + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hc := tendsto_counting_div_laplace_of_rv hρ hint hα hRV
  have h33 := karamata_laplace_div_counting hρ hint hα hRV
  have hsc : Tendsto (fun t : ℝ => 1 / (t * x)) atTop (𝓝[>] 0) :=
    tendsto_one_div_atTop_nhdsGT_zero.comp (tendsto_id.atTop_mul_const hx)
  have hA := hc.comp hsc
  have hB := (hRV (1 / x) (one_div_pos.2 hx)).comp tendsto_one_div_atTop_nhdsGT_zero
  have hlim := (hA.mul hB).mul h33
  have hval : 1 / Real.Gamma (α + 1) * (1 / x) ^ (-α) * Real.Gamma (α + 1) = x ^ α := by
    have hGne : Real.Gamma (α + 1) ≠ 0 := hG.ne'
    rw [one_div x, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, neg_neg]
    field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  have hLpos := eventually_laplace_pos_of_rv hRV
  have hFpos : ∀ᶠ t in atTop, 0 < counting ρ t := by
    filter_upwards [h33.eventually (lt_mem_nhds hG)] with t ht
    rcases (counting_nonneg (ρ := ρ) t).eq_or_lt with h0 | h0
    · rw [← h0, div_zero] at ht
      exact absurd ht (lt_irrefl _)
    · exact h0
  filter_upwards [eventually_gt_atTop 0, hFpos, tendsto_one_div_atTop_nhdsGT_zero.eventually hLpos,
    hsc.eventually hLpos] with t ht hF hL1 hL2
  show counting ρ (1 / (1 / (t * x))) / laplace ρ (1 / (t * x)) *
      (laplace ρ (1 / t * (1 / x)) / laplace ρ (1 / t)) * (laplace ρ (1 / t) / counting ρ t) =
    counting ρ (t * x) / counting ρ t
  have hFne : counting ρ t ≠ 0 := hF.ne'
  have hL1ne : laplace ρ (1 / t) ≠ 0 := hL1.ne'
  have hL2ne : laplace ρ (1 / (t * x)) ≠ 0 := hL2.ne'
  rw [one_div_mul_one_div, one_div_one_div]
  field_simp

end

end Lightlike.Karamata
