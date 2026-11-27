module

public import Mathlib

/-!
# Pythagoras for finite sums of mutually orthogonal `L²` functions

For complex functions `F_i ∈ L²(μ)` with `∫ F_i conj(F_k) dμ = 0` for `i ≠ k`,
`∫ |Σ_i F_i|² dμ = Σ_i ∫ |F_i|² dμ` (`lintegral_norm_sq_sum_of_orth`), stated with `lintegral`s of `ofReal ‖·‖²`.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma integrable_norm_sq_of_memLp {F : α → ℂ} (hF : MemLp F 2 μ) : Integrable (fun x => ‖F x‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF

lemma integrable_mul_conj_of_memLp {F G : α → ℂ} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    Integrable (fun x => F x * (starRingEnd ℂ) (G x)) μ := by
  have hG' : MemLp (fun x => (starRingEnd ℂ) (G x)) 2 μ := hG.star
  exact hF.integrable_mul hG'

/-- Pythagoras for two orthogonal `L²` functions. -/
lemma lintegral_norm_sq_add_of_orth {F G : α → ℂ} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (h : ∫ x, F x * (starRingEnd ℂ) (G x) ∂μ = 0) :
    ∫⁻ x, ENNReal.ofReal (‖F x + G x‖ ^ 2) ∂μ =
      ∫⁻ x, ENNReal.ofReal (‖F x‖ ^ 2) ∂μ + ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2) ∂μ := by
  have hiF := integrable_norm_sq_of_memLp hF
  have hiG := integrable_norm_sq_of_memLp hG
  have hiFG := integrable_mul_conj_of_memLp hF hG
  have hsum : Integrable (fun x => ‖F x + G x‖ ^ 2) μ := integrable_norm_sq_of_memLp (hF.add hG)
  have hpt : ∀ x, ‖F x + G x‖ ^ 2 = ‖F x‖ ^ 2 + ‖G x‖ ^ 2 + 2 * (F x * (starRingEnd ℂ) (G x)).re := by
    intro x
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
  have hre : Integrable (fun x => (F x * (starRingEnd ℂ) (G x)).re) μ := hiFG.re
  have hint : ∫ x, ‖F x + G x‖ ^ 2 ∂μ = ∫ x, ‖F x‖ ^ 2 ∂μ + ∫ x, ‖G x‖ ^ 2 ∂μ := by
    have hsum2 : Integrable (fun x => ‖F x‖ ^ 2 + ‖G x‖ ^ 2) μ := hiF.add hiG
    simp_rw [hpt]
    have hre0 : ∫ x, (F x * (starRingEnd ℂ) (G x)).re ∂μ = (∫ x, F x * (starRingEnd ℂ) (G x) ∂μ).re :=
      integral_re hiFG
    rw [integral_add hsum2 (hre.const_mul 2), integral_add hiF hiG, integral_const_mul, hre0, h]
    simp
  have hnn : ∀ f : α → ℂ, 0 ≤ᵐ[μ] fun x => ‖f x‖ ^ 2 := fun f => ae_of_all _ (fun x => by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hsum (hnn _), ← ofReal_integral_eq_lintegral_ofReal hiF (hnn _),
    ← ofReal_integral_eq_lintegral_ofReal hiG (hnn _), hint,
    ENNReal.ofReal_add (integral_nonneg (fun x => by positivity)) (integral_nonneg (fun x => by positivity))]

/-- **Pythagoras for finite sums of orthogonal `L²` functions.** -/
theorem lintegral_norm_sq_sum_of_orth {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → α → ℂ)
    (hF : ∀ i, MemLp (F i) 2 μ)
    (horth : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → ∫ x, F i x * (starRingEnd ℂ) (F k x) ∂μ = 0) :
    ∫⁻ x, ENNReal.ofReal (‖∑ i ∈ s, F i x‖ ^ 2) ∂μ = ∑ i ∈ s, ∫⁻ x, ENNReal.ofReal (‖F i x‖ ^ 2) ∂μ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hs : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → ∫ x, F i x * (starRingEnd ℂ) (F k x) ∂μ = 0 :=
      fun i hi k hk hik => horth i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk) hik
    have hmemsum : MemLp (fun x => ∑ i ∈ s, F i x) 2 μ := by
      have := memLp_finsetSum' s (fun i _ => hF i)
      convert this using 1
      funext x
      simp [Finset.sum_apply]
    have horth' : ∫ x, F a x * (starRingEnd ℂ) (∑ i ∈ s, F i x) ∂μ = 0 := by
      simp_rw [map_sum, Finset.mul_sum]
      rw [integral_finsetSum]
      · refine Finset.sum_eq_zero (fun i hi => ?_)
        exact horth a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (fun h => ha (h ▸ hi))
      · intro i _
        exact integrable_mul_conj_of_memLp (hF a) (hF i)
    have := lintegral_norm_sq_add_of_orth (hF a) hmemsum horth'
    simp only [Finset.sum_insert ha]
    rw [this, ih hs]

lemma lintegral_ofReal_norm_sq_eq {F : α → ℂ} (hF : MemLp F 2 μ) :
    ∫⁻ x, ENNReal.ofReal (‖F x‖ ^ 2) ∂μ = ENNReal.ofReal (∫ x, ‖F x‖ ^ 2 ∂μ) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_of_memLp hF)
    (ae_of_all _ (fun x => by positivity))).symm

/-- `‖x + y‖² ≤ (1 + ε) ‖x‖² + (1 + ε⁻¹) ‖y‖²`. -/
lemma norm_add_sq_le (x y : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ‖x + y‖ ^ 2 ≤ (1 + ε) * ‖x‖ ^ 2 + (1 + ε⁻¹) * ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 2 * ‖x‖ * ‖y‖ ≤ ε * ‖x‖ ^ 2 + ε⁻¹ * ‖y‖ ^ 2 := by
    have h4 : 2 * ‖x‖ * ‖y‖ * ε ≤ ε ^ 2 * ‖x‖ ^ 2 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg (ε * ‖x‖ - ‖y‖)]
    have h5 : ε * ‖x‖ ^ 2 + ε⁻¹ * ‖y‖ ^ 2 = (ε ^ 2 * ‖x‖ ^ 2 + ‖y‖ ^ 2) / ε := by field_simp
    rw [h5, le_div_iff₀ hε]
    exact h4
  nlinarith [h2, h3]

/-- The `ε`-triangle inequality for squared `L²` norms. -/
lemma integral_norm_sq_add_le {F G : α → ℂ} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) {ε : ℝ} (hε : 0 < ε) :
    ∫ x, ‖F x + G x‖ ^ 2 ∂μ ≤ (1 + ε) * ∫ x, ‖F x‖ ^ 2 ∂μ + (1 + ε⁻¹) * ∫ x, ‖G x‖ ^ 2 ∂μ := by
  have hiF := integrable_norm_sq_of_memLp hF
  have hiG := integrable_norm_sq_of_memLp hG
  have hsum : Integrable (fun x => ‖F x + G x‖ ^ 2) μ := integrable_norm_sq_of_memLp (hF.add hG)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hiF.const_mul _) (hiG.const_mul _)]
  exact integral_mono hsum ((hiF.const_mul _).add (hiG.const_mul _))
    (fun x => norm_add_sq_le (F x) (G x) hε)

end Lightlike.Lorentz.SL2RPlancherel
