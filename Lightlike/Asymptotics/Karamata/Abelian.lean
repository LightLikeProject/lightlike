import Lightlike.Asymptotics.Karamata.LayerCake

/-!
# Karamata's theorem: the Abelian direction and the equivalence

Let `ρ` be a measure on `[0, ∞)`, finite on compact sets, with finite Laplace transform `L`, `F t = ρ [0, t]`
and `α ≥ 0`.

* `karamata_abelian`: if `F (t x) / F t → x ^ α` as `t → ∞` for every `x > 0`, then
  `L (τ λ) / L τ → λ ^ (-α)` as `τ → 0⁺` for every `λ > 0`.
* `karamata_iff`: the two regular variation statements are equivalent (Karamata's Tauberian theorem), and
  in either case `L (1/t) / F t → Γ(α + 1)` (`karamata_laplace_div_counting`,
  `tendsto_laplace_div_counting_of_counting_rv`).

The Abelian direction uses `L (1/t) = ∫₀^∞ exp (-s) F (t s) ds` (`laplace_one_div_eq`), a polynomial growth
bound for `F` from the doubling limit (`counting_growth`), and dominated convergence.

## References

* M. Herdegen, G. Liang, O. Shelley, *A continuity theorem for generalised signed measures with an
  application to Karamata's Tauberian theorem*, arXiv:2205.13075v2, Theorem 3.1.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace Lightlike.Karamata

open Lightlike.Tauberian

variable {ρ : Measure ℝ} [IsFiniteMeasureOnCompacts ρ]

/-- Polynomial growth of the counting function from its doubling limit. -/
lemma counting_growth {α : ℝ} (hα : 0 ≤ α)
    (h2 : Tendsto (fun t => counting ρ (t * 2) / counting ρ t) atTop (𝓝 (2 ^ α))) :
    ∃ t0 : ℝ, 0 < t0 ∧ (∀ t, t0 ≤ t → 0 < counting ρ t) ∧
      ∀ t, t0 ≤ t → ∀ s : ℝ, 1 ≤ s →
        counting ρ (t * s) ≤ 2 ^ (α + 1) * s ^ (α + 1) * counting ρ t := by
  have hlt : (2 : ℝ) ^ α < 2 ^ (α + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hpos2 : (0 : ℝ) < 2 ^ α := Real.rpow_pos_of_pos (by norm_num) α
  obtain ⟨a, ha⟩ := eventually_atTop.1
    ((h2.eventually (lt_mem_nhds hpos2)).and (h2.eventually (gt_mem_nhds hlt)))
  have hF : ∀ t, max a 1 ≤ t → 0 < counting ρ t := by
    intro t ht
    have h := (ha t (le_trans (le_max_left _ _) ht)).1
    rcases (counting_nonneg (ρ := ρ) t).eq_or_lt with h0 | h0
    · rw [← h0, div_zero] at h
      exact absurd h (lt_irrefl _)
    · exact h0
  have hdbl : ∀ t, max a 1 ≤ t → counting ρ (t * 2) ≤ 2 ^ (α + 1) * counting ρ t := by
    intro t ht
    have h := (ha t (le_trans (le_max_left _ _) ht)).2
    rw [div_lt_iff₀ (hF t ht)] at h
    exact h.le
  have hpow : ∀ j : ℕ, ∀ t, max a 1 ≤ t →
      counting ρ (t * 2 ^ j) ≤ ((2 : ℝ) ^ (α + 1)) ^ j * counting ρ t := by
    intro j
    induction j with
    | zero =>
      intro t ht
      simp
    | succ j ih =>
      intro t ht
      have ht0 : 0 ≤ t := le_trans zero_le_one (le_trans (le_max_right a 1) ht)
      have ht2 : max a 1 ≤ t * 2 ^ j :=
        le_trans ht (le_mul_of_one_le_right ht0 (one_le_pow₀ (by norm_num)))
      calc counting ρ (t * 2 ^ (j + 1)) = counting ρ (t * 2 ^ j * 2) := by rw [pow_succ, mul_assoc]
        _ ≤ 2 ^ (α + 1) * counting ρ (t * 2 ^ j) := hdbl _ ht2
        _ ≤ 2 ^ (α + 1) * (((2 : ℝ) ^ (α + 1)) ^ j * counting ρ t) :=
            mul_le_mul_of_nonneg_left (ih t ht) (by positivity)
        _ = ((2 : ℝ) ^ (α + 1)) ^ (j + 1) * counting ρ t := by rw [pow_succ]; ring
  refine ⟨max a 1, lt_of_lt_of_le one_pos (le_max_right _ _), hF, ?_⟩
  intro t ht s hs
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  obtain ⟨j, hj1, hj2⟩ : ∃ j : ℕ, s ≤ (2 : ℝ) ^ j ∧ (2 : ℝ) ^ j ≤ 2 * s := by
    refine ⟨⌈Real.logb 2 s⌉₊, ?_, ?_⟩
    · have h1 : Real.logb 2 s ≤ (⌈Real.logb 2 s⌉₊ : ℝ) := Nat.le_ceil _
      rw [← Real.rpow_natCast]
      calc s = (2 : ℝ) ^ (Real.logb 2 s) := (Real.rpow_logb (by norm_num) (by norm_num) hs0).symm
        _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 s⌉₊ : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    · have hlog0 : 0 ≤ Real.logb 2 s := Real.logb_nonneg (by norm_num) hs
      have h1 : (⌈Real.logb 2 s⌉₊ : ℝ) < Real.logb 2 s + 1 := Nat.ceil_lt_add_one hlog0
      rw [← Real.rpow_natCast]
      calc (2 : ℝ) ^ ((⌈Real.logb 2 s⌉₊ : ℝ)) ≤ (2 : ℝ) ^ (Real.logb 2 s + 1) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) h1.le
        _ = 2 * s := by
            rw [Real.rpow_add (by norm_num), Real.rpow_one,
              Real.rpow_logb (by norm_num) (by norm_num) hs0, mul_comm]
  have htpos : 0 < t := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_right a 1)) ht
  calc counting ρ (t * s) ≤ counting ρ (t * 2 ^ j) :=
        counting_mono (mul_le_mul_of_nonneg_left hj1 htpos.le)
    _ ≤ ((2 : ℝ) ^ (α + 1)) ^ j * counting ρ t := hpow j t ht
    _ ≤ 2 ^ (α + 1) * s ^ (α + 1) * counting ρ t := by
        refine mul_le_mul_of_nonneg_right ?_ (counting_nonneg _)
        have e : ((2 : ℝ) ^ (α + 1)) ^ j = ((2 : ℝ) ^ j) ^ (α + 1) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
            Real.rpow_mul (by norm_num), Real.rpow_natCast]
        rw [e, ← Real.mul_rpow (by norm_num) hs0.le]
        exact Real.rpow_le_rpow (by positivity) hj2 (by linarith)

section

variable (hρ : ρ (Iio 0) = 0)
  (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ)
include hρ hint

/-- `L (1/t) = ∫₀^∞ exp (-s) ρ [0, t s] ds`. -/
lemma laplace_one_div_eq {t : ℝ} (ht : 0 < t) :
    laplace ρ (1 / t) = ∫ s in Ioi 0, Real.exp (-s) * counting ρ (t * s) := by
  rw [laplace_eq_integral_counting hρ hint (one_div_pos.2 ht)]
  have h := integral_comp_mul_left_Ioi
    (fun x => 1 / t * Real.exp (-(1 / t) * x) * counting ρ x) 0 ht
  rw [mul_zero, smul_eq_mul] at h
  have h2 : ∫ x in Ioi 0, 1 / t * Real.exp (-(1 / t) * x) * counting ρ x =
      t * ∫ s in Ioi 0, 1 / t * Real.exp (-(1 / t) * (t * s)) * counting ρ (t * s) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  rw [h2, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  show t * (1 / t * Real.exp (-(1 / t) * (t * s)) * counting ρ (t * s)) =
    Real.exp (-s) * counting ρ (t * s)
  have e : -(1 / t) * (t * s) = -s := by
    field_simp
  rw [e]
  field_simp

variable {α : ℝ} (hα : 0 ≤ α)
  (hF : ∀ x : ℝ, 0 < x → Tendsto (fun t => counting ρ (t * x) / counting ρ t) atTop (𝓝 (x ^ α)))
include hα hF

/-- If the counting function is regularly varying with index `α`, then `L (1/t) / ρ [0, t] → Γ(α + 1)`. -/
theorem tendsto_laplace_div_counting_of_counting_rv :
    Tendsto (fun t => laplace ρ (1 / t) / counting ρ t) atTop (𝓝 (Real.Gamma (α + 1))) := by
  obtain ⟨t0, ht0, hpos, hgrow⟩ := counting_growth hα (hF 2 two_pos)
  have hmono : Monotone (counting ρ) := fun _ _ h => counting_mono h
  have hc1 : (1 : ℝ) ≤ 2 ^ (α + 1) := Real.one_le_rpow (by norm_num) (by linarith)
  have hlim : Tendsto (fun t => ∫ s in Ioi 0, Real.exp (-s) * (counting ρ (t * s) / counting ρ t))
      atTop (𝓝 (∫ s in Ioi 0, Real.exp (-s) * s ^ α)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun s => Real.exp (-s) * (2 ^ (α + 1) * (1 + s ^ (α + 1)))) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun t =>
        ((Real.continuous_exp.comp continuous_neg).measurable.mul
          ((hmono.measurable.comp (measurable_const_mul t)).div_const _)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop t0] with t ht
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun s hs => ?_
      have hs0 : (0 : ℝ) < s := hs
      have htpos : 0 < t := lt_of_lt_of_le ht0 ht
      have hFt := hpos t ht
      have hsp : 0 ≤ s ^ (α + 1) := Real.rpow_nonneg hs0.le _
      have hratio : counting ρ (t * s) / counting ρ t ≤ 2 ^ (α + 1) * (1 + s ^ (α + 1)) := by
        rw [div_le_iff₀ hFt]
        rcases le_total s 1 with h1 | h1
        · calc counting ρ (t * s) ≤ counting ρ t :=
                counting_mono (by nlinarith)
            _ = 1 * counting ρ t := (one_mul _).symm
            _ ≤ 2 ^ (α + 1) * (1 + s ^ (α + 1)) * counting ρ t := by
                refine mul_le_mul_of_nonneg_right ?_ hFt.le
                nlinarith
        · calc counting ρ (t * s) ≤ 2 ^ (α + 1) * s ^ (α + 1) * counting ρ t := hgrow t ht s h1
            _ ≤ 2 ^ (α + 1) * (1 + s ^ (α + 1)) * counting ρ t := by
                refine mul_le_mul_of_nonneg_right ?_ hFt.le
                nlinarith
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
        (div_nonneg (counting_nonneg _) (counting_nonneg _)))]
      exact mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le
    · have h1 := (Real.GammaIntegral_convergent one_pos).const_mul ((2 : ℝ) ^ (α + 1))
      have h2 := (Real.GammaIntegral_convergent (by linarith : (0 : ℝ) < α + 2)).const_mul
        ((2 : ℝ) ^ (α + 1))
      have h12 : IntegrableOn (fun s : ℝ => (2 : ℝ) ^ (α + 1) * (Real.exp (-s) * s ^ ((1 : ℝ) - 1)) +
          (2 : ℝ) ^ (α + 1) * (Real.exp (-s) * s ^ (α + 2 - 1))) (Ioi 0) := h1.add h2
      refine IntegrableOn.congr_fun h12 (fun s hs => ?_) measurableSet_Ioi
      have e1 : (1 : ℝ) - 1 = 0 := sub_self 1
      have e2 : α + 2 - 1 = α + 1 := by ring
      show (2 : ℝ) ^ (α + 1) * (Real.exp (-s) * s ^ ((1 : ℝ) - 1)) +
        (2 : ℝ) ^ (α + 1) * (Real.exp (-s) * s ^ (α + 2 - 1)) =
        Real.exp (-s) * (2 ^ (α + 1) * (1 + s ^ (α + 1)))
      rw [e1, e2, Real.rpow_zero]
      ring
    · rw [ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall fun s hs => (hF s hs).const_mul _
  have hG : ∫ s in Ioi (0 : ℝ), Real.exp (-s) * s ^ α = Real.Gamma (α + 1) := by
    rw [Real.Gamma_eq_integral (by linarith), add_sub_cancel_right]
  rw [hG] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop t0] with t ht
  have htpos : 0 < t := lt_of_lt_of_le ht0 ht
  show ∫ s in Ioi 0, Real.exp (-s) * (counting ρ (t * s) / counting ρ t) =
    laplace ρ (1 / t) / counting ρ t
  rw [laplace_one_div_eq hρ hint htpos, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  show Real.exp (-s) * (counting ρ (t * s) / counting ρ t) =
    Real.exp (-s) * counting ρ (t * s) / counting ρ t
  rw [mul_div_assoc]

/-- **Karamata's theorem, the Abelian direction (3.2) ⇒ (3.1).** If the counting function `t ↦ ρ [0, t]`
is regularly varying at `∞` with index `α ≥ 0`, then the Laplace transform of `ρ` is regularly varying at
`0⁺` with index `-α`. -/
theorem karamata_abelian {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun τ => laplace ρ (τ * lam) / laplace ρ τ) (𝓝[>] 0) (𝓝 (lam ^ (-α))) := by
  obtain ⟨t0, ht0, hpos, -⟩ := counting_growth hα (hF 2 two_pos)
  have hR := tendsto_laplace_div_counting_of_counting_rv hρ hint hα hF
  have hG : 0 < Real.Gamma (α + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hinv : Tendsto (fun τ : ℝ => 1 / τ) (𝓝[>] 0) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
  have hinv2 : Tendsto (fun τ : ℝ => 1 / (τ * lam)) (𝓝[>] 0) atTop := by
    have h := hinv.comp (tendsto_const_mul_nhdsGT_zero hlam)
    refine h.congr fun τ => ?_
    show 1 / (lam * τ) = 1 / (τ * lam)
    rw [mul_comm]
  have h1 := hR.comp hinv2
  have h2 := (hF (1 / lam) (one_div_pos.2 hlam)).comp hinv
  have h3 := (hR.comp hinv).inv₀ hG.ne'
  have hlim := (h1.mul h2).mul h3
  have hval : Real.Gamma (α + 1) * (1 / lam) ^ α * (Real.Gamma (α + 1))⁻¹ = lam ^ (-α) := by
    have hGne : Real.Gamma (α + 1) ≠ 0 := hG.ne'
    rw [one_div, Real.inv_rpow hlam.le, Real.rpow_neg hlam.le]
    field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hinv.eventually (eventually_ge_atTop t0),
    hinv2.eventually (eventually_ge_atTop t0)] with τ hτ h4 h5
  have hτ' : (0 : ℝ) < τ := hτ
  have hF1 := hpos _ h4
  have hF2 := hpos _ h5
  have hL : 0 < laplace ρ τ :=
    lt_of_lt_of_le (mul_pos hF1 (Real.exp_pos _)) (counting_mul_exp_le hint hτ' (by positivity))
  show laplace ρ (1 / (1 / (τ * lam))) / counting ρ (1 / (τ * lam)) *
      (counting ρ (1 / τ * (1 / lam)) / counting ρ (1 / τ)) *
      (laplace ρ (1 / (1 / τ)) / counting ρ (1 / τ))⁻¹ = laplace ρ (τ * lam) / laplace ρ τ
  have hF1ne : counting ρ (1 / τ) ≠ 0 := hF1.ne'
  have hF2ne : counting ρ (1 / (τ * lam)) ≠ 0 := hF2.ne'
  have hLne : laplace ρ τ ≠ 0 := hL.ne'
  rw [one_div_one_div, one_div_one_div, one_div_mul_one_div, inv_div]
  field_simp

end

/-- **Karamata's Tauberian theorem** (Herdegen–Liang–Shelley, Theorem 3.1). For a measure `ρ` on `[0, ∞)`,
finite on compact sets, with finite Laplace transform `L`, and `α ≥ 0`: the Laplace transform is regularly
varying at `0⁺` with index `-α` if and only if the counting function `t ↦ ρ [0, t]` is regularly varying at
`∞` with index `α`; and in either case `L (1/t) ~ ρ [0, t] Γ(α + 1)` as `t → ∞`. -/
theorem karamata_iff (hρ : ρ (Iio 0) = 0)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ) {α : ℝ} (hα : 0 ≤ α) :
    ((∀ lam : ℝ, 0 < lam →
        Tendsto (fun τ => laplace ρ (τ * lam) / laplace ρ τ) (𝓝[>] 0) (𝓝 (lam ^ (-α)))) ↔
      ∀ x : ℝ, 0 < x → Tendsto (fun t => counting ρ (t * x) / counting ρ t) atTop (𝓝 (x ^ α))) ∧
    ((∀ lam : ℝ, 0 < lam →
        Tendsto (fun τ => laplace ρ (τ * lam) / laplace ρ τ) (𝓝[>] 0) (𝓝 (lam ^ (-α)))) →
      Tendsto (fun t => laplace ρ (1 / t) / counting ρ t) atTop (𝓝 (Real.Gamma (α + 1)))) :=
  ⟨⟨fun h x hx => karamata_counting_regularlyVarying hρ hint hα h hx,
    fun h lam hlam => karamata_abelian hρ hint hα h hlam⟩,
    fun h => karamata_laplace_div_counting hρ hint hα h⟩

end Lightlike.Karamata
