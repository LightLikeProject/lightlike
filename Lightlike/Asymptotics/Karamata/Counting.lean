import Lightlike.Asymptotics.Karamata.Functional

/-!
# Karamata's method: from continuous test functions to the counting function

With `gStep u = u⁻¹` for `u ≥ e⁻¹` and `0` otherwise, `weighted ρ β gStep = ρ [0, 1/β]`
(`weighted_gStep`). The step function is squeezed between the continuous functions `gLo n ≤ gStep ≤ gUp n`,
which converge to it away from `u = e⁻¹`. So if the moment ratios `L ((k+1) β) / L β` converge to the moments
of a finite measure `ν` on `[0, ∞)` without an atom at `t = 1`, then
`ρ [0, 1/β] / L β → ∫ gStep (exp (-t)) dν` as `β → 0⁺` (`tendsto_counting_div_laplace`).

Supporting lemmas for Karamata's Tauberian theorem; no catalogue entry.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace Lightlike.Karamata

open Lightlike.Tauberian

/-- The step test function of Karamata's method: `u⁻¹` for `u ≥ e⁻¹`, and `0` below. -/
def gStep (u : ℝ) : ℝ := if Real.exp (-1) ≤ u then 1 / u else 0

/-- A continuous cutoff equal to `1` for `u ≥ e⁻¹` and to `0` for `u ≤ e⁻¹ - 1/(n+1)`. -/
def cutUp (n : ℕ) (u : ℝ) : ℝ := max 0 (min 1 (1 + ((n : ℝ) + 1) * (u - Real.exp (-1))))

/-- A continuous cutoff equal to `0` for `u ≤ e⁻¹` and to `1` for `u ≥ e⁻¹ + 1/(n+1)`. -/
def cutLo (n : ℕ) (u : ℝ) : ℝ := max 0 (min 1 (((n : ℝ) + 1) * (u - Real.exp (-1))))

/-- The continuous function `u ↦ 1 / max u (e⁻¹/2)`, equal to `u⁻¹` for `u ≥ e⁻¹`. -/
def invTrunc (u : ℝ) : ℝ := (max u (Real.exp (-1) / 2))⁻¹

/-- The upper continuous approximation of `gStep`. -/
def gUp (n : ℕ) (u : ℝ) : ℝ := cutUp n u * invTrunc u

/-- The lower continuous approximation of `gStep`. -/
def gLo (n : ℕ) (u : ℝ) : ℝ := cutLo n u * invTrunc u

lemma half_exp_pos : (0 : ℝ) < Real.exp (-1) / 2 := by positivity

lemma continuous_invTrunc : Continuous invTrunc :=
  (continuous_id.max continuous_const).inv₀ fun u =>
    (lt_of_lt_of_le half_exp_pos (le_max_right u _)).ne'

lemma continuous_gUp (n : ℕ) : Continuous (gUp n) := by
  unfold gUp cutUp
  exact (continuous_const.max (continuous_const.min (by fun_prop))).mul continuous_invTrunc

lemma continuous_gLo (n : ℕ) : Continuous (gLo n) := by
  unfold gLo cutLo
  exact (continuous_const.max (continuous_const.min (by fun_prop))).mul continuous_invTrunc

lemma invTrunc_pos (u : ℝ) : 0 < invTrunc u :=
  inv_pos.2 (lt_of_lt_of_le half_exp_pos (le_max_right u _))

lemma invTrunc_le (u : ℝ) : invTrunc u ≤ 2 * Real.exp 1 := by
  unfold invTrunc
  rw [inv_le_comm₀ (lt_of_lt_of_le half_exp_pos (le_max_right u _)) (by positivity)]
  refine le_trans (le_of_eq ?_) (le_max_right u _)
  rw [Real.exp_neg]
  field_simp

lemma invTrunc_of_le {u : ℝ} (hu : Real.exp (-1) ≤ u) : invTrunc u = 1 / u := by
  unfold invTrunc
  rw [max_eq_left (by linarith [half_exp_pos]), one_div]

lemma cutUp_mem (n : ℕ) (u : ℝ) : 0 ≤ cutUp n u ∧ cutUp n u ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma cutLo_mem (n : ℕ) (u : ℝ) : 0 ≤ cutLo n u ∧ cutLo n u ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma cutUp_of_le (n : ℕ) {u : ℝ} (hu : Real.exp (-1) ≤ u) : cutUp n u = 1 := by
  unfold cutUp
  have h : (0 : ℝ) ≤ ((n : ℝ) + 1) * (u - Real.exp (-1)) := mul_nonneg (by positivity) (by linarith)
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

lemma cutLo_of_lt (n : ℕ) {u : ℝ} (hu : u < Real.exp (-1)) : cutLo n u = 0 := by
  unfold cutLo
  have h : ((n : ℝ) + 1) * (u - Real.exp (-1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  rw [min_eq_right (by linarith), max_eq_left h]

lemma gLo_le_gStep (n : ℕ) (u : ℝ) : gLo n u ≤ gStep u := by
  unfold gLo gStep
  by_cases hu : Real.exp (-1) ≤ u
  · rw [if_pos hu, invTrunc_of_le hu]
    have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hu
    calc cutLo n u * (1 / u) ≤ 1 * (1 / u) :=
          mul_le_mul_of_nonneg_right (cutLo_mem n u).2 (by positivity)
      _ = 1 / u := one_mul _
  · rw [if_neg hu, cutLo_of_lt n (not_le.1 hu), zero_mul]

lemma gStep_le_gUp (n : ℕ) (u : ℝ) : gStep u ≤ gUp n u := by
  unfold gUp gStep
  by_cases hu : Real.exp (-1) ≤ u
  · rw [if_pos hu, invTrunc_of_le hu, cutUp_of_le n hu, one_mul]
  · rw [if_neg hu]
    exact mul_nonneg (cutUp_mem n u).1 (invTrunc_pos u).le

lemma abs_gUp_le (n : ℕ) (u : ℝ) : |gUp n u| ≤ 2 * Real.exp 1 := by
  unfold gUp
  rw [abs_of_nonneg (mul_nonneg (cutUp_mem n u).1 (invTrunc_pos u).le)]
  calc cutUp n u * invTrunc u ≤ 1 * invTrunc u :=
        mul_le_mul_of_nonneg_right (cutUp_mem n u).2 (invTrunc_pos u).le
    _ ≤ 2 * Real.exp 1 := by rw [one_mul]; exact invTrunc_le u

lemma abs_gLo_le (n : ℕ) (u : ℝ) : |gLo n u| ≤ 2 * Real.exp 1 := by
  unfold gLo
  rw [abs_of_nonneg (mul_nonneg (cutLo_mem n u).1 (invTrunc_pos u).le)]
  calc cutLo n u * invTrunc u ≤ 1 * invTrunc u :=
        mul_le_mul_of_nonneg_right (cutLo_mem n u).2 (invTrunc_pos u).le
    _ ≤ 2 * Real.exp 1 := by rw [one_mul]; exact invTrunc_le u

/-- Away from `u = e⁻¹` the upper approximations are eventually equal to `gStep`. -/
lemma tendsto_gUp {u : ℝ} (hu : u ≠ Real.exp (-1)) :
    Tendsto (fun n : ℕ => gUp n u) atTop (𝓝 (gStep u)) := by
  rcases lt_or_gt_of_ne hu with h | h
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (Real.exp (-1) - u))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hd : 0 < Real.exp (-1) - u := by linarith
    have hn' : 1 / (Real.exp (-1) - u) < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h1 : 1 < ((n : ℝ) + 1) * (Real.exp (-1) - u) := by
      rw [div_lt_iff₀ hd] at hn'
      exact hn'
    have hc : cutUp n u = 0 := by
      unfold cutUp
      have h2 : 1 + ((n : ℝ) + 1) * (u - Real.exp (-1)) ≤ 0 := by nlinarith
      rw [min_eq_right (by linarith), max_eq_left h2]
    show gStep u = gUp n u
    unfold gUp gStep
    rw [if_neg (not_le.2 h), hc, zero_mul]
  · refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => ?_)
    show gStep u = gUp n u
    unfold gUp gStep
    rw [if_pos h.le, invTrunc_of_le h.le, cutUp_of_le n h.le, one_mul]

/-- Away from `u = e⁻¹` the lower approximations are eventually equal to `gStep`. -/
lemma tendsto_gLo {u : ℝ} (hu : u ≠ Real.exp (-1)) :
    Tendsto (fun n : ℕ => gLo n u) atTop (𝓝 (gStep u)) := by
  rcases lt_or_gt_of_ne hu with h | h
  · refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => ?_)
    show gStep u = gLo n u
    unfold gLo gStep
    rw [if_neg (not_le.2 h), cutLo_of_lt n h, zero_mul]
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (u - Real.exp (-1)))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hd : 0 < u - Real.exp (-1) := by linarith
    have hn' : 1 / (u - Real.exp (-1)) < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h1 : 1 < ((n : ℝ) + 1) * (u - Real.exp (-1)) := by
      rw [div_lt_iff₀ hd] at hn'
      exact hn'
    have hc : cutLo n u = 1 := by
      unfold cutLo
      rw [min_eq_left h1.le, max_eq_right zero_le_one]
    show gStep u = gLo n u
    unfold gLo gStep
    rw [if_pos h.le, invTrunc_of_le h.le, hc, one_mul]

variable {ρ : Measure ℝ}

/-- For `x ≥ 0` the weighted step function is the indicator of `[0, 1/β]`. -/
lemma exp_mul_gStep {β x : ℝ} (hβ : 0 < β) (hx : 0 ≤ x) :
    Real.exp (-β * x) * gStep (Real.exp (-β * x)) =
      (Icc (0 : ℝ) (1 / β)).indicator (fun _ => (1 : ℝ)) x := by
  unfold gStep
  by_cases h : x ≤ 1 / β
  · have h1 : Real.exp (-1) ≤ Real.exp (-β * x) := by
      refine Real.exp_le_exp.2 ?_
      rw [le_div_iff₀ hβ] at h
      linarith
    rw [if_pos h1, indicator_of_mem (show x ∈ Icc (0 : ℝ) (1 / β) from ⟨hx, h⟩),
      mul_one_div, div_self (Real.exp_pos _).ne']
  · have h1 : ¬ Real.exp (-1) ≤ Real.exp (-β * x) := by
      rw [Real.exp_le_exp]
      have h2 := not_le.1 h
      rw [div_lt_iff₀ hβ] at h2
      linarith
    rw [if_neg h1, mul_zero, indicator_of_notMem (fun hmem : x ∈ Icc (0 : ℝ) (1 / β) => h hmem.2)]

section

variable [IsFiniteMeasureOnCompacts ρ] (hρ : ρ (Iio 0) = 0)
  (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ)
include hρ hint

lemma integrable_indicator_Icc (X : ℝ) :
    Integrable ((Icc (0 : ℝ) X).indicator (fun _ => (1 : ℝ))) ρ :=
  (integrable_indicator_iff measurableSet_Icc).2
    (integrableOn_const (isCompact_Icc.measure_lt_top (μ := ρ)).ne)

omit hint in
lemma counting_eq_integral (X : ℝ) :
    counting ρ X = ∫ x, (Icc (0 : ℝ) X).indicator (fun _ => (1 : ℝ)) x ∂ρ := by
  rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one]
  rfl

/-- `weighted ρ β (gLo n) ≤ ρ [0, 1/β] ≤ weighted ρ β (gUp n)`. -/
lemma weighted_gLo_le_counting {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    weighted ρ β (gLo n) ≤ counting ρ (1 / β) := by
  rw [counting_eq_integral hρ]
  unfold weighted
  refine integral_mono_ae (integrable_weighted hρ hint hβ (continuous_gLo n))
    (integrable_indicator_Icc hρ hint _) ?_
  filter_upwards [ae_nonneg_of_Iio hρ] with x hx
  rw [← exp_mul_gStep hβ hx]
  exact mul_le_mul_of_nonneg_left (gLo_le_gStep n _) (Real.exp_pos _).le

lemma counting_le_weighted_gUp {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    counting ρ (1 / β) ≤ weighted ρ β (gUp n) := by
  rw [counting_eq_integral hρ]
  unfold weighted
  refine integral_mono_ae (integrable_indicator_Icc hρ hint _)
    (integrable_weighted hρ hint hβ (continuous_gUp n)) ?_
  filter_upwards [ae_nonneg_of_Iio hρ] with x hx
  rw [← exp_mul_gStep hβ hx]
  exact mul_le_mul_of_nonneg_left (gStep_le_gUp n _) (Real.exp_pos _).le

variable {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0) (hν1 : ν {1} = 0)
  (hmom : ∀ k : ℕ, Tendsto (fun β => laplace ρ ((k + 1) * β) / laplace ρ β) (𝓝[>] 0)
    (𝓝 (∫ t, Real.exp (-t) ^ k ∂ν)))
include hν hν1 hmom

omit [IsFiniteMeasureOnCompacts ρ] hρ hint hν hmom in
lemma ae_exp_neg_ne : ∀ᵐ t ∂ν, Real.exp (-t) ≠ Real.exp (-1) := by
  have h : ∀ᵐ t ∂ν, t ≠ 1 := by
    rw [ae_iff]
    have hs : {t : ℝ | ¬ t ≠ 1} = {1} := by
      ext t
      simp
    rw [hs]
    exact hν1
  filter_upwards [h] with t ht hexp
  exact ht (by linarith [Real.exp_injective hexp])

omit [IsFiniteMeasureOnCompacts ρ] hρ hint hν hmom in
lemma tendsto_integral_gUp :
    Tendsto (fun n : ℕ => ∫ t, gUp n (Real.exp (-t)) ∂ν) atTop
      (𝓝 (∫ t, gStep (Real.exp (-t)) ∂ν)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => 2 * Real.exp 1) (fun n => ?_)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun t => ?_) ?_
  · exact ((continuous_gUp n).comp (Real.continuous_exp.comp continuous_neg)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_gUp_le n _
  · filter_upwards [ae_exp_neg_ne hν1] with t ht
    exact tendsto_gUp ht

omit [IsFiniteMeasureOnCompacts ρ] hρ hint hν hmom in
lemma tendsto_integral_gLo :
    Tendsto (fun n : ℕ => ∫ t, gLo n (Real.exp (-t)) ∂ν) atTop
      (𝓝 (∫ t, gStep (Real.exp (-t)) ∂ν)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => 2 * Real.exp 1) (fun n => ?_)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun t => ?_) ?_
  · exact ((continuous_gLo n).comp (Real.continuous_exp.comp continuous_neg)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_gLo_le n _
  · filter_upwards [ae_exp_neg_ne hν1] with t ht
    exact tendsto_gLo ht

/-- **Karamata's method.** If the moment ratios `L ((k+1) β) / L β` of the Laplace transform of `ρ` converge,
as `β → 0⁺`, to the moments `∫ exp (-t) ^ k dν` of a finite measure `ν` on `[0, ∞)` with no atom at `1`,
then `ρ [0, 1/β] / L β → ∫ gStep (exp (-t)) dν`. -/
theorem tendsto_counting_div_laplace (hpos : ∀ᶠ β in 𝓝[>] (0 : ℝ), 0 < laplace ρ β) :
    Tendsto (fun β => counting ρ (1 / β) / laplace ρ β) (𝓝[>] 0)
      (𝓝 (∫ t, gStep (Real.exp (-t)) ∂ν)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨n, hn⟩ := ((tendsto_integral_gLo hν1).eventually (lt_mem_nhds ha)).exists
    have hlim := tendsto_weighted_continuous hρ hint hν hmom hpos (continuous_gLo n)
    filter_upwards [hlim.eventually (lt_mem_nhds hn), hpos, self_mem_nhdsWithin] with β h1 hL hβ
    exact h1.trans_le (div_le_div_of_nonneg_right (weighted_gLo_le_counting hρ hint hβ n) hL.le)
  · intro b hb
    obtain ⟨n, hn⟩ := ((tendsto_integral_gUp hν1).eventually (gt_mem_nhds hb)).exists
    have hlim := tendsto_weighted_continuous hρ hint hν hmom hpos (continuous_gUp n)
    filter_upwards [hlim.eventually (gt_mem_nhds hn), hpos, self_mem_nhdsWithin] with β h1 hL hβ
    exact lt_of_le_of_lt
      (div_le_div_of_nonneg_right (counting_le_weighted_gUp hρ hint hβ n) hL.le) h1

end

end Lightlike.Karamata
