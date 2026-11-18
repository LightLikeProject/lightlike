import Lightlike.Asymptotics.Tauberian.CrossingBound
import Lightlike.Asymptotics.Tauberian.Majorant
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The main term of the local bound

With `β = √(a/Δ)` the tangent-line inequality `2 √(a x) ≤ β (x + Δ)` gives
`crossingDensity a x · e^{-β (x - Δ)} ≤ 2 √2 a z^{-3/2} e^{2 √(a Δ)}`, `z = 2 √(a x)`, for all `x > 0`:
the exponent never exceeds its value at `x = Δ` (MZ (5.10), the saddle at `Δ' = Δ`).
-/

open Real

noncomputable section

namespace Lightlike.Tauberian

/-- The tangent line of `x ↦ 2 √(a x)` at `Δ`: `2 √(a x) ≤ β (x + Δ)` with `β = √(a / Δ)`. -/
lemma two_sqrt_le {a Δ x : ℝ} (ha : 0 < a) (hΔ : 0 < Δ) (hx : 0 ≤ x) :
    2 * Real.sqrt (a * x) ≤ Real.sqrt (a / Δ) * (x + Δ) := by
  have hr : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have ht : 0 < Real.sqrt Δ := Real.sqrt_pos.2 hΔ
  rw [Real.sqrt_mul ha.le, Real.sqrt_div ha.le]
  set s := Real.sqrt x
  set t := Real.sqrt Δ
  set r := Real.sqrt a
  have hx2 : x = s ^ 2 := (Real.sq_sqrt hx).symm
  have hΔ2 : Δ = t ^ 2 := (Real.sq_sqrt hΔ.le).symm
  rw [hx2, hΔ2]
  rw [div_mul_eq_mul_div, le_div_iff₀ ht]
  nlinarith [mul_nonneg hr (sq_nonneg (s - t))]

/-- The pointwise bound of the main term. -/
lemma crossingDensity_mul_exp_le {a Δ x : ℝ} (ha : 0 < a) (hΔ : 0 < Δ) (hx : 0 < x) :
    crossingDensity a x * Real.exp (-(Real.sqrt (a / Δ)) * (x - Δ)) ≤
      (2 * Real.sqrt 2 * a / (2 * Real.sqrt (a * x))) *
        (Real.exp (2 * Real.sqrt (a * Δ)) / Real.sqrt (2 * Real.sqrt (a * x))) := by
  set z := 2 * Real.sqrt (a * x) with hz
  have hzpos : 0 < z := by positivity
  have h1 := crossingDensity_le ha hx
  have hβΔ : Real.sqrt (a / Δ) * Δ = Real.sqrt (a * Δ) := by
    rw [Real.sqrt_div ha.le, Real.sqrt_mul ha.le]
    have : Real.sqrt Δ * Real.sqrt Δ = Δ := Real.mul_self_sqrt hΔ.le
    field_simp
    nlinarith [this]
  have hexp : Real.exp z * Real.exp (-(Real.sqrt (a / Δ)) * (x - Δ)) ≤ Real.exp (2 * Real.sqrt (a * Δ)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := two_sqrt_le ha hΔ hx.le
    nlinarith [this, hβΔ]
  have hC : 0 ≤ 2 * Real.sqrt 2 * a / z := by positivity
  calc crossingDensity a x * Real.exp (-(Real.sqrt (a / Δ)) * (x - Δ))
      ≤ ((2 * Real.sqrt 2 * a / z) * (Real.exp z / Real.sqrt z)) *
          Real.exp (-(Real.sqrt (a / Δ)) * (x - Δ)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (2 * Real.sqrt 2 * a / z) * ((Real.exp z * Real.exp (-(Real.sqrt (a / Δ)) * (x - Δ))) / Real.sqrt z) := by ring
    _ ≤ (2 * Real.sqrt 2 * a / z) * (Real.exp (2 * Real.sqrt (a * Δ)) / Real.sqrt z) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hexp (Real.sqrt_nonneg _)) hC

/-- `sinc(y)⁴ ≤ 2 / (1 + y²)`. -/
lemma sinc_pow_four_le (y : ℝ) : Real.sinc y ^ 4 ≤ 2 / (1 + y ^ 2) := by
  have h1 : |Real.sinc y| ≤ 1 := Real.abs_sinc_le_one y
  have h2 : Real.sinc y ^ 4 = |Real.sinc y| ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  rw [h2]
  by_cases hy : |y| ≤ 1
  · have : |Real.sinc y| ^ 4 ≤ 1 := pow_le_one₀ (abs_nonneg _) h1
    refine this.trans ?_
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_abs y, abs_nonneg y]
  · push Not at hy
    have hy0 : y ≠ 0 := by intro h; rw [h] at hy; simp at hy; linarith
    have h3 : |Real.sinc y| ≤ 1 / |y| := by
      rw [Real.sinc_of_ne_zero hy0, abs_div]
      have : |Real.sin y| ≤ 1 := Real.abs_sin_le_one y
      exact div_le_div_of_nonneg_right this (abs_nonneg y)
    have h4 : |Real.sinc y| ^ 4 ≤ (1 / |y|) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) h3 4
    refine h4.trans ?_
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have : |y| ^ 4 = (y ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]
    rw [this]
    nlinarith [sq_nonneg (y ^ 2 - 1), sq_abs y, one_lt_sq_iff_one_lt_abs y |>.2 hy]

open MeasureTheory Set in
/-- **The elementary integral estimate** of the local bound (MZ (5.11)-(5.17), in the form needed
here): if `0 ≤ H y ≤ M / (1 + y²)` then `∫₀^∞ x^{-3/4} H (b (x - Δ)) dx ≤ C Δ^{-3/4}` for `Δ ≥ 1`. -/
theorem integral_rpow_mul_le {H : ℝ → ℝ} {M b : ℝ} (hM : 0 ≤ M) (hb : 0 < b)
    (hH0 : ∀ y, 0 ≤ H y) (hHM : ∀ y, H y ≤ M / (1 + y ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Δ : ℝ, 1 ≤ Δ →
      ∫ x in Ioi (0 : ℝ), x ^ (-(3 / 4 : ℝ)) * H (b * (x - Δ)) ≤ C * Δ ^ (-(3 / 4 : ℝ)) := by
  set J : ℝ := ∫ x : ℝ, (1 + (b * x) ^ 2)⁻¹ with hJ
  have hJint : Integrable (fun x : ℝ => (1 + (b * x) ^ 2)⁻¹) := by
    have := (integrable_inv_one_add_sq).comp_mul_left' hb.ne'
    simpa using this
  have hJ0 : 0 ≤ J := integral_nonneg fun x => by positivity
  refine ⟨16 * M / b ^ 2 + 2 * M * J, by positivity, fun Δ hΔ => ?_⟩
  have hΔ0 : 0 < Δ := by linarith
  set c1 : ℝ := 4 * M / (b ^ 2 * Δ ^ 2) with hc1
  set g1 : ℝ → ℝ := fun x => (Ioc (0 : ℝ) (Δ / 2)).indicator (fun x => c1 * x ^ (-(3 / 4 : ℝ))) x with hg1
  set g2 : ℝ → ℝ := fun x => 2 * Δ ^ (-(3 / 4 : ℝ)) * M * (1 + (b * (x - Δ)) ^ 2)⁻¹ with hg2
  have hg2int : Integrable g2 := by
    have := (hJint.comp_sub_right Δ).const_mul (2 * Δ ^ (-(3 / 4 : ℝ)) * M)
    simpa [hg2] using this
  have hg1int : Integrable g1 := by
    rw [hg1, integrable_indicator_iff measurableSet_Ioc]
    have h0 : IntervalIntegrable (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) volume 0 (Δ / 2) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    exact (h0.1).const_mul c1
  have hc10 : 0 ≤ c1 := by positivity
  have hg10 : ∀ x, 0 ≤ g1 x := fun x => by
    simp only [hg1]
    exact Set.indicator_nonneg (fun y hy => mul_nonneg hc10 (Real.rpow_nonneg hy.1.le _)) x
  have hg20 : ∀ x, 0 ≤ g2 x := fun x => by simp only [hg2]; positivity
  have hdom : ∀ x ∈ Ioi (0 : ℝ), x ^ (-(3 / 4 : ℝ)) * H (b * (x - Δ)) ≤ g1 x + g2 x := by
    intro x hx
    have hx0 : 0 < x := hx
    have hxr : 0 ≤ x ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hx0.le _
    by_cases hxh : x ≤ Δ / 2
    · have hmem : x ∈ Ioc (0 : ℝ) (Δ / 2) := ⟨hx0, hxh⟩
      have hg1x : g1 x = c1 * x ^ (-(3 / 4 : ℝ)) := by simp only [hg1, Set.indicator_of_mem hmem]
      have hHb : H (b * (x - Δ)) ≤ c1 := by
        refine (hHM _).trans ?_
        have h1 : b ^ 2 * Δ ^ 2 / 4 ≤ (b * (x - Δ)) ^ 2 := by
          have : Δ / 2 ≤ Δ - x := by linarith
          have h2 : (b * (Δ / 2)) ^ 2 ≤ (b * (Δ - x)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left this hb.le) 2
          nlinarith [h2, sq_nonneg (b * (x - Δ)), show (b * (Δ - x)) ^ 2 = (b * (x - Δ)) ^ 2 by ring]
        rw [hc1, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg hM (sq_nonneg (b * (x - Δ))), h1, hM, sq_nonneg Δ, sq_nonneg b,
          mul_nonneg hM (by positivity : (0 : ℝ) ≤ b ^ 2 * Δ ^ 2)]
      calc x ^ (-(3 / 4 : ℝ)) * H (b * (x - Δ)) ≤ x ^ (-(3 / 4 : ℝ)) * c1 :=
            mul_le_mul_of_nonneg_left hHb hxr
        _ = g1 x := by rw [hg1x]; ring
        _ ≤ g1 x + g2 x := le_add_of_nonneg_right (hg20 x)
    · push Not at hxh
      have hxr2 : x ^ (-(3 / 4 : ℝ)) ≤ 2 * Δ ^ (-(3 / 4 : ℝ)) := by
        have h1 : x ^ (-(3 / 4 : ℝ)) ≤ (Δ / 2) ^ (-(3 / 4 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hxh.le (by norm_num)
        rw [Real.div_rpow hΔ0.le (by norm_num)] at h1
        have h2 : (2 : ℝ) ^ (-(3 / 4 : ℝ)) ≥ 0 := by positivity
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_eq_one_div] at h1
        have h3 : (2 : ℝ) ^ ((3 / 4 : ℝ)) ≤ 2 := by
          calc (2 : ℝ) ^ ((3 / 4 : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
        have h4 : Δ ^ (-(3 / 4 : ℝ)) / (1 / (2 : ℝ) ^ (3 / 4 : ℝ)) = (2 : ℝ) ^ (3 / 4 : ℝ) * Δ ^ (-(3 / 4 : ℝ)) := by
          field_simp
        rw [h4] at h1
        calc x ^ (-(3 / 4 : ℝ)) ≤ (2 : ℝ) ^ (3 / 4 : ℝ) * Δ ^ (-(3 / 4 : ℝ)) := h1
          _ ≤ 2 * Δ ^ (-(3 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hΔ0.le _)
      have hHM' := hHM (b * (x - Δ))
      have hrpow0 : 0 ≤ Δ ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hΔ0.le _
      calc x ^ (-(3 / 4 : ℝ)) * H (b * (x - Δ))
          ≤ (2 * Δ ^ (-(3 / 4 : ℝ))) * (M / (1 + (b * (x - Δ)) ^ 2)) :=
            mul_le_mul hxr2 hHM' (hH0 _) (by positivity)
        _ = g2 x := by simp only [hg2]; ring
        _ ≤ g1 x + g2 x := le_add_of_nonneg_left (hg10 x)
  have hsum_int : IntegrableOn (fun x => g1 x + g2 x) (Ioi 0) :=
    (hg1int.add hg2int).integrableOn
  have step1 : ∫ x in Ioi (0 : ℝ), x ^ (-(3 / 4 : ℝ)) * H (b * (x - Δ)) ≤
      ∫ x in Ioi (0 : ℝ), (g1 x + g2 x) := by
    refine integral_mono_of_nonneg ?_ hsum_int ?_
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (hH0 _)
    · exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hdom)
  have step2 : ∫ x in Ioi (0 : ℝ), (g1 x + g2 x) =
      (∫ x in Ioi (0 : ℝ), g1 x) + ∫ x in Ioi (0 : ℝ), g2 x :=
    integral_add hg1int.integrableOn hg2int.integrableOn
  have step3 : ∫ x in Ioi (0 : ℝ), g2 x ≤ ∫ x, g2 x :=
    setIntegral_le_integral hg2int (Filter.Eventually.of_forall hg20)
  have step4 : ∫ x, g2 x = 2 * Δ ^ (-(3 / 4 : ℝ)) * M * J := by
    simp only [hg2]
    rw [integral_const_mul, hJ]
    congr 1
    exact integral_sub_right_eq_self (fun x : ℝ => (1 + (b * x) ^ 2)⁻¹) Δ
  have step5 : ∫ x in Ioi (0 : ℝ), g1 x = c1 * (4 * (Δ / 2) ^ (1 / 4 : ℝ)) := by
    simp only [hg1]
    rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.2 Set.Ioc_subset_Ioi_self,
      integral_const_mul, ← intervalIntegral.integral_of_le (by positivity),
      integral_rpow (Or.inl (by norm_num))]
    rw [show (-(3 / 4 : ℝ) + 1) = 1 / 4 by norm_num, Real.zero_rpow (by norm_num)]
    ring
  have hfin : c1 * (4 * (Δ / 2) ^ (1 / 4 : ℝ)) ≤ 16 * M / b ^ 2 * Δ ^ (-(3 / 4 : ℝ)) := by
    have h1 : (Δ / 2) ^ (1 / 4 : ℝ) ≤ Δ ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have h2 : Δ ^ (-2 : ℝ) * Δ ^ (1 / 4 : ℝ) ≤ Δ ^ (-(3 / 4 : ℝ)) := by
      rw [← Real.rpow_add hΔ0]
      exact Real.rpow_le_rpow_of_exponent_le hΔ (by norm_num)
    have hΔ2 : (Δ ^ 2)⁻¹ = Δ ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hΔ0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have : c1 * (4 * (Δ / 2) ^ (1 / 4 : ℝ)) ≤ c1 * (4 * Δ ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hc10
    refine this.trans ?_
    have e : c1 * (4 * Δ ^ (1 / 4 : ℝ)) = 16 * M / b ^ 2 * (Δ ^ (-2 : ℝ) * Δ ^ (1 / 4 : ℝ)) := by
      rw [hc1, ← hΔ2]; field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  calc ∫ x in Ioi (0 : ℝ), x ^ (-(3 / 4 : ℝ)) * H (b * (x - Δ))
      ≤ ∫ x in Ioi (0 : ℝ), (g1 x + g2 x) := step1
    _ = (∫ x in Ioi (0 : ℝ), g1 x) + ∫ x in Ioi (0 : ℝ), g2 x := step2
    _ ≤ c1 * (4 * (Δ / 2) ^ (1 / 4 : ℝ)) + 2 * Δ ^ (-(3 / 4 : ℝ)) * M * J := by
        rw [step5, ← step4]; exact add_le_add_right step3 _
    _ ≤ 16 * M / b ^ 2 * Δ ^ (-(3 / 4 : ℝ)) + 2 * Δ ^ (-(3 / 4 : ℝ)) * M * J :=
        add_le_add hfin le_rfl
    _ = (16 * M / b ^ 2 + 2 * M * J) * Δ ^ (-(3 / 4 : ℝ)) := by ring

end Lightlike.Tauberian
