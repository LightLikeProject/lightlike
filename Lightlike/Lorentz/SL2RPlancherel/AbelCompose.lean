module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.AbelComposition

/-!
# Composing two half-order Abel integrals

For an integrable `F : ℝ → ℂ`, the half-order integral is `A F (b) = ∫_{a > b} F a / √(a - b) da`.
`integral_halfAbel_comp` says that applying it twice gives `π` times the plain integral:
`∫_{b > v} (A F b) / √(b - v) db = π ∫_{a > v} F a da`.
It follows from Fubini and the Beta(1/2, 1/2) integral `integral_inv_sqrt_mul_sub`, and is the
step that inverts the Abel transform on the hyperbolic plane, milestone HA3 (SL(2,ℝ) Plancherel
measure, density `ρ tanh(πρ)`).
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- The Beta kernel `1/√((a - v)(u - a))` is integrable on `(v, u)`. -/
lemma integrableOn_inv_sqrt_mul_sub {v u : ℝ} (h : v < u) :
    IntegrableOn (fun a => 1 / √((a - v) * (u - a))) (Ioo v u) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_inv_sqrt_mul_sub h]
  exact pi_ne_zero

/-- The integrand on the triangle `v < b < a`, as a function of `(b, a)`. -/
def composeKernel (F : ℝ → ℂ) (v b a : ℝ) : ℂ :=
  if v < b ∧ b < a then F a * ((1 / √((b - v) * (a - b)) : ℝ) : ℂ) else 0

lemma composeKernel_eq_indicator (F : ℝ → ℂ) (v a : ℝ) :
    (fun b => composeKernel F v b a) =
      (Ioo v a).indicator (fun b => F a * ((1 / √((b - v) * (a - b)) : ℝ) : ℂ)) := by
  funext b
  by_cases h : b ∈ Ioo v a
  · simp [composeKernel, h.1, h.2]
  · have : ¬ (v < b ∧ b < a) := fun h' => h h'
    simp [composeKernel, this]

lemma integral_composeKernel (F : ℝ → ℂ) (v a : ℝ) :
    ∫ b, composeKernel F v b a = (Ioi v).indicator (fun a => (π : ℂ) * F a) a := by
  rw [composeKernel_eq_indicator]
  by_cases h : v < a
  · rw [integral_indicator measurableSet_Ioo, indicator_of_mem (show a ∈ Ioi v from h)]
    rw [integral_const_mul, integral_complex_ofReal, integral_inv_sqrt_mul_sub h]
    ring
  · have : Ioo v a = ∅ := Ioo_eq_empty h
    simp [this, show a ∉ Ioi v from h]

lemma integrable_composeKernel_slice (F : ℝ → ℂ) (v a : ℝ) :
    Integrable (fun b => composeKernel F v b a) := by
  rw [composeKernel_eq_indicator]
  by_cases h : v < a
  · refine (IntegrableOn.integrable_indicator ?_ measurableSet_Ioo)
    exact ((integrableOn_inv_sqrt_mul_sub h).ofReal).const_mul _
  · have : Ioo v a = ∅ := Ioo_eq_empty h
    simp [this]

lemma integral_norm_composeKernel (F : ℝ → ℂ) (v a : ℝ) :
    ∫ b, ‖composeKernel F v b a‖ = (Ioi v).indicator (fun a => π * ‖F a‖) a := by
  have : (fun b => ‖composeKernel F v b a‖) =
      (Ioo v a).indicator (fun b => ‖F a‖ * (1 / √((b - v) * (a - b)))) := by
    funext b
    by_cases h : b ∈ Ioo v a
    · have hp : 0 ≤ 1 / √((b - v) * (a - b)) := by positivity
      simp [composeKernel, h.1, h.2]
    · have : ¬ (v < b ∧ b < a) := fun h' => h h'
      simp [composeKernel, this]
  rw [this]
  by_cases h : v < a
  · rw [integral_indicator measurableSet_Ioo, indicator_of_mem (show a ∈ Ioi v from h),
      integral_const_mul, integral_inv_sqrt_mul_sub h]
    ring
  · have : Ioo v a = ∅ := Ioo_eq_empty h
    simp [this, show a ∉ Ioi v from h]

lemma measurable_composeKernel_uncurry (F : ℝ → ℂ) (hF : Measurable F) (v : ℝ) :
    Measurable (Function.uncurry (composeKernel F v)) := by
  unfold composeKernel Function.uncurry
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  · fun_prop

/-- Integrability of the triangle kernel on `ℝ × ℝ`, for a measurable integrable `F`. -/
lemma integrable_composeKernel (F : ℝ → ℂ) (hF : Measurable F) (hI : Integrable F) (v : ℝ) :
    Integrable (Function.uncurry (composeKernel F v)) (volume.prod volume) := by
  rw [integrable_prod_iff' (measurable_composeKernel_uncurry F hF v).aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall (integrable_composeKernel_slice F v), ?_⟩
  simp only [Function.uncurry_apply_pair, integral_norm_composeKernel]
  exact (hI.norm.const_mul π).indicator measurableSet_Ioi

/-- **Two half-order Abel integrals compose to `π` times the integral**:
`∫_{b > v} (∫_{a > b} F a / √(a - b) da) / √(b - v) db = π ∫_{a > v} F a da`. -/
theorem integral_halfAbel_comp (F : ℝ → ℂ) (hF : Measurable F) (hI : Integrable F) (v : ℝ) :
    ∫ b in Ioi v, (∫ a in Ioi b, F a / ((√(a - b) : ℝ) : ℂ)) / ((√(b - v) : ℝ) : ℂ) =
      (π : ℂ) * ∫ a in Ioi v, F a := by
  have hswap := integral_integral_swap (integrable_composeKernel F hF hI v)
  have hR : ∫ a, ∫ b, composeKernel F v b a = (π : ℂ) * ∫ a in Ioi v, F a := by
    simp only [integral_composeKernel]
    rw [integral_indicator measurableSet_Ioi, integral_const_mul]
  have hL : ∫ b, ∫ a, composeKernel F v b a =
      ∫ b in Ioi v, (∫ a in Ioi b, F a / ((√(a - b) : ℝ) : ℂ)) / ((√(b - v) : ℝ) : ℂ) := by
    rw [← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun b => ?_))
    by_cases hb : v < b
    · rw [indicator_of_mem (show b ∈ Ioi v from hb), ← integral_div]
      have : (fun a => composeKernel F v b a) =
          (Ioi b).indicator (fun a => F a / ((√(a - b) : ℝ) : ℂ) / ((√(b - v) : ℝ) : ℂ)) := by
        funext a
        by_cases ha : b < a
        · have hs1 : 0 < √(a - b) := Real.sqrt_pos.2 (by linarith)
          have hs2 : 0 < √(b - v) := Real.sqrt_pos.2 (by linarith)
          rw [indicator_of_mem (show a ∈ Ioi b from ha)]
          simp only [composeKernel, hb, ha, and_self, ite_true]
          rw [Real.sqrt_mul (by linarith)]
          push_cast
          field_simp
        · simp [composeKernel, ha]
      simp only [this]
      rw [integral_indicator measurableSet_Ioi]
    · rw [indicator_of_notMem (show b ∉ Ioi v from hb)]
      simp [composeKernel, hb]
  rw [← hL, hswap, hR]

end Lightlike.Lorentz.SL2R
