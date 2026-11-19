import Lightlike.Asymptotics.Karamata.RegularVariation

/-!
# The Laplace transform as an integral of the counting function

For a measure `ρ` on `[0, ∞)`, finite on compact sets, with finite Laplace transform `L`:
`L β = ∫₀^∞ β exp (-β x) ρ [0, x] dx` (`laplace_eq_integral_counting`), by Fubini's theorem for the kernel
`β exp (-β x) 1_{0 ≤ y ≤ x}`.

Supporting lemma for the Abelian direction of Karamata's theorem; no catalogue entry.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace Lightlike.Karamata

open Lightlike.Tauberian

variable {ρ : Measure ℝ} [IsFiniteMeasureOnCompacts ρ]

lemma counting_mono {X Y : ℝ} (h : X ≤ Y) : counting ρ X ≤ counting ρ Y :=
  ENNReal.toReal_mono (isCompact_Icc.measure_lt_top).ne (measure_mono (Icc_subset_Icc_right h))

/-- The kernel `(y, x) ↦ β exp (-β x) 1_{0 ≤ y ≤ x}` of the layer-cake formula. -/
def lcKernel (β : ℝ) : ℝ × ℝ → ℝ :=
  {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ q.2}.indicator fun q => β * Real.exp (-β * q.2)

lemma measurable_lcKernel (β : ℝ) : Measurable (lcKernel β) := by
  unfold lcKernel
  refine Measurable.indicator (by fun_prop) ?_
  exact (measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_snd)

lemma lcKernel_apply (β y x : ℝ) :
    lcKernel β (y, x) = if 0 ≤ y ∧ y ≤ x then β * Real.exp (-β * x) else 0 := by
  unfold lcKernel
  rw [indicator_apply]
  rfl

lemma lcKernel_nonneg {β : ℝ} (hβ : 0 < β) (y x : ℝ) : 0 ≤ lcKernel β (y, x) := by
  rw [lcKernel_apply]
  split_ifs
  · positivity
  · exact le_rfl

lemma lcKernel_right_eq (β : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (fun x => lcKernel β (y, x)) = (Ici y).indicator fun x => β * Real.exp (-β * x) := by
  funext x
  rw [lcKernel_apply, indicator_apply]
  by_cases hx : y ≤ x
  · rw [if_pos ⟨hy, hx⟩, if_pos (show x ∈ Ici y from hx)]
  · rw [if_neg (fun h => hx h.2), if_neg (show x ∉ Ici y from hx)]

lemma integral_lcKernel_right {β y : ℝ} (hβ : 0 < β) (hy : 0 ≤ y) :
    ∫ x, lcKernel β (y, x) = Real.exp (-β * y) := by
  have hβ0 : β ≠ 0 := hβ.ne'
  rw [lcKernel_right_eq β hy, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, integral_exp_mul_Ioi (by linarith : -β < 0)]
  field_simp

lemma integrable_lcKernel_right {β : ℝ} (hβ : 0 < β) (y : ℝ) :
    Integrable fun x => lcKernel β (y, x) := by
  by_cases hy : 0 ≤ y
  · rw [lcKernel_right_eq β hy, integrable_indicator_iff measurableSet_Ici,
      integrableOn_Ici_iff_integrableOn_Ioi]
    exact (exp_neg_integrableOn_Ioi y hβ).const_mul β
  · have h : (fun x => lcKernel β (y, x)) = fun _ => (0 : ℝ) := by
      funext x
      rw [lcKernel_apply, if_neg fun h => hy h.1]
    rw [h]
    exact integrable_zero _ _ _

omit [IsFiniteMeasureOnCompacts ρ] in
lemma integral_lcKernel_left (β x : ℝ) :
    ∫ y, lcKernel β (y, x) ∂ρ = β * Real.exp (-β * x) * counting ρ x := by
  have h : (fun y => lcKernel β (y, x)) = (Icc 0 x).indicator fun _ => β * Real.exp (-β * x) := by
    funext y
    rw [lcKernel_apply, indicator_apply]
    by_cases hy : 0 ≤ y ∧ y ≤ x
    · rw [if_pos hy, if_pos (show y ∈ Icc 0 x from hy)]
    · rw [if_neg hy, if_neg (show y ∉ Icc 0 x from hy)]
  rw [h, integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_comm]
  rfl

/-- **Layer-cake formula for the Laplace transform**: `L β = ∫₀^∞ β exp (-β x) ρ [0, x] dx`. -/
theorem laplace_eq_integral_counting (hρ : ρ (Iio 0) = 0)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ) {β : ℝ} (hβ : 0 < β) :
    laplace ρ β = ∫ x in Ioi 0, β * Real.exp (-β * x) * counting ρ x := by
  have hprod : Integrable (lcKernel β) (ρ.prod volume) := by
    rw [integrable_prod_iff (measurable_lcKernel β).aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun y => integrable_lcKernel_right hβ y, ?_⟩
    refine (hint β hβ).congr ?_
    filter_upwards [ae_nonneg_of_Iio hρ] with y hy
    have hnn : ∀ x, ‖lcKernel β (y, x)‖ = lcKernel β (y, x) := fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (lcKernel_nonneg hβ y x)]
    simp_rw [hnn]
    exact (integral_lcKernel_right hβ hy).symm
  have hunc : Function.uncurry (fun y x => lcKernel β (y, x)) = lcKernel β := by
    funext ⟨y, x⟩
    rfl
  have hswap := integral_integral_swap (f := fun y x => lcKernel β (y, x)) (μ := ρ) (ν := volume)
    (by rw [hunc]; exact hprod)
  have hL : laplace ρ β = ∫ y, (∫ x, lcKernel β (y, x)) ∂ρ := by
    unfold laplace
    refine integral_congr_ae ?_
    filter_upwards [ae_nonneg_of_Iio hρ] with y hy
    exact (integral_lcKernel_right hβ hy).symm
  rw [hL, hswap]
  simp_rw [integral_lcKernel_left]
  rw [← integral_Ici_eq_integral_Ioi]
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  have hx' : x < 0 := not_le.1 hx
  have h0 : counting ρ x = 0 := by
    unfold counting
    rw [Icc_eq_empty (not_le.2 hx')]
    simp
  rw [h0, mul_zero]

end Lightlike.Karamata
