module

public import Lightlike.Lorentz.Radial

/-!
# Trust checks for the Haar measure of SL(2,ℂ) (milestone HA2)

1. **The chart density is forced** (wrong input). Replace the density `|d|⁻²` of the Bruhat
   chart by `|d|^{-2s}` (`chartMeasure s`). Left translation by `diag(1/2, 2)` rescales that
   measure by `4^{s-1}` (`lintegral_chartMeasure_diag`), so it is left-invariant exactly when
   `s = 1` (`isMulLeftInvariant_chartMeasure_iff`). In particular the flat chart measure
   (`s = 0`) is not a Haar measure, and `s = 1` gives `haarC` (`chartMeasure_one`).
2. **Known value: hyperbolic balls.** `haarC {g | coshDist g < cosh R} = π³ (sinh 2R − 2R)`
   (`haarC_coshDist_lt` in `Radial.lean`) is `π²` times the volume `π (sinh 2R − 2R)` of a ball of
   radius `R` in hyperbolic 3-space. For `R = 1` the value is positive and finite
   (`haarC_ball_one_pos`, `haarC_ball_one_lt_top`), so the formula is not a statement about
   `0` or `∞`.

The numerical cross-check `scripts/lorentz/radial_check.py` evaluates the chart integral of
`exp(-coshDist)` by quadrature and compares it with the radial formula; its control drops the
factor `|d|⁻²`.
-/

@[expose] public section

open MeasureTheory Measure Real
open scoped ENNReal

namespace Lightlike.Lorentz

/-- The chart measure with density `|d|^{-2s}` in place of `|d|⁻²`. -/
noncomputable def chartMeasure (s : ℝ) : Measure SL2C :=
  (volume.withDensity fun x : Fin 3 → ℂ => ENNReal.ofReal ((‖x 2‖ ^ 2) ^ (-s))).map bruhat

/-- Almost every point of the chart has `d ≠ 0`. -/
lemma ae_two_ne_zero : ∀ᵐ x ∂(volume : Measure (Fin 3 → ℂ)), x 2 ≠ 0 := by
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_)
    (volume_hyperplane (u := 0) (v := 1) (Or.inr one_ne_zero))
  simp only [Set.mem_ofPred_eq, not_not] at hx ⊢
  simp [hx]

/-- `g ↦ |g₁₁|^{2(1-s)}` is measurable. -/
lemma measurable_entryPow (s : ℝ) :
    Measurable fun g : SL2C => ENNReal.ofReal ((‖g 1 1‖ ^ 2) ^ (1 - s)) := by
  exact ENNReal.measurable_ofReal.comp
    (((continuous_entry 1 1).measurable.norm.pow_const 2).pow_const _)

/-- `chartMeasure s` is `haarC` with the extra density `|d|^{2(1-s)}`, where `d = g₁₁`. -/
lemma lintegral_chartMeasure (s : ℝ) {F : SL2C → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ g, F g ∂chartMeasure s =
      ∫⁻ g, ENNReal.ofReal ((‖g 1 1‖ ^ 2) ^ (1 - s)) * F g ∂haarC := by
  rw [lintegral_haarC (F := fun g => ENNReal.ofReal ((‖g 1 1‖ ^ 2) ^ (1 - s)) * F g)
      ((measurable_entryPow s).mul hF), chartMeasure,
    lintegral_map hF measurable_bruhat]
  refine (lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
    (hF.comp measurable_bruhat)).trans (lintegral_congr_ae ?_)
  filter_upwards [ae_two_ne_zero] with x hx
  have h11 : (bruhat x) 1 1 = x 2 := by
    have := congrFun (congrFun (bruhat_apply hx) 1) 1
    simpa using this
  have hpos : 0 < ‖x 2‖ ^ 2 := by positivity
  simp only [Pi.mul_apply, bruhatDensity, h11, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_sub hpos, Real.rpow_one,
    Real.rpow_neg hpos.le]
  congr 1
  field_simp

/-- For `s = 1` the chart measure is the Haar measure `haarC`. -/
lemma chartMeasure_one : chartMeasure 1 = haarC := by
  unfold chartMeasure haarC
  congr 2
  funext x
  simp [bruhatDensity, Real.rpow_neg_one]

/-- Left multiplication by `diag(1/2, 2)` doubles the entry `d = g₁₁`. -/
lemma diag_half_mul_one_one (g : SL2C) :
    (SL2C.diagSL (1 / 2) (by norm_num) * g) 1 1 = 2 * g 1 1 := by
  simp [SL2C.diagSL, Matrix.mul_apply, Fin.sum_univ_two]

/-- Left translation by `diag(1/2, 2)` rescales `chartMeasure s` by `4^{s-1}`. -/
lemma lintegral_chartMeasure_diag (s : ℝ) {F : SL2C → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ g, F g ∂chartMeasure s = ENNReal.ofReal (4 ^ (1 - s)) *
      ∫⁻ g, F (SL2C.diagSL (1 / 2) (by norm_num) * g) ∂chartMeasure s := by
  set a := SL2C.diagSL (1 / 2) (by norm_num)
  have hFa : Measurable fun g => F (a * g) := hF.comp (measurable_const_mul a)
  rw [lintegral_chartMeasure s hF, lintegral_chartMeasure s hFa,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (lintegral_mul_left_eq_self
    (fun g => ENNReal.ofReal ((‖g 1 1‖ ^ 2) ^ (1 - s)) * F g) a).symm.trans
    (lintegral_congr fun g => ?_)
  simp only [a, diag_half_mul_one_one, norm_mul, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_mul (by positivity), mul_pow,
    Real.mul_rpow (by positivity) (by positivity)]
  norm_num

/-- **Trust check: the chart density is forced.** With the density `|d|^{-2s}` in place of
`|d|⁻²`, the Bruhat chart gives a left-invariant measure exactly when `s = 1`. -/
theorem isMulLeftInvariant_chartMeasure_iff (s : ℝ) :
    (chartMeasure s).IsMulLeftInvariant ↔ s = 1 := by
  constructor
  · intro hinv
    set U := {g : SL2C | ‖g 0 1‖ < 2 ∧ ‖g 1 0‖ < 2 ∧ ‖g 1 1‖ < 2 ∧ 1 / 2 < ‖g 1 1‖}
    have c := fun i j => (continuous_entry i j).norm
    have hU : IsOpen U :=
      (isOpen_lt (c 0 1) continuous_const).inter ((isOpen_lt (c 1 0) continuous_const).inter
        ((isOpen_lt (c 1 1) continuous_const).inter (isOpen_lt continuous_const (c 1 1))))
    have h1U : (1 : SL2C) ∈ U := by simp [U]; norm_num
    set F := U.indicator fun g : SL2C => ENNReal.ofReal ((‖g 1 1‖ ^ 2) ^ (s - 1))
    have hF : Measurable F :=
      (ENNReal.measurable_ofReal.comp
        (((continuous_entry 1 1).measurable.norm.pow_const 2).pow_const _)).indicator
        hU.measurableSet
    have hX : ∫⁻ g, F g ∂chartMeasure s = haarC U := by
      rw [lintegral_chartMeasure s hF, ← lintegral_indicator_one hU.measurableSet]
      refine lintegral_congr fun g => ?_
      by_cases hg : g ∈ U
      · have hpos : 0 < ‖g 1 1‖ ^ 2 := by
          have := hg.2.2.2; positivity
        simp only [F, Set.indicator_of_mem hg, Pi.one_apply]
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hpos]
        simp
      · simp [F, Set.indicator_of_notMem hg]
    have hpos : haarC U ≠ 0 := (hU.measure_pos haarC ⟨1, h1U⟩).ne'
    have htop : haarC U ≠ ∞ := by
      refine ne_top_of_le_ne_top (haarC_box_lt_top 2 (by norm_num : (0 : ℝ) < 1 / 2)).ne
        (measure_mono fun g hg => ?_)
      exact ⟨hg.1.le, hg.2.1.le, hg.2.2.1.le, hg.2.2.2.le⟩
    have key := lintegral_chartMeasure_diag s hF
    rw [lintegral_mul_left_eq_self, hX] at key
    have h4 : ENNReal.ofReal (4 ^ (1 - s)) = 1 :=
      (ENNReal.mul_left_inj hpos htop).1 (key.symm.trans (one_mul _).symm)
    have h4' : (4 : ℝ) ^ (1 - s) = 1 := (ENNReal.ofReal_eq_one).1 h4
    have hlog := congrArg Real.log h4'
    rw [Real.log_rpow (by norm_num), Real.log_one] at hlog
    have : Real.log 4 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have := (mul_eq_zero.1 hlog).resolve_right this
    linarith
  · rintro rfl
    rw [chartMeasure_one]
    infer_instance

/-- Non-vacuity of the ball formula: the ball of radius `1` has positive measure. -/
theorem haarC_ball_one_pos : 0 < haarC {g | coshDist g < cosh 1} := by
  rw [haarC_coshDist_lt zero_le_one, ENNReal.ofReal_pos, mul_one]
  have := Real.self_lt_sinh_iff.2 (two_pos : (0 : ℝ) < 2)
  exact mul_pos (by positivity) (by linarith)

/-- Non-vacuity of the ball formula: the ball of radius `1` has finite measure. -/
theorem haarC_ball_one_lt_top : haarC {g | coshDist g < cosh 1} < ∞ := by
  rw [haarC_coshDist_lt zero_le_one]; exact ENNReal.ofReal_lt_top

end Lightlike.Lorentz
