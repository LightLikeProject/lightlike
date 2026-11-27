import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.TorusParseval

/-!
# Smoothness of parameter integrals over the box

If `Φ : ℝ → (Fin 2 → ℝ) → ℂ` is jointly smooth, then `ξ ↦ ∫_K Φ ξ x dx` is smooth for every compact
`K` (`contDiff_setIntegral_of_isCompact`): the `ξ`-derivative passes under the integral, dominated by
the maximum of the continuous partial derivative on `closedBall ξ₀ 1 × K`, and the partial derivative
`fderiv Φ (ξ, x) (1, 0)` is again jointly smooth. The box `(0, 1]²` differs from `[0, 1]²` by a null
set, so the same holds for `∫_box` (`contDiff_integral_box`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (smoothness of the `K × K` components),
milestone HA3.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The `ξ`-partial derivative `fderiv Φ (ξ, x) (1, 0)`. -/
def partialFst (Φ : ℝ → (Fin 2 → ℝ) → ℂ) (ξ : ℝ) (x : Fin 2 → ℝ) : ℂ :=
  fderiv ℝ (Function.uncurry Φ) (ξ, x) (1, 0)

lemma contDiff_partialFst {Φ : ℝ → (Fin 2 → ℝ) → ℂ} (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) :
    ContDiff ℝ ∞ (Function.uncurry (partialFst Φ)) :=
  (hΦ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma hasDerivAt_partialFst {Φ : ℝ → (Fin 2 → ℝ) → ℂ} (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ))
    (ξ : ℝ) (x : Fin 2 → ℝ) : HasDerivAt (fun t => Φ t x) (partialFst Φ ξ x) ξ := by
  have hd := ((hΦ.differentiable (by simp)) (ξ, x)).hasFDerivAt
  have hp : HasDerivAt (fun t : ℝ => (t, x)) ((1 : ℝ), (0 : Fin 2 → ℝ)) ξ :=
    (hasDerivAt_id ξ).prodMk (hasDerivAt_const ξ x)
  exact hd.comp_hasDerivAt ξ hp

/-- The derivative of a parameter integral over a compact set. -/
lemma hasDerivAt_setIntegral_of_isCompact {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    {Φ : ℝ → (Fin 2 → ℝ) → ℂ} (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) (ξ₀ : ℝ) :
    HasDerivAt (fun ξ => ∫ x in K, Φ ξ x) (∫ x in K, partialFst Φ ξ₀ x) ξ₀ := by
  have hc := hΦ.continuous
  have hc' := (contDiff_partialFst hΦ).continuous
  obtain ⟨C, hC⟩ := (isCompact_closedBall ξ₀ 1).prod hK |>.exists_bound_of_continuousOn
    hc'.norm.continuousOn
  have hcont : ∀ ξ, Continuous (Φ ξ) := fun ξ => hc.comp (Continuous.prodMk_right ξ)
  have hcont' : ∀ ξ, Continuous (partialFst Φ ξ) := fun ξ => hc'.comp (Continuous.prodMk_right ξ)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (Metric.ball_mem_nhds ξ₀ one_pos)
    (Eventually.of_forall fun ξ => (hcont ξ).aestronglyMeasurable)
    ((hcont ξ₀).continuousOn.integrableOn_compact hK)
    (hcont' ξ₀).aestronglyMeasurable ?_ ?_ ?_).2
  · filter_upwards [ae_restrict_mem₀ hK.measurableSet.nullMeasurableSet] with x hx ξ hξ
    have := hC (ξ, x) ⟨Metric.ball_subset_closedBall hξ, hx⟩
    simpa using this
  · have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    exact integrable_const C
  · exact Eventually.of_forall fun x ξ _ => hasDerivAt_partialFst hΦ ξ x

/-- **Smooth parameter integrals over a compact set.** -/
theorem contDiff_setIntegral_of_isCompact {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    {Φ : ℝ → (Fin 2 → ℝ) → ℂ} (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) :
    ContDiff ℝ ∞ fun ξ => ∫ x in K, Φ ξ x := by
  suffices h : ∀ n : ℕ, ∀ Φ : ℝ → (Fin 2 → ℝ) → ℂ, ContDiff ℝ ∞ (Function.uncurry Φ) →
      ContDiff ℝ n fun ξ => ∫ x in K, Φ ξ x from
    contDiff_infty.2 fun n => h n Φ hΦ
  intro n
  induction n with
  | zero =>
    intro Φ hΦ
    exact contDiff_zero.2 (continuous_parametric_integral_of_continuous hΦ.continuous hK)
  | succ n ih =>
    intro Φ hΦ
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun ξ => (hasDerivAt_setIntegral_of_isCompact hK hΦ ξ).differentiableAt,
      by simp, ?_⟩
    have e : deriv (fun ξ => ∫ x in K, Φ ξ x) = fun ξ => ∫ x in K, partialFst Φ ξ x :=
      funext fun ξ => (hasDerivAt_setIntegral_of_isCompact hK hΦ ξ).deriv
    rw [e]
    exact ih _ (contDiff_partialFst hΦ)

/-- **Smooth parameter integrals over the box** `(0, 1]²`. -/
theorem contDiff_integral_box {Φ : ℝ → (Fin 2 → ℝ) → ℂ}
    (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) : ContDiff ℝ ∞ fun ξ => ∫ x in box, Φ ξ x := by
  have hbox : box =ᵐ[volume] Icc (0 : Fin 2 → ℝ) 1 := by
    have h := Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin 2 => (volume : Measure ℝ))
      (f := fun _ => (0 : ℝ)) (g := fun _ => (1 : ℝ))
    rw [← volume_pi] at h
    convert h using 2
    ext x
    simp [box]
  have e : (fun ξ => ∫ x in box, Φ ξ x) = fun ξ => ∫ x in Icc (0 : Fin 2 → ℝ) 1, Φ ξ x :=
    funext fun ξ => setIntegral_congr_set hbox
  rw [e]
  exact contDiff_setIntegral_of_isCompact isCompact_Icc hΦ

end Lightlike.Lorentz.SL2RPlancherel
