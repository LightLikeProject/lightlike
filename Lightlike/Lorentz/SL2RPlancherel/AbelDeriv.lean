module

public import Mathlib

/-!
# Differentiating the half-order Abel integral under the integral sign

For a `C¹` function `f : ℝ → ℂ` of compact support, the half-order integral
`v ↦ ∫_{w > 0} w^{-1/2} f (v + w) dw` is differentiable with derivative
`∫_{w > 0} w^{-1/2} f' (v + w) dw`: the Abel transform commutes with `d/dv`. This is the step that
turns `g = abelTransform F` into a function whose derivative is again an Abel integral, in the
proof of the SL(2,ℝ) Plancherel formula with density `ρ tanh(πρ)` (milestone HA3).
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- Differentiation under the integral sign for the half-order integral of a compactly supported
`C¹` function. -/
theorem hasDerivAt_halfAbel (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (x : ℝ) :
    HasDerivAt (fun v : ℝ => ∫ w in Ioi (0 : ℝ), (w ^ (-(1 / 2 : ℝ)) : ℝ) • f (v + w))
      (∫ w in Ioi (0 : ℝ), (w ^ (-(1 / 2 : ℝ)) : ℝ) • deriv f (x + w)) x := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hsupp : ∀ y, R < |y| → f y = 0 ∧ deriv f y = 0 := by
    intro y hy
    have hy' : y ∉ tsupport f := fun h => by
      have := hR h
      simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      linarith
    have h1 : f y = 0 := image_eq_zero_of_notMem_tsupport hy'
    refine ⟨h1, ?_⟩
    have : y ∉ tsupport (deriv f) := fun h => hy' (tsupport_deriv_subset h)
    exact image_eq_zero_of_notMem_tsupport this
  have hcont : Continuous f := hf.continuous
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd'cont : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ := hd'cont.bounded_above_of_compact_support hc.deriv
  obtain ⟨Cf, hCf⟩ := hcont.bounded_above_of_compact_support hc
  set T : ℝ := |R| + |x| + 2 with hT
  have hTpos : 0 < T := by positivity
  have hind : IntegrableOn (fun w : ℝ => w ^ (-(1 / 2 : ℝ))) (Ioo 0 T) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hTpos).2 (by norm_num)
  have hindI : Integrable ((Ioo 0 T).indicator (fun w : ℝ => w ^ (-(1 / 2 : ℝ)))) :=
    hind.integrable_indicator measurableSet_Ioo
  have hmeas : ∀ g : ℝ → ℂ, Continuous g → ∀ v : ℝ,
      AEStronglyMeasurable (fun w : ℝ => (w ^ (-(1 / 2 : ℝ)) : ℝ) • g (v + w))
        (volume.restrict (Ioi (0 : ℝ))) := by
    intro g hg v
    refine Measurable.aestronglyMeasurable ?_
    have : Measurable g := hg.measurable
    fun_prop
  -- vanishing beyond `T`
  have hvan : ∀ v : ℝ, |v - x| < 1 → ∀ w : ℝ, T ≤ w → f (v + w) = 0 ∧ deriv f (v + w) = 0 := by
    intro v hv w hw
    apply hsupp
    have h1 : |v| ≤ |x| + 1 := by
      have := abs_sub_abs_le_abs_sub v x
      linarith
    have : |v + w| ≥ w - |v| := by
      have := neg_abs_le (v + w)
      have h2 := abs_add_le (v + w) (-v)
      simp only [abs_neg] at h2
      have : w ≤ |v + w| + |v| := by
        have h3 : w ≤ |w| := le_abs_self w
        have h4 : |w| ≤ |v + w| + |v| := by simpa using h2
        linarith
      linarith
    have : 0 ≤ |R| := abs_nonneg R
    have : R ≤ |R| := le_abs_self R
    linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (v : ℝ) (w : ℝ) => (w ^ (-(1 / 2 : ℝ)) : ℝ) • f (v + w))
    (F' := fun (v : ℝ) (w : ℝ) => (w ^ (-(1 / 2 : ℝ)) : ℝ) • deriv f (v + w))
    (x₀ := x) (s := Metric.ball x 1) (Metric.ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall (fun v => hmeas f hcont v))
    ?_ (hmeas _ hd'cont x)
    (bound := fun w => C * (Ioo 0 T).indicator (fun w : ℝ => w ^ (-(1 / 2 : ℝ))) w) ?_
    (hindI.restrict.const_mul C) ?_
  · exact key.2
  · refine Integrable.mono' (hindI.restrict.const_mul Cf) (hmeas f hcont x) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun w hw => ?_)
    have hw' : 0 < w := hw
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hw'.le _)]
    by_cases h : w < T
    · rw [indicator_of_mem (show w ∈ Ioo 0 T from ⟨hw', h⟩)]
      rw [mul_comm]
      gcongr
      exact hCf _
    · have := (hvan x (by simp) w (not_lt.1 h)).1
      rw [this]
      simp [indicator_of_notMem (show w ∉ Ioo 0 T from fun h' => h h'.2)]
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun w hw => ?_)
    intro v hv
    have hw' : 0 < w := hw
    have hv' : |v - x| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hv
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hw'.le _)]
    by_cases h : w < T
    · rw [indicator_of_mem (show w ∈ Ioo 0 T from ⟨hw', h⟩)]
      rw [mul_comm]
      gcongr
      exact hC _
    · have := (hvan v hv' w (not_lt.1 h)).2
      rw [this]
      simp [indicator_of_notMem (show w ∉ Ioo 0 T from fun h' => h h'.2)]
  · refine Filter.Eventually.of_forall fun w => ?_
    intro v _
    exact (((hdiff (v + w)).hasDerivAt).comp_add_const v w).const_smul (w ^ (-(1 / 2 : ℝ)))

end Lightlike.Lorentz.SL2R
