import Mathlib

/-!
# Differentiation under the integral sign for compactly supported integrands

If `F t x` is differentiable in `t` with derivative `F' t x`, vanishes (with `F'`) outside a compact set `K`, and
`F'` is jointly continuous, then `d/dt ∫ F t x dx = ∫ F' 0 x dx` at `t = 0`.
-/

open MeasureTheory Metric Set Topology

namespace Lightlike.Canonical

variable {d : ℕ}

theorem hasDerivAt_integral_compact {F F' : ℝ → (Fin d → ℝ) → ℝ} {K : Set (Fin d → ℝ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε)
    (hzero : ∀ t x, x ∉ K → F t x = 0 ∧ F' t x = 0)
    (hderiv : ∀ t ∈ ball (0 : ℝ) ε, ∀ x, HasDerivAt (fun s => F s x) (F' t x) t)
    (hFc : ∀ t ∈ ball (0 : ℝ) ε, Continuous (F t))
    (hF'c : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F' p.1 p.2) (closedBall (0 : ℝ) (ε / 2) ×ˢ univ)) :
    Integrable (F' 0) volume ∧ HasDerivAt (fun t => ∫ x, F t x) (∫ x, F' 0 x) 0 := by
  have hε2 : 0 < ε / 2 := by linarith
  have hs : ball (0 : ℝ) (ε / 2) ∈ 𝓝 (0 : ℝ) := ball_mem_nhds _ hε2
  have hsub : ball (0 : ℝ) (ε / 2) ⊆ ball (0 : ℝ) ε := ball_subset_ball (by linarith)
  have hF_meas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) volume := by
    filter_upwards [hs] with t ht using (hFc t (hsub ht)).aestronglyMeasurable
  have hF0 : Continuous (F 0) := hFc 0 (mem_ball_self hε)
  have hF_int : Integrable (F 0) volume := by
    refine hF0.integrable_of_hasCompactSupport (HasCompactSupport.intro hK fun x hx => (hzero 0 x hx).1)
  have hF'0 : Continuous (F' 0) := by
    have : ContinuousOn (fun x : Fin d → ℝ => F' 0 x) univ := by
      have hc : ContinuousOn (fun x : Fin d → ℝ => ((0 : ℝ), x)) univ := (continuous_const.prodMk continuous_id).continuousOn
      refine (hF'c.comp hc ?_)
      intro x _
      exact ⟨by simp [hε2.le], mem_univ _⟩
    exact continuousOn_univ.mp this
  have hKc : IsCompact (closedBall (0 : ℝ) (ε / 2) ×ˢ K) := (isCompact_closedBall _ _).prod hK
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hF'c.mono (prod_mono subset_rfl (subset_univ _)))
  have hbound_int : Integrable (K.indicator fun _ => max C 0) volume := by
    rw [integrable_indicator_iff hK.measurableSet]
    exact integrableOn_const hK.measure_lt_top.ne
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F') (x₀ := (0 : ℝ))
    (bound := K.indicator fun _ => max C 0) hs hF_meas hF_int hF'0.aestronglyMeasurable
    (Filter.Eventually.of_forall fun a t ht => ?_) hbound_int
    (Filter.Eventually.of_forall fun a t ht => hderiv t (hsub ht) a)
  · exact this
  · by_cases ha : a ∈ K
    · rw [indicator_of_mem ha]
      have := hC (t, a) ⟨mem_closedBall.mpr (by have := mem_ball.mp ht; rw [Real.dist_eq, sub_zero] at this; rw [Real.dist_eq, sub_zero]; exact this.le), ha⟩
      exact this.trans (le_max_left _ _)
    · rw [indicator_of_notMem ha, (hzero t a ha).2]; simp

end Lightlike.Canonical
