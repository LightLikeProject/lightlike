module

public import Mathlib

/-!
# The weighted mean-value property of holomorphic functions on the unit disc

For `h` holomorphic on the open unit disc and a radial weight `ρ(|w|)`,
`∫_{|w|<1} h(w) ρ(|w|) dA = h(0) ∫_{|w|<1} ρ(|w|) dA`
whenever `h · ρ(|·|)` is integrable: polar coordinates and the circle mean-value property
`(2π)⁻¹ ∫_0^{2π} h(s e^{iθ}) dθ = h(0)`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The circle mean of a function holomorphic on the open disc is its value at the centre. -/
lemma integral_circle_polar {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball (0 : ℂ) 1)) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∫ θ in Ioo (-π) π, h (Complex.polarCoord.symm (s, θ)) = (2 * π : ℝ) • h 0 := by
  have hdc : DiffContOnCl ℂ h (ball (0 : ℂ) |s|) := by
    rw [abs_of_pos hs.1]
    exact (hh.mono (closedBall_subset_ball hs.2)).diffContOnCl_ball subset_rfl
  have hmean := hdc.circleAverage
  rw [Real.circleAverage_def] at hmean
  have hper : ∫ θ in (0 : ℝ)..2 * π, h (circleMap 0 s θ) =
      ∫ θ in Ioo (-π) π, h (Complex.polarCoord.symm (s, θ)) := by
    have h1 := ((periodic_circleMap 0 s).comp h).intervalIntegral_add_eq 0 (-π)
    simp only [zero_add, Function.comp_def] at h1
    rw [h1, show -π + 2 * π = π by ring, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
    simp only [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, zero_add]
  rw [hper] at hmean
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  have : ∫ θ in Ioo (-π) π, h (Complex.polarCoord.symm (s, θ)) = (2 * π : ℝ) • (2 * π)⁻¹ •
      ∫ θ in Ioo (-π) π, h (Complex.polarCoord.symm (s, θ)) := by
    rw [smul_smul, mul_inv_cancel₀ hpi, one_smul]
  rw [this, hmean]

/-- **Polar reduction**: for `k` holomorphic on the disc and a continuous radial weight with `k ρ(|·|)` integrable,
`∫_{|w|<1} k(w) ρ(|w|) dA = 2π k(0) ∫_0^1 s ρ(s) ds`. -/
theorem integral_ball_radial {k : ℂ → ℂ} (hk : DifferentiableOn ℂ k (ball (0 : ℂ) 1)) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hint : IntegrableOn (fun w => k w * (ρ ‖w‖ : ℂ)) (ball (0 : ℂ) 1)) :
    ∫ w in ball (0 : ℂ) 1, k w * (ρ ‖w‖ : ℂ) =
      (2 * π : ℝ) • k 0 * ((∫ s in Ioo (0 : ℝ) 1, s * ρ s : ℝ) : ℂ) := by
  classical
  set F : ℂ → ℂ := (ball (0 : ℂ) 1).indicator (fun w => k w * (ρ ‖w‖ : ℂ)) with hF
  have hFm : Measurable F := by
    rw [hF, ← Set.piecewise_eq_indicator]
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const measurableSet_ball
    exact hk.continuousOn.mul (Complex.continuous_ofReal.comp (hρ.comp continuous_norm)).continuousOn
  have hFi : Integrable F := (integrable_indicator_iff measurableSet_ball).2 hint
  have hpol := Complex.integral_comp_polarCoord_symm F
  have hFint : ∫ p, F p = ∫ w in ball (0 : ℂ) 1, k w * (ρ ‖w‖ : ℂ) := integral_indicator measurableSet_ball
  rw [← hFint, ← hpol]
  set G : ℝ × ℝ → ℂ := fun p => p.1 • F (Complex.polarCoord.symm p) with hG
  have hsymm : Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    simp only [Complex.polarCoord_symm_apply]; fun_prop
  have hGm : Measurable G := (measurable_fst.smul (hFm.comp hsymm.measurable))
  have hGi : IntegrableOn G (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := by
    refine ⟨hGm.aestronglyMeasurable, ?_⟩
    have h1 := Complex.lintegral_comp_polarCoord_symm (fun z => ‖F z‖ₑ)
    have h2 : ∫⁻ p in Complex.polarCoord.target, ‖G p‖ₑ = ∫⁻ z, ‖F z‖ₑ := by
      rw [← h1]
      refine setLIntegral_congr_fun Complex.polarCoord.open_target.measurableSet fun p hp => ?_
      have hp1 : 0 < p.1 := hp.1
      simp only [hG, enorm_smul, smul_eq_mul, Real.enorm_eq_ofReal hp1.le]
    have : HasFiniteIntegral G (volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo (-π) π)) := by
      unfold HasFiniteIntegral
      rw [← Complex.polarCoord_target, h2]
      exact hFi.2
    exact this
  have ht : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  rw [ht, Measure.volume_eq_prod, setIntegral_prod G hGi]
  have hin : ∀ s ∈ Ioi (0 : ℝ), ∫ θ in Ioo (-π) π, G (s, θ) =
      (Ioo (0 : ℝ) 1).indicator (fun s => ((s * ρ s : ℝ) : ℂ) * ((2 * π : ℝ) • k 0)) s := by
    intro s hs
    have hs0 : 0 < s := hs
    by_cases hs1 : s < 1
    · have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨hs0, hs1⟩
      rw [indicator_of_mem hsI]
      have : ∀ θ : ℝ, G (s, θ) = ((s * ρ s : ℝ) : ℂ) * k (Complex.polarCoord.symm (s, θ)) := by
        intro θ
        have hmem : Complex.polarCoord.symm (s, θ) ∈ ball (0 : ℂ) 1 := by
          rw [mem_ball_zero_iff, Complex.norm_polarCoord_symm]; simpa [abs_of_pos hs0] using hs1
        simp only [hG, hF, indicator_of_mem hmem, Complex.norm_polarCoord_symm, abs_of_pos hs0,
          Complex.real_smul]
        push_cast
        ring
      simp_rw [this]
      rw [integral_const_mul, integral_circle_polar hk hsI]
    · rw [indicator_of_notMem (fun h => hs1 h.2)]
      have : ∀ θ : ℝ, G (s, θ) = 0 := by
        intro θ
        have hmem : Complex.polarCoord.symm (s, θ) ∉ ball (0 : ℂ) 1 := by
          rw [mem_ball_zero_iff, Complex.norm_polarCoord_symm, abs_of_pos hs0]; exact hs1
        simp only [hG, hF, indicator_of_notMem hmem, smul_zero]
      simp_rw [this]
      simp
  rw [setIntegral_congr_fun measurableSet_Ioi hin, setIntegral_indicator measurableSet_Ioo,
    show Ioi (0 : ℝ) ∩ Ioo 0 1 = Ioo 0 1 from by
      ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioo]; constructor
      · exact fun h => h.2
      · exact fun h => ⟨h.1, h⟩,
    integral_mul_const, integral_complex_ofReal, mul_comm]

/-- **The weighted mean-value property on the disc**: for `k` holomorphic on the open unit disc and a continuous radial
weight `ρ(|w|)` with `k ρ(|·|)` and `ρ(|·|)` integrable,
`∫_{|w|<1} k(w) ρ(|w|) dA = k(0) ∫_{|w|<1} ρ(|w|) dA`. -/
theorem integral_ball_radial_mul {k : ℂ → ℂ} (hk : DifferentiableOn ℂ k (ball (0 : ℂ) 1)) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hint : IntegrableOn (fun w => k w * (ρ ‖w‖ : ℂ)) (ball (0 : ℂ) 1))
    (hint1 : IntegrableOn (fun w : ℂ => (ρ ‖w‖ : ℂ)) (ball (0 : ℂ) 1)) :
    ∫ w in ball (0 : ℂ) 1, k w * (ρ ‖w‖ : ℂ) = k 0 * ∫ w in ball (0 : ℂ) 1, (ρ ‖w‖ : ℂ) := by
  have h1 := integral_ball_radial hk hρ hint
  have h2 := integral_ball_radial (k := fun _ => (1 : ℂ)) (differentiableOn_const _) hρ
    (by simpa using hint1)
  simp only [one_mul] at h2
  rw [h1, h2]
  simp only [Complex.real_smul, mul_one]
  ring

end Lightlike.Lorentz.SL2RPlancherel
