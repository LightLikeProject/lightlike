module

public import Lightlike.Lorentz.SL2RPlancherel.DiscMeanValue
public import Lightlike.Lorentz.SL2RPlancherel.DiscCircleMode

/-!
# Integrals over the unit disc against a Fourier mode

For `k` holomorphic on the open unit disc, a continuous radial weight `ρ(|w|)` and `m ∈ ℕ`,
`∫_{|w|<1} k(w) conj(w)^m ρ(|w|) dA = 2π a_m ∫_0^1 s^{2m+1} ρ(s) ds`, with `a_m = discCoeff k m` the `m`-th Taylor
coefficient of `k` at `0` (`integral_ball_mode`). For `m = 0` this is the weighted mean-value property
`integral_ball_radial` (`a_0 = k(0)`).
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- On the polar parametrisation the conjugate power is `s^m e^{-imθ}`. -/
lemma conj_polar_pow (m : ℕ) (s θ : ℝ) :
    (starRingEnd ℂ (Complex.polarCoord.symm (s, θ))) ^ m =
      (s : ℂ) ^ m * Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I)) := by
  have h1 : starRingEnd ℂ (Complex.polarCoord.symm (s, θ)) =
      (s : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)) := by
    rw [Complex.polarCoord_symm_apply]
    rw [show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
    ring
  rw [h1, mul_pow, ← Complex.exp_nat_mul]
  congr 2
  ring

/-- **The disc integral against a Fourier mode**: for `k` holomorphic on the open unit disc, a continuous radial weight
and `m ∈ ℕ`, `∫_{|w|<1} k(w) conj(w)^m ρ(|w|) dA = 2π a_m ∫_0^1 s^{2m+1} ρ(s) ds`. -/
theorem integral_ball_mode {k : ℂ → ℂ} (hk : DifferentiableOn ℂ k (ball (0 : ℂ) 1)) (m : ℕ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ)
    (hint : IntegrableOn (fun w => k w * (starRingEnd ℂ w) ^ m * (ρ ‖w‖ : ℂ)) (ball (0 : ℂ) 1)) :
    ∫ w in ball (0 : ℂ) 1, k w * (starRingEnd ℂ w) ^ m * (ρ ‖w‖ : ℂ) =
      (2 * π : ℂ) * discCoeff k m * ((∫ s in Ioo (0 : ℝ) 1, s ^ (2 * m + 1) * ρ s : ℝ) : ℂ) := by
  classical
  set F : ℂ → ℂ := (ball (0 : ℂ) 1).indicator (fun w => k w * (starRingEnd ℂ w) ^ m * (ρ ‖w‖ : ℂ)) with hF
  have hFm : Measurable F := by
    rw [hF, ← Set.piecewise_eq_indicator]
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const measurableSet_ball
    exact (hk.continuousOn.mul ((Complex.continuous_conj.pow m)).continuousOn).mul
      (Complex.continuous_ofReal.comp (hρ.comp continuous_norm)).continuousOn
  have hFi : Integrable F := (integrable_indicator_iff measurableSet_ball).2 hint
  have hpol := Complex.integral_comp_polarCoord_symm F
  have hFint : ∫ p, F p = ∫ w in ball (0 : ℂ) 1, k w * (starRingEnd ℂ w) ^ m * (ρ ‖w‖ : ℂ) := integral_indicator measurableSet_ball
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
      (Ioo (0 : ℝ) 1).indicator (fun s => ((s ^ (2 * m + 1) * ρ s : ℝ) : ℂ) * ((2 * π : ℂ) * discCoeff k m)) s := by
    intro s hs
    have hs0 : 0 < s := hs
    by_cases hs1 : s < 1
    · have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨hs0, hs1⟩
      rw [indicator_of_mem hsI]
      have : ∀ θ : ℝ, G (s, θ) = ((s ^ (m + 1) * ρ s : ℝ) : ℂ) *
          (k (Complex.polarCoord.symm (s, θ)) * Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I))) := by
        intro θ
        have hmem : Complex.polarCoord.symm (s, θ) ∈ ball (0 : ℂ) 1 := by
          rw [mem_ball_zero_iff, Complex.norm_polarCoord_symm]; simpa [abs_of_pos hs0] using hs1
        simp only [hG, hF, indicator_of_mem hmem, Complex.norm_polarCoord_symm, abs_of_pos hs0,
          Complex.real_smul, conj_polar_pow]
        push_cast
        ring
      simp_rw [this]
      rw [integral_const_mul, integral_polar_mode hk m hsI]
      push_cast
      ring
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
    integral_mul_const, integral_complex_ofReal]
  ring

end Lightlike.Lorentz.SL2RPlancherel
