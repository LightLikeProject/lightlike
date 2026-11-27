import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.CasimirSymmetry
import Lightlike.Lorentz.SL2RPlancherel.WeakDeriv

/-!
# The radial Casimir is symmetric against test functions

For `χ` smooth with compact support in `(0, ∞)` and `G` twice continuously differentiable on
`(0, ∞)`, `∫_{(0,∞)} (L χ) conj G sinh = ∫_{(0,∞)} χ conj (L G) sinh` (`integral_radialCasimir_test`):
the boundary form vanishes at the ends of an interval containing the support.
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (opposite-sign blocks), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

lemma radialCasimir_eq_zero_of_eventuallyEq {l r : ℝ} {χ : ℝ → ℂ} {x : ℝ}
    (h : χ =ᶠ[nhds x] fun _ => (0 : ℂ)) : radialCasimir l r χ x = 0 := by
  have h1 : deriv χ =ᶠ[nhds x] fun _ => (0 : ℂ) := by
    filter_upwards [h.eventually_nhds] with y hy
    have hy' : χ =ᶠ[nhds y] fun _ => (0 : ℂ) := hy
    rw [hy'.deriv_eq, deriv_const]
  unfold radialCasimir
  rw [h1.deriv_eq, deriv_const, h1.self_of_nhds, h.self_of_nhds]
  simp

/-- **Symmetry of the radial Casimir against a test function.** -/
theorem integral_radialCasimir_test (l r : ℝ) {χ G : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hsub : tsupport χ ⊆ Ioi 0) (hG : ContDiffOn ℝ 2 G (Ioi 0)) :
    ∫ x in Ioi 0, radialCasimir l r χ x * (starRingEnd ℂ) (G x) * (Real.sinh x : ℂ) =
      ∫ x in Ioi 0, χ x * (starRingEnd ℂ) (radialCasimir l r G x) * (Real.sinh x : ℂ) := by
  rcases (tsupport χ).eq_empty_or_nonempty with he | hne
  · have h0 : χ = 0 := tsupport_eq_empty_iff.1 he
    subst h0
    have hL : ∀ x, radialCasimir l r (0 : ℝ → ℂ) x = 0 := fun x =>
      radialCasimir_eq_zero_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
    simp [hL]
  obtain ⟨s₀, hs₀, s₁, -, hs, hS⟩ := exists_Icc_of_isCompact hc.isCompact hne
  have hs₀0 : 0 < s₀ := hsub hs₀
  have hout : ∀ x, x ∉ Icc s₀ s₁ → χ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hS h)
  -- `χ` vanishes near every point outside `[s₀, s₁]`
  have hloc : ∀ x, x < s₀ ∨ s₁ < x → χ =ᶠ[nhds x] fun _ => (0 : ℂ) := by
    intro x hx
    rcases hx with hx | hx
    · filter_upwards [Iio_mem_nhds hx] with y hy using hout y fun h => absurd h.1 (not_le.2 hy)
    · filter_upwards [Ioi_mem_nhds hx] with y hy using hout y fun h => absurd h.2 (not_le.2 hy)
  set a := s₀ / 2 with ha
  set b := s₁ + 1 with hb
  have ha0 : 0 < a := by positivity
  have hab : a ≤ b := by linarith
  have hχc : ContDiffOn ℝ 2 χ (Ioi 0) := (hχ.of_le (by norm_cast)).contDiffOn
  -- both integrands vanish outside `(a, b]`
  have hred : ∀ f : ℝ → ℂ, (∀ x, 0 < x → (x < s₀ ∨ s₁ < x) → f x = 0) →
      ∫ x in Ioi 0, f x = ∫ x in a..b, f x := by
    intro f hf
    rw [intervalIntegral.integral_of_le hab]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => lt_trans ha0 hx.1) fun x hx => hf x hx.1 ?_
    by_contra h
    push Not at h
    exact hx.2 ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [hred _ fun x _ hx => by rw [radialCasimir_eq_zero_of_eventuallyEq (hloc x hx)]; simp,
    hred _ fun x _ hx => by rw [(hloc x hx).self_of_nhds]; simp]
  have hsymm := integral_radialCasimir_symm l r ha0 hab hχc hG
  have hBa : casBdry χ G a = 0 := by
    have h := hloc a (Or.inl (by linarith))
    have hd : deriv χ a = 0 := by rw [h.deriv_eq, deriv_const]
    simp [casBdry, h.self_of_nhds, hd]
  have hBb : casBdry χ G b = 0 := by
    have h := hloc b (Or.inr (by linarith))
    have hd : deriv χ b = 0 := by rw [h.deriv_eq, deriv_const]
    simp [casBdry, h.self_of_nhds, hd]
  rw [hBa, hBb, sub_zero] at hsymm
  have hsub' : uIcc a b ⊆ Ioi 0 := by
    rw [uIcc_of_le hab]; exact fun x hx => lt_of_lt_of_le ha0 hx.1
  have hi1 : IntervalIntegrable (fun x => radialCasimir l r χ x * (starRingEnd ℂ) (G x) *
      (Real.sinh x : ℂ)) volume a b :=
    ContinuousOn.intervalIntegrable ((((continuousOn_radialCasimir l r hχc).mul
      (Complex.continuous_conj.comp_continuousOn hG.continuousOn)).mul
      (Complex.continuous_ofReal.comp Real.continuous_sinh).continuousOn).mono hsub')
  have hi2 : IntervalIntegrable (fun x => χ x * (starRingEnd ℂ) (radialCasimir l r G x) *
      (Real.sinh x : ℂ)) volume a b :=
    ContinuousOn.intervalIntegrable (((hχc.continuousOn.mul (Complex.continuous_conj.comp_continuousOn
      (continuousOn_radialCasimir l r hG))).mul
      (Complex.continuous_ofReal.comp Real.continuous_sinh).continuousOn).mono hsub')
  have e : (fun x => (radialCasimir l r χ x * (starRingEnd ℂ) (G x) -
      χ x * (starRingEnd ℂ) (radialCasimir l r G x)) * (Real.sinh x : ℂ)) =
      fun x => radialCasimir l r χ x * (starRingEnd ℂ) (G x) * (Real.sinh x : ℂ) -
        χ x * (starRingEnd ℂ) (radialCasimir l r G x) * (Real.sinh x : ℂ) := by
    funext x; ring
  rw [e, intervalIntegral.integral_sub hi1 hi2] at hsymm
  exact sub_eq_zero.1 hsymm

/-- **The Casimir of a test function supported in `(0, ∞)` is again one.** -/
theorem radialCasimir_test (l r : ℝ) {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hsub : tsupport χ ⊆ Ioi 0) :
    ContDiff ℝ ∞ (radialCasimir l r χ) ∧ HasCompactSupport (radialCasimir l r χ) ∧
      tsupport (radialCasimir l r χ) ⊆ Ioi 0 := by
  rcases (tsupport χ).eq_empty_or_nonempty with he | hne
  · have h0 : χ = 0 := tsupport_eq_empty_iff.1 he
    subst h0
    have hL : radialCasimir l r (0 : ℝ → ℂ) = 0 := funext fun x =>
      radialCasimir_eq_zero_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
    rw [hL]
    exact ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  obtain ⟨s₀, hs₀, s₁, -, hs, hS⟩ := exists_Icc_of_isCompact hc.isCompact hne
  have hs₀0 : 0 < s₀ := hsub hs₀
  have hout : ∀ x, x ∉ Icc s₀ s₁ → χ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hS h)
  have hloc : ∀ x, x < s₀ ∨ s₁ < x → χ =ᶠ[nhds x] fun _ => (0 : ℂ) := by
    intro x hx
    rcases hx with hx | hx
    · filter_upwards [Iio_mem_nhds hx] with y hy using hout y fun h => absurd h.1 (not_le.2 hy)
    · filter_upwards [Ioi_mem_nhds hx] with y hy using hout y fun h => absurd h.2 (not_le.2 hy)
  have hzero : ∀ x, x ∉ Icc s₀ s₁ → radialCasimir l r χ x = 0 := fun x hx => by
    refine radialCasimir_eq_zero_of_eventuallyEq (hloc x ?_)
    by_contra h
    push Not at h
    exact hx ⟨h.1, h.2⟩
  refine ⟨?_, HasCompactSupport.intro isCompact_Icc hzero, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : 0 < x
    · have hd1 : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.1 hχ).2
      have hd2 : ContDiff ℝ ∞ (deriv (deriv χ)) := (contDiff_infty_iff_deriv.1 hd1).2
      have hs : ∀ y ∈ Ioi (0 : ℝ), Real.sinh y ≠ 0 := fun y hy => (Real.sinh_pos_iff.2 hy).ne'
      have hcoth : ContDiffOn ℝ ∞ (fun y : ℝ => ((Real.cosh y / Real.sinh y : ℝ) : ℂ)) (Ioi 0) :=
        Complex.ofRealCLM.contDiff.comp_contDiffOn
          (Real.contDiff_cosh.contDiffOn.div Real.contDiff_sinh.contDiffOn hs)
      have hV : ContDiffOn ℝ ∞ (fun y : ℝ =>
          (((l ^ 2 + r ^ 2 + 2 * l * r * Real.cosh y) / Real.sinh y ^ 2 : ℝ) : ℂ)) (Ioi 0) :=
        Complex.ofRealCLM.contDiff.comp_contDiffOn
          ((contDiff_const.add (contDiff_const.mul Real.contDiff_cosh)).contDiffOn.div
            (Real.contDiff_sinh.pow 2).contDiffOn fun y hy => pow_ne_zero 2 (hs y hy))
      have hon : ContDiffOn ℝ ∞ (radialCasimir l r χ) (Ioi 0) := by
        unfold radialCasimir
        exact ((hd2.contDiffOn.neg).sub (hcoth.mul hd1.contDiffOn)).add (hV.mul hχ.contDiffOn)
      exact hon.contDiffAt (Ioi_mem_nhds hx)
    · push Not at hx
      refine (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℂ)) x).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds (show x < s₀ by linarith)] with y hy
      exact hzero y fun h => absurd h.1 (not_le.2 hy)
  · refine (closure_minimal (t := Icc s₀ s₁) (fun x hx => ?_) isClosed_Icc).trans
      (fun x hx => lt_of_lt_of_le hs₀0 hx.1)
    by_contra h
    exact hx (hzero x h)

end Lightlike.Lorentz.SL2RPlancherel
