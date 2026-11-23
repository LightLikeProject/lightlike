import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.AbelSchwartz

/-!
# Every smooth compactly supported function of `cosh t` is an Abel transform

For `P` smooth with compact support there is a smooth compactly supported `F` with
`halfAbel F v = P v` for all `v ≥ 0`, namely a cutoff of `-(1/π) halfAbel P'`
(Abel inversion `halfAbel_halfAbel_deriv`).  Hence `𝒜F (t) = √2 · P (cosh t)`.  This is the first step
of the surjectivity of the spherical Plancherel isometry for `SL(2,ℝ)` (milestone HA3): the range
of the isometry contains the weighted Fourier transforms of all functions `P ∘ cosh`.
-/

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `halfAbel` commutes with multiplication by a complex constant. -/
theorem halfAbel_const_mul (c : ℂ) (g : ℝ → ℂ) (v : ℝ) :
    halfAbel (fun x => c * g x) v = c * halfAbel g v := by
  unfold halfAbel
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [Complex.real_smul]
  ring

/-- `halfAbel f v` only depends on the values of `f` on `(v, ∞)`. -/
theorem halfAbel_congr {f g : ℝ → ℂ} {v : ℝ} (h : ∀ a, v < a → f a = g a) :
    halfAbel f v = halfAbel g v := by
  rw [halfAbel_eq, halfAbel_eq]
  refine setIntegral_congr_fun measurableSet_Ioi (fun a ha => ?_)
  rw [h a ha]

/-- **Surjectivity of the Abel transform onto functions of `cosh t`**: for every smooth compactly
supported `P` there is a smooth compactly supported `F` with `halfAbel F v = P v` for `v ≥ 0`. -/
theorem exists_halfAbel_eq (P : ℝ → ℂ) (hP : ContDiff ℝ ∞ P) (hc : HasCompactSupport P) :
    ∃ F : ℝ → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ ∀ v : ℝ, 0 ≤ v → halfAbel F v = P v := by
  have hdP : ContDiff ℝ ∞ (deriv P) := (contDiff_infty_iff_deriv.1 hP).2
  have hcdP : HasCompactSupport (deriv P) := hc.deriv
  set G : ℝ → ℂ := halfAbel (deriv P) with hG
  have hGs : ContDiff ℝ ∞ G := contDiff_halfAbel _ hdP hcdP
  set F0 : ℝ → ℂ := fun v => (-(1 / π : ℝ) : ℂ) * G v with hF0
  have hF0s : ContDiff ℝ ∞ F0 := contDiff_const.mul hGs
  set χ : ℝ → ℝ := fun v => Real.smoothTransition (v + 1) with hχ
  have hχs : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)
  refine ⟨fun v => (χ v : ℂ) * F0 v, ?_, ?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp hχs).mul hF0s
  · obtain ⟨R, hR⟩ := hcdP.isCompact.isBounded.subset_closedBall (0 : ℝ)
    have hd0 : ∀ x : ℝ, R + 1 ≤ ‖x‖ → deriv P x = 0 := by
      intro x hx
      by_contra hne
      have := hR (subset_tsupport _ hne)
      simp only [Metric.mem_closedBall, dist_zero_right] at this
      linarith
    refine HasCompactSupport.intro (isCompact_Icc (a := -1) (b := |R + 1|)) (fun x hx => ?_)
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · have : χ x = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
      simp [this]
    · have h1 : halfAbel (deriv P) x = 0 :=
        halfAbel_eq_zero_of_support hd0 (le_trans (le_abs_self _) hx.le)
      simp [hF0, hG, h1]
  · intro v hv
    have h1 : halfAbel (fun x => (χ x : ℂ) * F0 x) v = halfAbel F0 v := by
      refine halfAbel_congr (fun a ha => ?_)
      have : χ a = 1 := Real.smoothTransition.one_of_one_le (by linarith)
      simp [this]
    rw [h1, hF0, halfAbel_const_mul, hG, halfAbel_halfAbel_deriv P (hP.of_le (by norm_num)) hc]
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp

/-- The Abel transform of the preimage of `P` is `√2 · P (cosh t)`. -/
theorem exists_abelTransform_eq (P : ℝ → ℂ) (hP : ContDiff ℝ ∞ P) (hc : HasCompactSupport P) :
    ∃ F : ℝ → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      ∀ t : ℝ, abelTransform F t = (√2 : ℂ) * P (Real.cosh t) := by
  obtain ⟨F, hF, hFc, hFP⟩ := exists_halfAbel_eq P hP hc
  refine ⟨F, hF, hFc, fun t => ?_⟩
  rw [abelTransform_eq_halfAbel, hFP _ (Real.cosh_pos t).le]

end Lightlike.Lorentz.SL2RPlancherel
