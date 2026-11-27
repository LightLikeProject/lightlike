import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.AbelSchwartz
import Lightlike.Lorentz.SL2RPlancherel.AbelTransformDeriv
import Lightlike.Lorentz.SL2RPlancherel.PrincipalSpherical

/-!
# The Abel transform of `v · G(v)`

For `G` smooth with compact support and `g = 𝒜G` its Abel transform,

  `𝒜(v G)(t) = cosh t · g(t) + ½ ∫_{s > t} sinh s · g(s) ds`   (`abelTransform_mul_v`).

This is the form, on the Abel side, of multiplication by `v = cosh d` on the hyperbolic plane (the Legendre
recursion `(2μ + 1) v P_μ = (μ + 1) P_{μ+1} + μ P_{μ-1}` on the Fourier side), and is the input that turns the
odd Plancherel identity into a contour shift of the even one (`docs/notes/sl2r-odd-plancherel-route.md`).

The proof differentiates `T(t) = 𝒜(vG)(t) - cosh t · g(t) - ½ ∫_{s>t} sinh s · g(s) ds` and finds
`T' = sinh t · (𝒜(vG')(t) - cosh t · 𝒜(G')(t) + ½ g(t)) = 0`, by one integration by parts in `w`:
`∫ (w²/2) G'(c + w²/2) dw = -½ ∫ G(c + w²/2) dw` (`abelTransform_vderiv`). `T` is constant and vanishes for large `t`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2ROddPlancherel

open Lightlike.Lorentz.SL2RPlancherel

/-- The derivative of the Abel transform: `(𝒜F)'(t) = sinh t · 𝒜(F')(t)`. -/
theorem hasDerivAt_abel (F : ℝ → ℂ) (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) (t : ℝ) :
    HasDerivAt (abelTransform F) ((Real.sinh t : ℂ) * abelTransform (deriv F) t) t := by
  have h := hasDerivAt_abelTransform F hF hc t
  have e : (√2 : ℂ) * (Real.sinh t : ℂ) * halfAbel (deriv F) (Real.cosh t) =
      (Real.sinh t : ℂ) * abelTransform (deriv F) t := by
    rw [abelTransform_eq_halfAbel]; ring
  rwa [e] at h

/-- `∫_{x > s} φ(x) dx` has derivative `-φ(s)` for integrable continuous `φ`. -/
lemma hasDerivAt_integral_Ioi {φ : ℝ → ℂ} (hφ : Continuous φ) (hint : Integrable φ) (t : ℝ) :
    HasDerivAt (fun s => ∫ x in Ioi s, φ x) (-φ t) t := by
  have h := ((hφ.integral_hasStrictDerivAt 0 t).hasDerivAt.neg).const_add (∫ x in Ioi 0, φ x)
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  have := intervalIntegral.integral_Ioi_sub_Ioi' (a := 0) (b := s) hint.integrableOn hint.integrableOn
  simp only [Pi.neg_apply]
  rw [← this]
  ring

/-- **Integration by parts in `w`**: `∫ (w²/2) G'(c + w²/2) dw = -½ ∫ G(c + w²/2) dw`, `c = cosh t`;
in terms of the Abel transform, `𝒜(v G')(t) - cosh t · 𝒜(G')(t) = -½ 𝒜G(t)`. -/
theorem abelTransform_vderiv {G : ℝ → ℂ} (hG : ContDiff ℝ 1 G) (hc : HasCompactSupport G) (t : ℝ) :
    abelTransform (fun v => (v : ℂ) * deriv G v) t - (Real.cosh t : ℂ) * abelTransform (deriv G) t =
      -(1 / 2 : ℂ) * abelTransform G t := by
  set c := Real.cosh t with hcdef
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hd1 : Continuous (deriv G) := hG.continuous_deriv (by norm_num)
  have hu : ∀ w : ℝ, HasDerivAt (fun w : ℝ => (w : ℂ)) 1 w := fun w => (hasDerivAt_id w).ofReal_comp
  have hv : ∀ w : ℝ, HasDerivAt (fun w : ℝ => G (c + w ^ 2 / 2)) ((w : ℂ) * deriv G (c + w ^ 2 / 2)) w := by
    intro w
    have h1 : HasDerivAt (fun w : ℝ => c + w ^ 2 / 2) w w := by
      have := ((hasDerivAt_pow 2 w).div_const 2).const_add c
      convert this using 1; simp
    have h2 := (hGd (c + w ^ 2 / 2)).hasDerivAt
    have := h2.scomp w h1
    refine this.congr_deriv ?_
    simp [Complex.real_smul]
  have hcG : HasCompactSupport fun w : ℝ => G (c + w ^ 2 / 2) := hasCompactSupport_comp_abel hc t
  have hcG' : HasCompactSupport fun w : ℝ => deriv G (c + w ^ 2 / 2) :=
    hasCompactSupport_comp_abel hc.deriv t
  have hcont : Continuous fun w : ℝ => G (c + w ^ 2 / 2) := hG.continuous.comp (by fun_prop)
  have hcont' : Continuous fun w : ℝ => deriv G (c + w ^ 2 / 2) := hd1.comp (by fun_prop)
  have hi1 : Integrable fun w : ℝ => G (c + w ^ 2 / 2) := hcont.integrable_of_hasCompactSupport hcG
  have hi2 : Integrable fun w : ℝ => deriv G (c + w ^ 2 / 2) := hcont'.integrable_of_hasCompactSupport hcG'
  have hi3 : Integrable fun w : ℝ => (w : ℂ) * ((w : ℂ) * deriv G (c + w ^ 2 / 2)) := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_)
    exact (hcG'.mul_left : HasCompactSupport fun w : ℝ => (w : ℂ) * _).mul_left
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun w : ℝ => (w : ℂ))
    (v := fun w : ℝ => G (c + w ^ 2 / 2)) (u' := fun _ => (1 : ℂ))
    (v' := fun w : ℝ => (w : ℂ) * deriv G (c + w ^ 2 / 2)) (fun x _ => hu x) (fun x _ => hv x)
    (by simpa [Pi.mul_def] using hi3)
    (by simpa [Pi.mul_def] using hi1)
    (by
      have : Integrable fun w : ℝ => (w : ℂ) * G (c + w ^ 2 / 2) :=
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) hcG.mul_left)
      simpa [Pi.mul_def] using this)
  simp only [one_mul] at hibp
  have hlin : abelTransform (fun v => (v : ℂ) * deriv G v) t - c * abelTransform (deriv G) t =
      ∫ w : ℝ, (w ^ 2 / 2 : ℂ) * deriv G (c + w ^ 2 / 2) := by
    unfold abelTransform
    rw [← integral_const_mul, ← integral_sub]
    · refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
      ring
    · exact (Continuous.integrable_of_hasCompactSupport (by fun_prop) (hcG'.mul_left))
    · exact hi2.const_mul _
  rw [hlin]
  have e : ∀ w : ℝ, (w ^ 2 / 2 : ℂ) * deriv G (c + w ^ 2 / 2) =
      (1 / 2 : ℂ) * ((w : ℂ) * ((w : ℂ) * deriv G (c + w ^ 2 / 2))) := fun w => by ring
  simp_rw [e]
  rw [integral_const_mul, hibp]
  unfold abelTransform
  ring

/-- A compactly supported function vanishes beyond some point. -/
lemma exists_zero_beyond {f : ℝ → ℂ} (hf : HasCompactSupport f) : ∃ R : ℝ, ∀ t, R < t → f t = 0 := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨R, fun t ht => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
  have := hR hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith [le_abs_self t]

/-- **The Abel transform of `v G(v)`**: `𝒜(vG)(t) = cosh t · 𝒜G(t) + ½ ∫_{s>t} sinh s · 𝒜G(s) ds`
for `G` smooth with compact support. -/
theorem abelTransform_mul_v {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (t : ℝ) :
    abelTransform (fun v => (v : ℂ) * G v) t =
      (Real.cosh t : ℂ) * abelTransform G t +
        (1 / 2 : ℂ) * ∫ s in Ioi t, (Real.sinh s : ℂ) * abelTransform G s := by
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast le_top)
  have hGd : Differentiable ℝ G := hG1.differentiable (by norm_num)
  have hΨ : ContDiff ℝ ∞ (fun v : ℝ => (v : ℂ) * G v) := Complex.ofRealCLM.contDiff.mul hG
  have hΨ1 : ContDiff ℝ 1 (fun v : ℝ => (v : ℂ) * G v) := hΨ.of_le (by exact_mod_cast le_top)
  have hΨc : HasCompactSupport (fun v : ℝ => (v : ℂ) * G v) := hc.mul_left
  have hderiv : deriv (fun v : ℝ => (v : ℂ) * G v) = fun v => G v + (v : ℂ) * deriv G v := by
    funext v
    have hd : HasDerivAt (fun v : ℝ => (v : ℂ) * G v) _ v :=
      (hasDerivAt_id v).ofReal_comp.mul (hGd v).hasDerivAt
    rw [hd.deriv]
    simp
  have hg1 : ContDiff ℝ ∞ (abelTransform G) := contDiff_abelTransform G hG hc
  have hgc : HasCompactSupport (abelTransform G) := hasCompactSupport_abelTransform G hc
  have hφc : Continuous fun s : ℝ => (Real.sinh s : ℂ) * abelTransform G s :=
    (Complex.continuous_ofReal.comp Real.continuous_sinh).mul hg1.continuous
  have hφk : HasCompactSupport fun s : ℝ => (Real.sinh s : ℂ) * abelTransform G s := hgc.mul_left
  have hφi : Integrable fun s : ℝ => (Real.sinh s : ℂ) * abelTransform G s :=
    hφc.integrable_of_hasCompactSupport hφk
  set T : ℝ → ℂ := fun t => abelTransform (fun v => (v : ℂ) * G v) t -
    (Real.cosh t : ℂ) * abelTransform G t -
      (1 / 2 : ℂ) * ∫ s in Ioi t, (Real.sinh s : ℂ) * abelTransform G s with hT
  have hTd : ∀ t, HasDerivAt T 0 t := by
    intro t
    have d1 := hasDerivAt_abel _ hΨ1 hΨc t
    have dg := hasDerivAt_abel G hG1 hc t
    have dcosh : HasDerivAt (fun s : ℝ => (Real.cosh s : ℂ)) (Real.sinh t : ℂ) t :=
      (Real.hasDerivAt_cosh t).ofReal_comp
    have d2 := dcosh.mul dg
    have dK := (hasDerivAt_integral_Ioi hφc hφi t).const_mul (1 / 2 : ℂ)
    have hsum := (d1.sub d2).sub dK
    refine hsum.congr_deriv ?_
    rw [hderiv]
    have hlin : abelTransform (fun v => G v + (v : ℂ) * deriv G v) t =
        abelTransform G t + abelTransform (fun v => (v : ℂ) * deriv G v) t := by
      unfold abelTransform
      refine integral_add ?_ ?_
      · exact (hG.continuous.comp (by fun_prop : Continuous fun w : ℝ => Real.cosh t + w ^ 2 / 2)).integrable_of_hasCompactSupport
          (hasCompactSupport_comp_abel hc t)
      · have hd1 : Continuous (deriv G) := hG1.continuous_deriv (by norm_num)
        exact (Continuous.integrable_of_hasCompactSupport
          (by have := hd1.comp (by fun_prop : Continuous fun w : ℝ => Real.cosh t + w ^ 2 / 2); fun_prop)
          ((hasCompactSupport_comp_abel hc.deriv t).mul_left))
    rw [hlin]
    have hibp := abelTransform_vderiv hG1 hc t
    linear_combination (Real.sinh t : ℂ) * hibp
  have hconst : ∀ x y, T x = T y :=
    is_const_of_deriv_eq_zero (fun x => (hTd x).differentiableAt) fun x => (hTd x).deriv
  obtain ⟨R1, hR1⟩ := exists_zero_beyond (hasCompactSupport_abelTransform _ hΨc)
  obtain ⟨R2, hR2⟩ := exists_zero_beyond hgc
  obtain ⟨R3, hR3⟩ := exists_zero_beyond hφk
  set t₀ := max R1 (max R2 R3) + 1 with ht₀
  have h1 : R1 < t₀ := by have := le_max_left R1 (max R2 R3); linarith
  have h2 : R2 < t₀ := by have := le_max_left R2 R3; have := le_max_right R1 (max R2 R3); linarith
  have h3 : R3 < t₀ := by have := le_max_right R2 R3; have := le_max_right R1 (max R2 R3); linarith
  have hT0 : T t₀ = 0 := by
    simp only [hT]
    have hK0 : ∫ s in Ioi t₀, (Real.sinh s : ℂ) * abelTransform G s = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun s (hs : t₀ < s) => hR3 s (lt_trans h3 hs)
    rw [hR1 t₀ h1, hR2 t₀ h2, hK0]
    simp
  have := hconst t t₀
  rw [hT0] at this
  simp only [hT] at this
  linear_combination this

end Lightlike.Lorentz.SL2ROddPlancherel
