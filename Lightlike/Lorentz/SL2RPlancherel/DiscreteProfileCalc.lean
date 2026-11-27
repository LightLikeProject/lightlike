module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileDeriv

/-!
# The ladder relations for the profile polynomials of the discrete series

`P_{jl}(t) = discCoeff (genFun n l t) j` is differentiable in `t ∈ (-1, 1)` with derivative the `j`-th Taylor
coefficient of `∂_t G_l` (`hasDerivAt_profPoly`), and `discCoeff (w ∂_w h) j = j discCoeff h j`
(`discCoeff_mul_deriv`); with the pointwise identities of `DiscreteProfileDeriv` this gives
`t (1 - t²) P_{j,k+1}' + ((k+1) (1 + t²) - j (1 - t²)) P_{j,k+1} = 2 (k+1) t P_{jk}` (`profPoly_lower`) and
`t (1 - t²) P_{jl}' + (j (1 - t²) - l (1 + t²) - 2 n t²) P_{jl} = -2 (n + l) t P_{j,l+1}` (`profPoly_raise`).
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real Filter Topology Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

lemma differentiableOn_genFunT (n l : ℕ) {t : ℝ} (ht : |t| < 1) :
    DifferentiableOn ℂ (genFunT n l t) (ball (0 : ℂ) 1) := by
  intro w hw
  refine DifferentiableAt.differentiableWithinAt ?_
  have hV := pow_ne_zero (n + l) (one_add_mul_ne_zero ht hw)
  have hV' := pow_ne_zero (n + l + 1) (one_add_mul_ne_zero ht hw)
  unfold genFunT
  refine DifferentiableAt.sub ?_ ?_
  · exact (DifferentiableAt.mul (by fun_prop) (DifferentiableAt.inv (by fun_prop) hV))
  · exact DifferentiableAt.mul (by fun_prop) (DifferentiableAt.inv (by fun_prop) hV')

lemma discCoeff_add {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1)) (m : ℕ) :
    discCoeff (fun w => f w + g w) m = discCoeff f m + discCoeff g m := by
  have hs : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1 := integral_circleMap_mode hf m hs
  have h2 := integral_circleMap_mode hg m hs
  have h3 := integral_circleMap_mode (h := fun w => f w + g w) (hf.add hg) m hs
  have hcont : ∀ k : ℂ → ℂ, DifferentiableOn ℂ k (ball (0 : ℂ) 1) →
      IntervalIntegrable (fun θ : ℝ => k (circleMap 0 (1 / 2) θ) *
        Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I))) volume 0 (2 * π) := by
    intro k hk
    refine Continuous.intervalIntegrable ?_ _ _
    refine Continuous.mul ?_ (by fun_prop)
    refine hk.continuousOn.comp_continuous (continuous_circleMap 0 (1 / 2)) (fun θ => ?_)
    rw [mem_ball_zero_iff, norm_circleMap_zero]; norm_num
  have h4 : ∫ θ in (0 : ℝ)..2 * π, (f (circleMap 0 (1 / 2) θ) + g (circleMap 0 (1 / 2) θ)) *
      Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I)) =
      (∫ θ in (0 : ℝ)..2 * π, f (circleMap 0 (1 / 2) θ) * Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I))) +
      ∫ θ in (0 : ℝ)..2 * π, g (circleMap 0 (1 / 2) θ) * Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I)) := by
    rw [← intervalIntegral.integral_add (hcont f hf) (hcont g hg)]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [add_mul]
  rw [h4, h1, h2] at h3
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hne : (2 * π : ℂ) * (((1 / 2 : ℝ) : ℂ) ^ m) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (by norm_num)))
  have : (2 * π : ℂ) * (((1 / 2 : ℝ) : ℂ) ^ m) * discCoeff (fun w => f w + g w) m =
      (2 * π : ℂ) * (((1 / 2 : ℝ) : ℂ) ^ m) * (discCoeff f m + discCoeff g m) := by
    linear_combination (-1 : ℂ) * h3
  exact mul_left_cancel₀ hne this

lemma discCoeff_sub {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1)) (m : ℕ) :
    discCoeff (fun w => f w - g w) m = discCoeff f m - discCoeff g m := by
  have h1 := discCoeff_add hf (hg.const_mul (-1)) m
  have h2 := discCoeff_const_mul hg (-1) m
  have e : (fun w => f w - g w) = fun w => f w + (-1) * g w := by funext w; ring
  rw [e, h1, h2]; ring

/-- **The multiplication by `j` on Taylor coefficients**: `discCoeff (w ∂_w h) j = j · discCoeff h j`. -/
lemma discCoeff_mul_deriv {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball (0 : ℂ) 1)) (m : ℕ) :
    discCoeff (fun w => w * deriv h w) m = (m : ℂ) * discCoeff h m := by
  have hs : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hmem : ∀ θ : ℝ, circleMap 0 (1 / 2) θ ∈ ball (0 : ℂ) 1 := fun θ => by
    rw [mem_ball_zero_iff, norm_circleMap_zero]; norm_num
  have hdiff : DifferentiableOn ℂ (deriv h) (ball (0 : ℂ) 1) :=
    (hh.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hh2 : DifferentiableOn ℂ (fun w => w * deriv h w) (ball (0 : ℂ) 1) :=
    differentiableOn_id.mul hdiff
  have h1 := integral_circleMap_mode hh2 m hs
  have h0 := integral_circleMap_mode hh m hs
  set E : ℝ → ℂ := fun θ => Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I)) with hE
  set H : ℝ → ℂ := fun θ => h (circleMap 0 (1 / 2) θ) with hH
  set H' : ℝ → ℂ := fun θ => deriv h (circleMap 0 (1 / 2) θ) * (circleMap 0 (1 / 2) θ * Complex.I) with hH'
  have hHd : ∀ θ, HasDerivAt H (H' θ) θ := by
    intro θ
    have hd : HasDerivAt h (deriv h (circleMap 0 (1 / 2) θ)) (circleMap 0 (1 / 2) θ) :=
      (hh.differentiableAt (isOpen_ball.mem_nhds (hmem θ))).hasDerivAt
    have hc : HasDerivAt (circleMap 0 (1 / 2)) (circleMap 0 (1 / 2) θ * Complex.I) θ :=
      hasDerivAt_circleMap 0 (1 / 2) θ
    exact (hd.scomp θ hc).congr_deriv (by simp only [hH', smul_eq_mul]; ring)
  have hEd : ∀ θ, HasDerivAt E (-((m : ℂ) * Complex.I) * E θ) θ := by
    intro θ
    have h0 : HasDerivAt (fun θ : ℝ => (m : ℂ) * (θ : ℂ) * Complex.I) ((m : ℂ) * 1 * Complex.I) θ :=
      ((hasDerivAt_id θ).ofReal_comp.const_mul (m : ℂ)).mul_const Complex.I
    have h1' : HasDerivAt (fun θ : ℝ => -((m : ℂ) * (θ : ℂ) * Complex.I)) (-((m : ℂ) * Complex.I)) θ :=
      (h0.neg).congr_deriv (by ring)
    exact (h1'.cexp).congr_deriv (by ring)
  have hcontH' : Continuous H' := by
    refine Continuous.mul ?_ (by fun_prop)
    exact hdiff.continuousOn.comp_continuous (continuous_circleMap 0 (1 / 2)) hmem
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * π)
    (u := E) (v := H) (u' := fun θ => -((m : ℂ) * Complex.I) * E θ) (v' := H')
    (fun θ _ => hEd θ) (fun θ _ => hHd θ)
    (Continuous.intervalIntegrable (by simp only [hE]; fun_prop) _ _)
    (Continuous.intervalIntegrable hcontH' _ _)
  have hE2 : E (2 * π) = 1 := by
    simp only [hE]
    have : -((m : ℂ) * ((2 * π : ℝ) : ℂ) * Complex.I) = ((-(m : ℤ) : ℤ) : ℂ) * (2 * π * Complex.I) := by
      push_cast; ring
    rw [this]; exact Complex.exp_int_mul_two_pi_mul_I _
  have hE0 : E 0 = 1 := by simp [hE]
  have hH2 : H (2 * π) = H 0 := by
    simp only [hH]
    have := (periodic_circleMap (0 : ℂ) (1 / 2)) 0
    rw [zero_add] at this
    rw [this]
  rw [hE2, hE0, hH2] at hibp
  simp only [one_mul, sub_self, zero_sub] at hibp
  -- hibp : ∫ E * H' = -∫ (-(m I) E) H
  have hlhs : ∫ θ in (0 : ℝ)..2 * π, (circleMap 0 (1 / 2) θ * deriv h (circleMap 0 (1 / 2) θ)) * E θ =
      -Complex.I * ∫ θ in (0 : ℝ)..2 * π, E θ * H' θ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [hH']
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (E θ * deriv h (circleMap 0 (1 / 2) θ) * circleMap 0 (1 / 2) θ) * this
  have hrhs : ∫ θ in (0 : ℝ)..2 * π, E θ * H' θ =
      Complex.I * (m : ℂ) * ∫ θ in (0 : ℝ)..2 * π, H θ * E θ := by
    rw [hibp, ← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    ring
  have key : ∫ θ in (0 : ℝ)..2 * π, (circleMap 0 (1 / 2) θ * deriv h (circleMap 0 (1 / 2) θ)) * E θ =
      (m : ℂ) * ∫ θ in (0 : ℝ)..2 * π, H θ * E θ := by
    rw [hlhs, hrhs]
    have : -Complex.I * (Complex.I * (m : ℂ)) = (m : ℂ) := by
      linear_combination (-(m : ℂ)) * Complex.I_mul_I
    rw [← mul_assoc, this]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hne : (2 * π : ℂ) * (((1 / 2 : ℝ) : ℂ) ^ m) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (by norm_num)))
  have h1' : ∫ θ in (0 : ℝ)..2 * π, (circleMap 0 (1 / 2) θ * deriv h (circleMap 0 (1 / 2) θ)) * E θ =
      2 * π * (((1 / 2 : ℝ) : ℂ) ^ m * discCoeff (fun w => w * deriv h w) m) := h1
  have h0' : ∫ θ in (0 : ℝ)..2 * π, H θ * E θ = 2 * π * (((1 / 2 : ℝ) : ℂ) ^ m * discCoeff h m) := h0
  rw [h1', h0'] at key
  have : (2 * π : ℂ) * (((1 / 2 : ℝ) : ℂ) ^ m) * discCoeff (fun w => w * deriv h w) m =
      (2 * π : ℂ) * (((1 / 2 : ℝ) : ℂ) ^ m) * ((m : ℂ) * discCoeff h m) := by
    linear_combination key
  exact mul_left_cancel₀ hne this

end Lightlike.Lorentz.SL2RPlancherel
