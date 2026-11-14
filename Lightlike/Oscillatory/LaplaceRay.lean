module

public import Mathlib

/-!
# Laplace's method on a ray, with an explicit uniform constant

For a complex phase `φ` on `[0, r]` that behaves like `-a t² / 2` near `0`
(`‖φ t + a t² / 2‖ ≤ M t³`) and is uniformly damped (`Re φ t ≤ -c t²`), and an amplitude `g`
that is Lipschitz at `0`, the one-sided Laplace integral satisfies

`‖∫₀ʳ g t e^{N φ t} dt - g 0 · (π / (N a / 2))^{1/2} / 2‖ ≤ C / N`  for all `N > 0`,

with a constant `C` that depends only on `r, α, M, c, K, G` (with `α ≤ Re a`, `‖g 0‖ ≤ G`,
`K` the Lipschitz constant of `g` at `0`). The leading term is the half-line Gaussian integral
`∫₀^∞ e^{-N a t² / 2} dt`, Mathlib's `integral_gaussian_complex_Ioi`.

This is the one-dimensional case of Laplace's method with a complex phase; see Olver,
*Asymptotics and Special Functions* (1974), Ch. 3, §7 (Laplace's method for contour integrals,
Theorem 7.1), and Hörmander, *The Analysis of Linear Partial Differential Operators I*,
Theorem 7.7.5 (the general stationary-phase theorem with `Im φ ≥ 0`). The uniform form, with `C`
independent of `a, φ, g` within the stated bounds, is what a consumer needs when the phase and
amplitude depend on further parameters.

## Main results

* `laplace_ray_uniform`: the bound above, with
  `C = K / (2 c) + G M / (2 c'²) + G / (α r)` and `c' = min c (α / 2)`.

## Proof

Split `∫₀^∞ e^{-b t²}` (`b = N a / 2`) at `r`. The difference with the integral on `[0, r]` is
`∫₀ʳ (g t - g 0) e^{Nφ} + g 0 ∫₀ʳ (e^{Nφ} - e^{-b t²}) - g 0 ∫ᵣ^∞ e^{-b t²}`, and the three
pieces are bounded by `K / (2 c N)`, `G M / (2 c'² N)` and `G / (α r N)`, using
`|e^u - e^v| ≤ |u - v| e^{max (Re u) (Re v)}` for the middle one.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace Lightlike.Oscillatory

/-- `∫₀ʳ t e^{-β t²} dt ≤ 1 / (2 β)` for `β > 0` and every `r`. -/
theorem integral_mul_exp_neg_sq_le {β : ℝ} (hβ : 0 < β) (r : ℝ) :
    ∫ t in (0 : ℝ)..r, t * Real.exp (-β * t ^ 2) ≤ 1 / (2 * β) := by
  have hderiv : ∀ x ∈ uIcc 0 r, HasDerivAt (fun t => -Real.exp (-β * t ^ 2) / (2 * β))
      (x * Real.exp (-β * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun t => -β * t ^ 2) (-β * (2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul (-β)
    convert h1.exp.neg.div_const (2 * β) using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have := Real.exp_pos (-β * r ^ 2)
  have h2 : 0 < 2 * β := by positivity
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Real.exp_zero]
  rw [div_sub_div_same, div_le_div_iff_of_pos_right h2]
  linarith

/-- `∫₀ʳ t³ e^{-β t²} dt ≤ 1 / (2 β²)` for `β > 0` and every `r`. -/
theorem integral_pow_three_mul_exp_neg_sq_le {β : ℝ} (hβ : 0 < β) (r : ℝ) :
    ∫ t in (0 : ℝ)..r, t ^ 3 * Real.exp (-β * t ^ 2) ≤ 1 / (2 * β ^ 2) := by
  have hderiv : ∀ x ∈ uIcc 0 r,
      HasDerivAt (fun t => -((β * t ^ 2 + 1) * Real.exp (-β * t ^ 2)) / (2 * β ^ 2))
      (x ^ 3 * Real.exp (-β * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun t => -β * t ^ 2) (-β * (2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul (-β)
    have h3 : HasDerivAt (fun t => β * t ^ 2 + 1) (β * (2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul β).add_const 1
    convert ((h3.mul h1.exp).neg).div_const (2 * β ^ 2) using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have := Real.exp_pos (-β * r ^ 2)
  have h2 : 0 < 2 * β ^ 2 := by positivity
  have h4 : 0 ≤ β * r ^ 2 + 1 := by positivity
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Real.exp_zero,
    zero_add, mul_one]
  rw [div_sub_div_same, div_le_div_iff_of_pos_right h2]
  nlinarith [mul_nonneg h4 this.le]

/-- Gaussian tail: `∫ᵣ^∞ e^{-β t²} dt ≤ 1 / (2 β r)` for `β, r > 0`. -/
theorem integral_Ioi_exp_neg_sq_le {β r : ℝ} (hβ : 0 < β) (hr : 0 < r) :
    ∫ t in Ioi r, Real.exp (-β * t ^ 2) ≤ 1 / (2 * β * r) := by
  have hderiv : ∀ x ∈ Ici r, HasDerivAt (fun t => -Real.exp (-β * t ^ 2) / (2 * β))
      (x * Real.exp (-β * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun t => -β * t ^ 2) (-β * (2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul (-β)
    convert h1.exp.neg.div_const (2 * β) using 1
    field_simp
  have hlim : Tendsto (fun t => -Real.exp (-β * t ^ 2) / (2 * β)) atTop (𝓝 (-0 / (2 * β))) := by
    refine ((Real.tendsto_exp_atBot.comp ?_).neg).div_const _
    exact (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.2 hβ)
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrable_mul_exp_neg_mul_sq hβ).integrableOn hlim
  have hint : IntegrableOn (fun t => Real.exp (-β * t ^ 2)) (Ioi r) :=
    (integrable_exp_neg_mul_sq hβ).integrableOn
  calc ∫ t in Ioi r, Real.exp (-β * t ^ 2)
      ≤ ∫ t in Ioi r, r⁻¹ * (t * Real.exp (-β * t ^ 2)) := by
        refine setIntegral_mono_on hint
          ((integrable_mul_exp_neg_mul_sq hβ).integrableOn.const_mul _) measurableSet_Ioi ?_
        intro t ht
        have ht' : r < t := ht
        rw [← mul_assoc]
        refine le_mul_of_one_le_left (Real.exp_pos _).le ?_
        rw [inv_mul_eq_div, one_le_div hr]
        exact ht'.le
    _ = r⁻¹ * (Real.exp (-β * r ^ 2) / (2 * β)) := by
        rw [integral_const_mul, hval]
        ring
    _ ≤ r⁻¹ * (1 / (2 * β)) := by
        gcongr
        rw [Real.exp_le_one_iff]
        nlinarith [sq_nonneg r]
    _ = 1 / (2 * β * r) := by field_simp

/-- Lipschitz bound for the complex exponential on a half-plane:
`‖e^u - e^v‖ ≤ e^{max (Re u) (Re v)} ‖u - v‖`. -/
theorem norm_cexp_sub_le (u v : ℂ) :
    ‖cexp u - cexp v‖ ≤ Real.exp (max u.re v.re) * ‖u - v‖ := by
  set m := max u.re v.re
  have hs : Convex ℝ {w : ℂ | w.re ≤ m} := convex_halfSpace_re_le m
  refine hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w _ => (Complex.hasDerivAt_exp w).hasDerivWithinAt) ?_
    (show v.re ≤ m from le_max_right _ _) (show u.re ≤ m from le_max_left _ _)
  intro w hw
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr hw

/-- **Laplace's method on a ray, uniform form.** Let `φ, g : [0, r] → ℂ` be continuous, with
`‖φ t + a t² / 2‖ ≤ M t³`, `Re φ t ≤ -c t²`, `‖g t - g 0‖ ≤ K t` and `‖g 0‖ ≤ G`, where
`Re a ≥ α > 0`. Then for every `N > 0`

`‖∫₀ʳ g t e^{N φ t} dt - g 0 · (π / (N a / 2))^{1/2} / 2‖ ≤ C / N`,

with `C` depending only on `r, α, M, c, K, G` (not on `a, φ, g, N`). The leading term is
`g 0 ∫₀^∞ e^{-N a t² / 2} dt` (principal branch of the square root, `Re (N a / 2) > 0`).

Source: Laplace's method with a complex phase, Olver, *Asymptotics and Special Functions*
(1974), Ch. 3, §7, Theorem 7.1 (one-sided endpoint at a nondegenerate minimum of `-Re φ`), in
the uniform form needed for parameter-dependent phases; the `n`-dimensional version is
Hörmander, *The Analysis of Linear Partial Differential Operators I*, Theorem 7.7.5. -/
theorem laplace_ray_uniform (r α M c K G : ℝ) (hr : 0 < r) (hα : 0 < α) (hc : 0 < c) :
    ∃ C : ℝ, ∀ (a : ℂ) (φ g : ℝ → ℂ), α ≤ a.re →
      ContinuousOn φ (Icc 0 r) → ContinuousOn g (Icc 0 r) →
      (∀ t ∈ Icc 0 r, ‖φ t + a * t ^ 2 / 2‖ ≤ M * t ^ 3) →
      (∀ t ∈ Icc 0 r, (φ t).re ≤ -c * t ^ 2) →
      (∀ t ∈ Icc 0 r, ‖g t - g 0‖ ≤ K * t) → ‖g 0‖ ≤ G →
      ∀ N : ℝ, 0 < N →
        ‖(∫ t in (0 : ℝ)..r, g t * cexp (N * φ t)) -
            g 0 * ((π / (N * a / 2)) ^ (1 / 2 : ℂ) / 2)‖ ≤ C / N := by
  set c' := min c (α / 2) with hc'def
  have hc' : 0 < c' := lt_min hc (by linarith)
  refine ⟨K / (2 * c) + G * M / (2 * c' ^ 2) + G / (α * r), ?_⟩
  intro a φ g ha hφ hg hφa hφre hgK hgG N hN
  have hrmem : r ∈ Icc 0 r := ⟨hr.le, le_rfl⟩
  have hr3 : 0 < r ^ 3 := by positivity
  have hM : 0 ≤ M := by
    have := (norm_nonneg _).trans (hφa r hrmem)
    nlinarith
  have hK : 0 ≤ K := by
    have := (norm_nonneg _).trans (hgK r hrmem)
    nlinarith
  have hG : 0 ≤ G := (norm_nonneg _).trans hgG
  have hN0 : N ≠ 0 := hN.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have hc'0 : c' ≠ 0 := hc'.ne'
  set b : ℂ := (N : ℂ) * a / 2 with hbdef
  have hbre : b.re = N * a.re / 2 := by
    rw [hbdef, Complex.div_ofNat_re, Complex.re_ofReal_mul]
  have hbpos : 0 < b.re := by
    rw [hbre]
    have := hα.trans_le ha
    positivity
  have hE : ContinuousOn (fun t => cexp (N * φ t)) (Icc 0 r) :=
    (continuousOn_const.mul hφ).cexp
  have hF : Continuous (fun t : ℝ => cexp (-b * (t : ℂ) ^ 2)) := by fun_prop
  have iE : IntervalIntegrable (fun t => cexp (N * φ t)) volume 0 r :=
    hE.intervalIntegrable_of_Icc hr.le
  have igE : IntervalIntegrable (fun t => g t * cexp (N * φ t)) volume 0 r :=
    (hg.mul hE).intervalIntegrable_of_Icc hr.le
  have iF : IntervalIntegrable (fun t : ℝ => cexp (-b * (t : ℂ) ^ 2)) volume 0 r :=
    hF.intervalIntegrable 0 r
  -- the half-line Gaussian, split at `r`
  have hsplit : (π / b) ^ (1 / 2 : ℂ) / 2 =
      (∫ t in (0 : ℝ)..r, cexp (-b * (t : ℂ) ^ 2)) + ∫ t in Ioi r, cexp (-b * (t : ℂ) ^ 2) := by
    rw [← integral_gaussian_complex_Ioi hbpos, intervalIntegral.integral_of_le hr.le,
      ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (integrable_cexp_neg_mul_sq hbpos).integrableOn
        (integrable_cexp_neg_mul_sq hbpos).integrableOn,
      Ioc_union_Ioi_eq_Ioi hr.le]
  have h1 : (∫ t in (0 : ℝ)..r, (g t - g 0) * cexp (N * φ t)) =
      (∫ t in (0 : ℝ)..r, g t * cexp (N * φ t)) - g 0 * ∫ t in (0 : ℝ)..r, cexp (N * φ t) := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub igE (iE.const_mul (g 0)),
      intervalIntegral.integral_const_mul]
  have h2 : (∫ t in (0 : ℝ)..r, (cexp (N * φ t) - cexp (-b * (t : ℂ) ^ 2))) =
      (∫ t in (0 : ℝ)..r, cexp (N * φ t)) - ∫ t in (0 : ℝ)..r, cexp (-b * (t : ℂ) ^ 2) :=
    intervalIntegral.integral_sub iE iF
  have hdecomp : (∫ t in (0 : ℝ)..r, g t * cexp (N * φ t)) - g 0 * ((π / b) ^ (1 / 2 : ℂ) / 2) =
      (∫ t in (0 : ℝ)..r, (g t - g 0) * cexp (N * φ t)) +
      g 0 * (∫ t in (0 : ℝ)..r, (cexp (N * φ t) - cexp (-b * (t : ℂ) ^ 2))) -
      g 0 * ∫ t in Ioi r, cexp (-b * (t : ℂ) ^ 2) := by
    rw [hsplit, h1, h2]
    ring
  have hNc : 0 < N * c := mul_pos hN hc
  have hNc' : 0 < N * c' := mul_pos hN hc'
  -- piece 1: the amplitude varies, `‖g t - g 0‖ ≤ K t`
  have hP1 : ‖∫ t in (0 : ℝ)..r, (g t - g 0) * cexp (N * φ t)‖ ≤ K / (2 * c) / N := by
    calc ‖∫ t in (0 : ℝ)..r, (g t - g 0) * cexp (N * φ t)‖
        ≤ ∫ t in (0 : ℝ)..r, K * (t * Real.exp (-(N * c) * t ^ 2)) := by
          refine intervalIntegral.norm_integral_le_of_norm_le hr.le (ae_of_all _ fun t ht => ?_)
            (by apply Continuous.intervalIntegrable; fun_prop)
          have ht' : t ∈ Icc 0 r := Ioc_subset_Icc_self ht
          rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, ← mul_assoc]
          refine mul_le_mul (hgK t ht') (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
            (mul_nonneg hK ht'.1)
          have := mul_le_mul_of_nonneg_left (hφre t ht') hN.le
          linarith
      _ = K * ∫ t in (0 : ℝ)..r, t * Real.exp (-(N * c) * t ^ 2) :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ K * (1 / (2 * (N * c))) :=
          mul_le_mul_of_nonneg_left (integral_mul_exp_neg_sq_le hNc r) hK
      _ = K / (2 * c) / N := by field_simp
  -- piece 2: the phase differs from its quadratic part by `M t³`
  have hP2 : ‖∫ t in (0 : ℝ)..r, (cexp (N * φ t) - cexp (-b * (t : ℂ) ^ 2))‖ ≤
      M / (2 * c' ^ 2) / N := by
    calc ‖∫ t in (0 : ℝ)..r, (cexp (N * φ t) - cexp (-b * (t : ℂ) ^ 2))‖
        ≤ ∫ t in (0 : ℝ)..r, (N * M) * (t ^ 3 * Real.exp (-(N * c') * t ^ 2)) := by
          refine intervalIntegral.norm_integral_le_of_norm_le hr.le (ae_of_all _ fun t ht => ?_)
            (by apply Continuous.intervalIntegrable; fun_prop)
          have ht' : t ∈ Icc 0 r := Ioc_subset_Icc_self ht
          refine (norm_cexp_sub_le _ _).trans ?_
          have hid : (N : ℂ) * φ t - -b * (t : ℂ) ^ 2 = N * (φ t + a * (t : ℂ) ^ 2 / 2) := by
            rw [hbdef]; ring
          rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg hN.le]
          have hre1 : ((N : ℂ) * φ t).re ≤ -(N * c') * t ^ 2 := by
            rw [Complex.re_ofReal_mul]
            have h1 := mul_le_mul_of_nonneg_left (hφre t ht') hN.le
            have h2 : c' ≤ c := min_le_left _ _
            have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hN.le (sq_nonneg t))
            nlinarith
          have hre2 : (-b * (t : ℂ) ^ 2).re = -b.re * t ^ 2 := by
            rw [← Complex.ofReal_pow, mul_comm (-b) _, Complex.re_ofReal_mul, Complex.neg_re]
            ring
          have hre2' : (-b * (t : ℂ) ^ 2).re ≤ -(N * c') * t ^ 2 := by
            rw [hre2, hbre]
            have h2 : c' ≤ α / 2 := min_le_right _ _
            have h3 := mul_le_mul_of_nonneg_left (h2.trans (by linarith : α / 2 ≤ a.re / 2))
              (mul_nonneg hN.le (sq_nonneg t))
            nlinarith
          calc Real.exp (max ((N : ℂ) * φ t).re (-b * (t : ℂ) ^ 2).re) *
                (N * ‖φ t + a * (t : ℂ) ^ 2 / 2‖)
              ≤ Real.exp (-(N * c') * t ^ 2) * (N * (M * t ^ 3)) :=
                mul_le_mul (Real.exp_le_exp.mpr (max_le hre1 hre2'))
                  (mul_le_mul_of_nonneg_left (hφa t ht') hN.le)
                  (mul_nonneg hN.le (norm_nonneg _)) (Real.exp_pos _).le
            _ = (N * M) * (t ^ 3 * Real.exp (-(N * c') * t ^ 2)) := by ring
      _ = (N * M) * ∫ t in (0 : ℝ)..r, t ^ 3 * Real.exp (-(N * c') * t ^ 2) :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ (N * M) * (1 / (2 * (N * c') ^ 2)) :=
          mul_le_mul_of_nonneg_left (integral_pow_three_mul_exp_neg_sq_le hNc' r)
            (mul_nonneg hN.le hM)
      _ = M / (2 * c' ^ 2) / N := by field_simp
  -- piece 3: the Gaussian tail beyond `r`
  have hP3 : ‖∫ t in Ioi r, cexp (-b * (t : ℂ) ^ 2)‖ ≤ 1 / (α * r) / N := by
    calc ‖∫ t in Ioi r, cexp (-b * (t : ℂ) ^ 2)‖
        ≤ ∫ t in Ioi r, Real.exp (-b.re * t ^ 2) :=
          norm_integral_le_of_norm_le (integrable_exp_neg_mul_sq hbpos).integrableOn
            (ae_of_all _ fun t => (norm_cexp_neg_mul_sq b t).le)
      _ ≤ 1 / (2 * b.re * r) := integral_Ioi_exp_neg_sq_le hbpos hr
      _ ≤ 1 / (α * r) / N := by
          rw [div_div, hbre]
          apply one_div_le_one_div_of_le (mul_pos (mul_pos hα hr) hN)
          have := mul_le_mul_of_nonneg_left ha (mul_pos hN hr).le
          nlinarith
  rw [hdecomp]
  set I1 := ∫ t in (0 : ℝ)..r, (g t - g 0) * cexp (N * φ t)
  set I2 := ∫ t in (0 : ℝ)..r, (cexp (N * φ t) - cexp (-b * (t : ℂ) ^ 2))
  set T := ∫ t in Ioi r, cexp (-b * (t : ℂ) ^ 2)
  have e1 := norm_sub_le (I1 + g 0 * I2) (g 0 * T)
  have e2 := norm_add_le I1 (g 0 * I2)
  rw [norm_mul] at e1 e2
  have b2 := mul_le_mul hgG hP2 (norm_nonneg _) hG
  have b3 := mul_le_mul hgG hP3 (norm_nonneg _) hG
  have hC : (K / (2 * c) + G * M / (2 * c' ^ 2) + G / (α * r)) / N =
      K / (2 * c) / N + G * (M / (2 * c' ^ 2) / N) + G * (1 / (α * r) / N) := by ring
  rw [hC]
  linarith

end Lightlike.Oscillatory
