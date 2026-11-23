import Mathlib
import Lightlike.Geometry.HeatKernel.GaussianDeriv

/-!
# The summand of the `S³` heat trace, by rescaling the even Gaussian

The Laplace–Beltrami spectrum of the unit round `S³` is `l(l+2)` with multiplicity `(l+1)²`
(`l = 0, 1, …`). With `m = l + 1` the heat trace is `e^t ∑_{m ≥ 1} m² e^{-t m²}`. The summand is the
value at `m` of `s3G t x = x² e^{-t x²}`, and for `t > 0`, `c = √t`, `s3G t x = t⁻¹ · gaussEven (c x)`
with `gaussEven u = u² e^{-u²}`. All derivatives of `s3G t` are therefore rescalings of those of
`gaussEven`, which bounds the Euler–Maclaurin remainder by `O(t^{3/2})`.

## Main results

* `iteratedDeriv_gaussEven`: `gaussEven⁽ᵏ⁾ = e_k(u) e^{-u²}` with a polynomial `e_k`.
* `iteratedDeriv_gaussEven_odd_zero`: odd derivatives of `gaussEven` vanish at `0`.
* `iteratedDeriv_s3G`: `s3G⁽ᵏ⁾ = t⁻¹ c^k gaussEven⁽ᵏ⁾(c x)`.
* `integral_s3G`: `∫₀^∞ x² e^{-t x²} dx = (√π/4) t^{-3/2}`.
* `integral_abs_s3G_six_le`: `∫₀^∞ |s3G⁽⁶⁾| ≤ t² (√t)⁻¹ ∫ |gaussEven⁽⁶⁾|`.
-/

open Polynomial Filter

noncomputable section

namespace Lightlike.HeatKernel

/-- The even Gaussian `u² e^{-u²}`. -/
def gaussEven (u : ℝ) : ℝ := u ^ 2 * Real.exp (-(u ^ 2))

/-- The polynomials with `gaussEven⁽ᵏ⁾ = ePoly k · e^{-u²}`. -/
def ePoly : ℕ → ℝ[X]
  | 0 => X ^ 2
  | k + 1 => derivative (ePoly k) - C 2 * X * ePoly k

theorem iteratedDeriv_gaussEven (k : ℕ) :
    iteratedDeriv k gaussEven = fun u => (ePoly k).eval u * Real.exp (-(u ^ 2)) := by
  induction k with
  | zero => ext u; simp [ePoly, gaussEven]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    ext u
    have h : HasDerivAt (fun u => (ePoly k).eval u * Real.exp (-(u ^ 2)))
        (((ePoly k).derivative.eval u) * Real.exp (-(u ^ 2)) +
          (ePoly k).eval u * (Real.exp (-(u ^ 2)) * (-(2 * u)))) u :=
      ((ePoly k).hasDerivAt u).mul (hasDerivAt_gauss u)
    rw [h.deriv]
    simp only [ePoly, eval_sub, eval_mul, eval_C, eval_X]
    ring

theorem gaussEven_smooth (k : ℕ) : Differentiable ℝ (iteratedDeriv k gaussEven) := by
  rw [iteratedDeriv_gaussEven]
  intro u
  exact (((ePoly k).hasDerivAt u).mul (hasDerivAt_gauss u)).differentiableAt

theorem integrable_iteratedDeriv_gaussEven (k : ℕ) :
    MeasureTheory.Integrable (iteratedDeriv k gaussEven) := by
  rw [iteratedDeriv_gaussEven]; exact integrable_poly_mul_gauss _

theorem tendsto_iteratedDeriv_gaussEven (k : ℕ) :
    Tendsto (iteratedDeriv k gaussEven) atTop (nhds 0) := by
  rw [iteratedDeriv_gaussEven]; exact tendsto_poly_mul_gauss _

theorem contDiff_gaussEven (n : ℕ∞) : ContDiff ℝ n gaussEven := by
  unfold gaussEven
  exact (contDiff_id.pow 2).mul (Real.contDiff_exp.comp (contDiff_id.pow 2).neg)

/-- `gaussEven` is even, so its odd derivatives vanish at `0`. -/
theorem iteratedDeriv_gaussEven_odd_zero {k : ℕ} (hk : Odd k) :
    iteratedDeriv k gaussEven 0 = 0 := by
  have h := iteratedDeriv_comp_neg k gaussEven 0
  have he : (fun x : ℝ => gaussEven (-x)) = gaussEven := by
    ext x; simp [gaussEven]
  rw [he, neg_zero, hk.neg_one_pow] at h
  simp only [smul_eq_mul] at h
  linarith

/-- The summand of the `S³` heat trace: `x² e^{-t x²}`. -/
def s3G (t x : ℝ) : ℝ := x ^ 2 * Real.exp (-(t * x ^ 2))

theorem s3G_eq {t : ℝ} (ht : 0 < t) :
    s3G t = fun x => t⁻¹ * gaussEven (Real.sqrt t * x) := by
  ext x
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  unfold s3G gaussEven
  rw [mul_pow, hsq]
  field_simp

theorem iteratedDeriv_s3G {t : ℝ} (ht : 0 < t) (k : ℕ) :
    iteratedDeriv k (s3G t) = fun x => t⁻¹ *
      (Real.sqrt t ^ k * iteratedDeriv k gaussEven (Real.sqrt t * x)) := by
  rw [s3G_eq ht]
  ext x
  rw [iteratedDeriv_const_mul_field]
  congr 1
  exact congrFun (iteratedDeriv_comp_const_mul (contDiff_gaussEven k) (Real.sqrt t)) x

theorem s3G_smooth {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Differentiable ℝ (iteratedDeriv k (s3G t)) := by
  rw [iteratedDeriv_s3G ht]
  have h := (gaussEven_smooth k).comp ((differentiable_const (Real.sqrt t)).mul differentiable_id)
  exact (differentiable_const _).mul ((differentiable_const _).mul h)

theorem tendsto_iteratedDeriv_s3G {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Tendsto (iteratedDeriv k (s3G t)) atTop (nhds 0) := by
  rw [iteratedDeriv_s3G ht]
  have hc : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h1 : Tendsto (fun x : ℝ => Real.sqrt t * x) atTop atTop :=
    Tendsto.const_mul_atTop hc tendsto_id
  have h2 := (tendsto_iteratedDeriv_gaussEven k).comp h1
  have h3 := (h2.const_mul (Real.sqrt t ^ k)).const_mul t⁻¹
  simpa using h3

theorem integrable_iteratedDeriv_s3G {t : ℝ} (ht : 0 < t) (k : ℕ) :
    MeasureTheory.Integrable (iteratedDeriv k (s3G t)) := by
  rw [iteratedDeriv_s3G ht]
  have hc : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have h1 := (integrable_iteratedDeriv_gaussEven k).comp_mul_left' hc
  have h2 : MeasureTheory.Integrable fun x : ℝ =>
      iteratedDeriv k gaussEven (Real.sqrt t * x) := by
    simpa [Function.comp_def] using h1
  exact (h2.const_mul (Real.sqrt t ^ k)).const_mul _

theorem s3G_zero (t : ℝ) : iteratedDeriv 0 (s3G t) 0 = 0 := by
  simp [s3G]

theorem iteratedDeriv_s3G_odd_zero {t : ℝ} (ht : 0 < t) {k : ℕ} (hk : Odd k) :
    iteratedDeriv k (s3G t) 0 = 0 := by
  rw [iteratedDeriv_s3G ht]
  simp [iteratedDeriv_gaussEven_odd_zero hk]

/-- The leading term: `∫_0^∞ x² e^{-t x²} dx = (√π/4) t^{-3/2}`. -/
theorem integral_s3G {t : ℝ} (ht : 0 < t) :
    ∫ x in Set.Ioi (0 : ℝ), s3G t x = Real.sqrt Real.pi / 4 * t ^ (-(3 / 2) : ℝ) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := t) (by norm_num)
    (by norm_num) ht
  have e1 : ∀ x : ℝ, x ^ (2 : ℝ) * Real.exp (-t * x ^ (2 : ℝ)) = s3G t x := by
    intro x
    simp only [s3G, Real.rpow_two]
    ring_nf
  simp only [e1] at h
  rw [h]
  have hg : Real.Gamma ((2 + 1) / 2) = Real.sqrt Real.pi / 2 := by
    have : ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 := by norm_num
    rw [this, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  rw [hg]
  have : -((2 : ℝ) + 1) / 2 = -(3 / 2) := by norm_num
  rw [this]
  ring

/-- The Euler–Maclaurin remainder integral of `s3G t`:
`∫_{(0,∞)} |s3G⁽⁶⁾| ≤ t² (√t)⁻¹ ∫_ℝ |gaussEven⁽⁶⁾|`. -/
theorem integral_abs_s3G_six_le {t : ℝ} (ht : 0 < t) :
    ∫ x in Set.Ioi (0 : ℝ), |iteratedDeriv 6 (s3G t) x| ≤
      t ^ 2 * (Real.sqrt t)⁻¹ * ∫ u, |iteratedDeriv 6 gaussEven u| := by
  have hc : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  set A : ℝ := t⁻¹ * Real.sqrt t ^ 6 with hA
  have hA0 : 0 < A := by positivity
  have hfun : (fun x => |iteratedDeriv 6 (s3G t) x|) = fun x =>
      A * |iteratedDeriv 6 gaussEven (Real.sqrt t * x)| := by
    ext x
    rw [iteratedDeriv_s3G ht]
    rw [abs_mul, abs_of_pos (by positivity : 0 < t⁻¹), abs_mul,
      abs_of_pos (by positivity : 0 < Real.sqrt t ^ 6)]
    rw [hA]; ring
  have hint : MeasureTheory.Integrable fun x : ℝ =>
      |iteratedDeriv 6 (s3G t) x| := (integrable_iteratedDeriv_s3G ht 6).abs
  have h1 : ∫ x in Set.Ioi (0 : ℝ), |iteratedDeriv 6 (s3G t) x| ≤
      ∫ x, |iteratedDeriv 6 (s3G t) x| :=
    MeasureTheory.setIntegral_le_integral hint (Filter.Eventually.of_forall fun x => abs_nonneg _)
  have h2 : ∫ x, |iteratedDeriv 6 (s3G t) x| =
      A * (Real.sqrt t)⁻¹ * ∫ u, |iteratedDeriv 6 gaussEven u| := by
    rw [hfun, MeasureTheory.integral_const_mul]
    have e2 := MeasureTheory.Measure.integral_comp_mul_left
      (fun y : ℝ => |iteratedDeriv 6 gaussEven y|) (Real.sqrt t)
    rw [e2, abs_of_pos (inv_pos.mpr hc), smul_eq_mul]
    ring
  have h3 : A * (Real.sqrt t)⁻¹ = t ^ 2 * (Real.sqrt t)⁻¹ := by
    have : Real.sqrt t ^ 6 = t ^ 3 := by rw [show 6 = 2 * 3 by rfl, pow_mul, hsq]
    rw [hA, this]
    field_simp
  rw [h2, h3] at h1
  exact h1

end Lightlike.HeatKernel
