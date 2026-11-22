import Lightlike.Geometry.HeatKernel.GaussianDeriv

/-!
# The summand of the `S²` heat trace, by rescaling the odd Gaussian

The heat trace of the unit round `S²` is `∑_{l ≥ 0} (2l+1) e^{-t l(l+1)}`. Its summand is the
value at `l` of `sphereG t x = (2x+1) e^{-t x(x+1)}`. For `t > 0`, with `c = √t`,
`sphereG t x = e^{t/4} (2/c) · gaussOdd (c (x + 1/2))`, so all derivatives of `sphereG t` are
rescalings of those of `gaussOdd`: this is what bounds the Euler–Maclaurin remainder by `O(t²)`.

## Main results

* `Lightlike.HeatKernel.sphereG_eq`: the rescaling identity.
* `Lightlike.HeatKernel.iteratedDeriv_sphereG`: `sphereG⁽ᵏ⁾ = e^{t/4}(2/c) c^k gaussOdd⁽ᵏ⁾(c(x+1/2))`.
-/

open Filter

noncomputable section

namespace Lightlike.HeatKernel

/-- The function whose values at the integers are the multiplicities-weighted Boltzmann factors
of `S²`: `(2x+1) e^{-t x(x+1)}`. -/
def sphereG (t x : ℝ) : ℝ := (2 * x + 1) * Real.exp (-(t * (x * (x + 1))))

theorem sphereG_eq {t : ℝ} (ht : 0 < t) :
    sphereG t = fun x => (Real.exp (t / 4) * (2 / Real.sqrt t)) *
      gaussOdd (Real.sqrt t * (x + 1 / 2)) := by
  ext x
  have hc : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  unfold sphereG gaussOdd
  have : Real.exp (-(t * (x * (x + 1)))) = Real.exp (t / 4) *
      Real.exp (-((Real.sqrt t * (x + 1 / 2)) ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    have : (Real.sqrt t * (x + 1 / 2)) ^ 2 = t * (x + 1 / 2) ^ 2 := by
      rw [mul_pow, hsq]
    rw [this]; ring
  rw [this]
  field_simp

theorem contDiff_gaussOdd (n : ℕ∞) : ContDiff ℝ n gaussOdd := by
  unfold gaussOdd
  exact contDiff_id.mul (Real.contDiff_exp.comp (contDiff_id.pow 2).neg)

theorem iteratedDeriv_sphereG {t : ℝ} (ht : 0 < t) (k : ℕ) :
    iteratedDeriv k (sphereG t) = fun x => (Real.exp (t / 4) * (2 / Real.sqrt t)) *
      (Real.sqrt t ^ k * iteratedDeriv k gaussOdd (Real.sqrt t * (x + 1 / 2))) := by
  rw [sphereG_eq ht]
  ext x
  rw [iteratedDeriv_const_mul_field]
  congr 1
  have h2 := congrFun (iteratedDeriv_comp_add_const (n := k)
    (f := fun y => gaussOdd (Real.sqrt t * y)) (s := (1 / 2 : ℝ))) x
  have h3 := congrFun (iteratedDeriv_comp_const_mul (n := k) (contDiff_gaussOdd k)
    (Real.sqrt t)) (x + 1 / 2)
  exact h2.trans h3

theorem sphereG_smooth {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Differentiable ℝ (iteratedDeriv k (sphereG t)) := by
  rw [iteratedDeriv_sphereG ht]
  have h := (gaussOdd_smooth k).comp
    ((differentiable_const (Real.sqrt t)).mul (differentiable_id.add_const (1 / 2 : ℝ)))
  exact (differentiable_const _).mul ((differentiable_const _).mul h)

theorem tendsto_iteratedDeriv_sphereG {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Tendsto (iteratedDeriv k (sphereG t)) atTop (nhds 0) := by
  rw [iteratedDeriv_sphereG ht]
  have hc : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h1 : Tendsto (fun x : ℝ => Real.sqrt t * (x + 1 / 2)) atTop atTop :=
    Tendsto.const_mul_atTop hc (tendsto_atTop_add_const_right _ _ tendsto_id)
  have h2 := (tendsto_iteratedDeriv_gaussOdd k).comp h1
  have h3 := (h2.const_mul (Real.sqrt t ^ k)).const_mul (Real.exp (t / 4) * (2 / Real.sqrt t))
  simpa using h3

theorem integrable_iteratedDeriv_sphereG {t : ℝ} (ht : 0 < t) (k : ℕ) :
    MeasureTheory.Integrable (iteratedDeriv k (sphereG t)) := by
  rw [iteratedDeriv_sphereG ht]
  have hc : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have h1 := ((integrable_iteratedDeriv_gaussOdd k).comp_mul_left' hc).comp_add_right (1 / 2 : ℝ)
  have h2 : MeasureTheory.Integrable fun x : ℝ =>
      iteratedDeriv k gaussOdd (Real.sqrt t * (x + 1 / 2)) := by
    simpa [Function.comp_def] using h1
  exact (h2.const_mul (Real.sqrt t ^ k)).const_mul _

/-- The Euler–Maclaurin remainder integral of `sphereG t` is `O(t²)`:
`∫_{(0,∞)} |G⁽⁶⁾| ≤ 2 e^{t/4} t² ∫_ℝ |gaussOdd⁽⁶⁾|`. -/
theorem integral_abs_sphereG_six_le {t : ℝ} (ht : 0 < t) :
    ∫ x in Set.Ioi (0 : ℝ), |iteratedDeriv 6 (sphereG t) x| ≤
      2 * Real.exp (t / 4) * t ^ 2 * ∫ u, |iteratedDeriv 6 gaussOdd u| := by
  have hc : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  set A : ℝ := Real.exp (t / 4) * (2 / Real.sqrt t) * Real.sqrt t ^ 6 with hA
  have hA0 : 0 < A := by positivity
  have hfun : (fun x => |iteratedDeriv 6 (sphereG t) x|) = fun x =>
      A * |iteratedDeriv 6 gaussOdd (Real.sqrt t * (x + 1 / 2))| := by
    ext x
    rw [iteratedDeriv_sphereG ht]
    rw [abs_mul, abs_of_pos (by positivity : 0 < Real.exp (t / 4) * (2 / Real.sqrt t)), abs_mul,
      abs_of_pos (by positivity : 0 < Real.sqrt t ^ 6)]
    rw [hA]; ring
  have hint : MeasureTheory.Integrable fun x : ℝ =>
      |iteratedDeriv 6 (sphereG t) x| := (integrable_iteratedDeriv_sphereG ht 6).abs
  have h1 : ∫ x in Set.Ioi (0 : ℝ), |iteratedDeriv 6 (sphereG t) x| ≤
      ∫ x, |iteratedDeriv 6 (sphereG t) x| :=
    MeasureTheory.setIntegral_le_integral hint (Filter.Eventually.of_forall fun x => abs_nonneg _)
  have h2 : ∫ x, |iteratedDeriv 6 (sphereG t) x| =
      A * (Real.sqrt t)⁻¹ * ∫ u, |iteratedDeriv 6 gaussOdd u| := by
    rw [hfun, MeasureTheory.integral_const_mul]
    have e1 := MeasureTheory.integral_add_right_eq_self (μ := MeasureTheory.volume)
      (fun y : ℝ => |iteratedDeriv 6 gaussOdd (Real.sqrt t * y)|) (1 / 2 : ℝ)
    have e2 := MeasureTheory.Measure.integral_comp_mul_left
      (fun y : ℝ => |iteratedDeriv 6 gaussOdd y|) (Real.sqrt t)
    rw [e1, e2, abs_of_pos (inv_pos.mpr hc), smul_eq_mul]
    ring
  have h3 : A * (Real.sqrt t)⁻¹ = 2 * Real.exp (t / 4) * t ^ 2 := by
    have : Real.sqrt t ^ 6 = t ^ 3 := by rw [show 6 = 2 * 3 by rfl, pow_mul, hsq]
    rw [hA, this]
    field_simp
    nlinarith [hsq]
  rw [h2, h3] at h1
  exact h1

end Lightlike.HeatKernel
