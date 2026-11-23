import Mathlib

/-!
# Derivatives of `u ↦ u e^{-u²}`

The odd Gaussian `gaussOdd u = u e^{-u²}` is the model function used to estimate the Euler–Maclaurin
remainder for the heat trace of the round `S²` (by the rescaling `u = √t (x + 1/2)`).
Its `k`-th derivative is `p_k(u) e^{-u²}` with the polynomial `p_k` defined by
`p₀ = X`, `p_{k+1} = p_k' - 2 X p_k`.

## Main results

* `Lightlike.HeatKernel.iteratedDeriv_gaussOdd`: `gaussOdd⁽ᵏ⁾ = p_k e^{-u²}`.
* `Lightlike.HeatKernel.integrable_iteratedDeriv_gaussOdd`, `tendsto_iteratedDeriv_gaussOdd`:
  every derivative is integrable on `ℝ` and tends to `0` at `+∞`.
-/

open Polynomial Filter

noncomputable section

namespace Lightlike.HeatKernel

/-- The odd Gaussian `u e^{-u²}`. -/
def gaussOdd (u : ℝ) : ℝ := u * Real.exp (-(u ^ 2))

/-- The polynomials with `gaussOdd⁽ᵏ⁾ = hPoly k · e^{-u²}`. -/
def hPoly : ℕ → ℝ[X]
  | 0 => X
  | k + 1 => derivative (hPoly k) - C 2 * X * hPoly k

theorem hasDerivAt_gauss (u : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2))) (Real.exp (-(u ^ 2)) * (-(2 * u))) u := by
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2)) (-(2 * u)) u := by
    convert (hasDerivAt_pow 2 u).neg using 1
    simp
  exact h1.exp

theorem iteratedDeriv_gaussOdd (k : ℕ) :
    iteratedDeriv k gaussOdd = fun u => (hPoly k).eval u * Real.exp (-(u ^ 2)) := by
  induction k with
  | zero => ext u; simp [hPoly, gaussOdd]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    ext u
    have h : HasDerivAt (fun u => (hPoly k).eval u * Real.exp (-(u ^ 2)))
        (((hPoly k).derivative.eval u) * Real.exp (-(u ^ 2)) +
          (hPoly k).eval u * (Real.exp (-(u ^ 2)) * (-(2 * u)))) u :=
      ((hPoly k).hasDerivAt u).mul (hasDerivAt_gauss u)
    rw [h.deriv]
    simp only [hPoly, eval_sub, eval_mul, eval_C, eval_X]
    ring

theorem gaussOdd_smooth (k : ℕ) : Differentiable ℝ (iteratedDeriv k gaussOdd) := by
  rw [iteratedDeriv_gaussOdd]
  intro u
  exact (((hPoly k).hasDerivAt u).mul (hasDerivAt_gauss u)).differentiableAt

/-- A monomial times a Gaussian is integrable. -/
theorem integrable_pow_mul_gauss (n : ℕ) :
    MeasureTheory.Integrable (fun u : ℝ => u ^ n * Real.exp (-(u ^ 2))) := by
  have := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := (n : ℝ))
    (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  simpa [Real.rpow_natCast] using this

/-- A polynomial times a Gaussian is integrable. -/
theorem integrable_poly_mul_gauss (p : ℝ[X]) :
    MeasureTheory.Integrable (fun u : ℝ => p.eval u * Real.exp (-(u ^ 2))) := by
  have : (fun u : ℝ => p.eval u * Real.exp (-(u ^ 2))) =
      fun u => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (u ^ i * Real.exp (-(u ^ 2))) := by
    ext u
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  exact MeasureTheory.integrable_finsetSum _ fun i _ => (integrable_pow_mul_gauss i).const_mul _

theorem tendsto_pow_mul_gauss (n : ℕ) :
    Tendsto (fun u : ℝ => u ^ n * Real.exp (-(u ^ 2))) atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hu0 : 0 ≤ u ^ n := by positivity
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hu0
    nlinarith

theorem tendsto_poly_mul_gauss (p : ℝ[X]) :
    Tendsto (fun u : ℝ => p.eval u * Real.exp (-(u ^ 2))) atTop (nhds 0) := by
  have : (fun u : ℝ => p.eval u * Real.exp (-(u ^ 2))) =
      fun u => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (u ^ i * Real.exp (-(u ^ 2))) := by
    ext u
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  have h : ∀ i ∈ Finset.range (p.natDegree + 1),
      Tendsto (fun u : ℝ => p.coeff i * (u ^ i * Real.exp (-(u ^ 2)))) atTop (nhds 0) := by
    intro i _
    simpa using (tendsto_pow_mul_gauss i).const_mul (p.coeff i)
  simpa using tendsto_finsetSum _ h

theorem integrable_iteratedDeriv_gaussOdd (k : ℕ) :
    MeasureTheory.Integrable (iteratedDeriv k gaussOdd) := by
  rw [iteratedDeriv_gaussOdd]; exact integrable_poly_mul_gauss _

theorem tendsto_iteratedDeriv_gaussOdd (k : ℕ) :
    Tendsto (iteratedDeriv k gaussOdd) atTop (nhds 0) := by
  rw [iteratedDeriv_gaussOdd]; exact tendsto_poly_mul_gauss _

end Lightlike.HeatKernel
