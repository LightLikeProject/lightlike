import Lightlike.Asymptotics.Tauberian.Scaling
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Polynomials in `exp (-x / t)` against a regularly varying measure

For a polynomial `P = ∑ cₙ Xⁿ` the integral `∫ exp (-x/t) P (exp (-x/t)) dρ = ∑ cₙ L((n + 1)/t)`, so by
`tendsto_scaled_laplace`
`(t^α ℓ t)⁻¹ ∫ exp (-x/t) P (exp (-x/t)) dρ → ∑ cₙ (n + 1)^{-α}` (`tendsto_poly_integral`).
-/

open MeasureTheory Set Real Filter Topology Polynomial

noncomputable section

namespace Lightlike.Tauberian

variable {ρ : Measure ℝ}

/-- The integral `∫ exp (-x/t) P (exp (-x/t)) dρ` against a polynomial. -/
lemma integral_poly_eq_sum (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ)
    (P : ℝ[X]) {t : ℝ} (ht : 0 < t) :
    ∫ x, Real.exp (-(1 / t) * x) * P.eval (Real.exp (-(1 / t) * x)) ∂ρ =
      ∑ n ∈ Finset.range (P.natDegree + 1), P.coeff n * laplace ρ (((n : ℝ) + 1) / t) := by
  have h1 : ∀ x : ℝ, Real.exp (-(1 / t) * x) * P.eval (Real.exp (-(1 / t) * x)) =
      ∑ n ∈ Finset.range (P.natDegree + 1), P.coeff n * Real.exp (-(((n : ℝ) + 1) / t) * x) := by
    intro x
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show -(((n : ℝ) + 1) / t) * x = -(1 / t) * x + (n : ℝ) * (-(1 / t) * x) by ring, Real.exp_add,
      ← Real.exp_nat_mul]
    ring
  simp_rw [h1]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul]
    rfl
  · intro n _
    exact (hint _ (by positivity)).const_mul _

/-- **The polynomial functionals converge.** -/
theorem tendsto_poly_integral (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ)
    {α : ℝ} {ℓ : ℝ → ℝ} (hℓ : SlowlyVarying ℓ)
    (hL : Tendsto (fun β : ℝ => laplace ρ β / (β ^ (-α) * ℓ (1 / β))) (𝓝[>] 0) (𝓝 1)) (P : ℝ[X]) :
    Tendsto (fun t : ℝ => (∫ x, Real.exp (-(1 / t) * x) * P.eval (Real.exp (-(1 / t) * x)) ∂ρ) /
        (t ^ α * ℓ t)) atTop
      (𝓝 (∑ n ∈ Finset.range (P.natDegree + 1), P.coeff n * (((n : ℝ) + 1) ^ (-α)))) := by
  have key : ∀ n : ℕ, Tendsto (fun t : ℝ => P.coeff n * (laplace ρ (((n : ℝ) + 1) / t) /
      (t ^ α * ℓ t))) atTop (𝓝 (P.coeff n * (((n : ℝ) + 1) ^ (-α)))) := fun n =>
    (tendsto_scaled_laplace hℓ hL (by positivity : (0 : ℝ) < (n : ℝ) + 1)).const_mul _
  have hsum := tendsto_finset_sum (Finset.range (P.natDegree + 1)) fun n _ => key n
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [integral_poly_eq_sum hint P ht, Finset.sum_div]
  exact Finset.sum_congr rfl fun n _ => by ring

end Lightlike.Tauberian
