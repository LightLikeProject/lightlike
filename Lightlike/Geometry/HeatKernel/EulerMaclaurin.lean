import Mathlib

/-!
# Euler–Maclaurin on a unit interval (Bernoulli integration by parts)

The per-interval identity behind the Euler–Maclaurin formula, used for the heat trace of the round
`S²`: for smooth `g`, the Bernoulli integrals `I k = ∫₀¹ B_k(x) g^{(k)}(x) dx` satisfy
`I k + I (k+1) / (k+1) = [B_{k+1}(x) g^{(k)}(x)]₀¹ / (k+1)`.

## Main results

* `Lightlike.HeatKernel.bernoulliInt_succ`: the integration-by-parts recursion for `I k`.
* `Lightlike.HeatKernel.integral_unit_interval_six`: `∫₀¹ g` as trapezoid value, boundary terms in
  `g'`, `g'''`, `g⁽⁵⁾` (coefficients `1/12`, `1/720`, `B₆/720`) and the Bernoulli remainder `I₆/720`.
-/

open intervalIntegral

noncomputable section

namespace Lightlike.HeatKernel

/-- Bernoulli integral `I_k(g) = ∫₀¹ B_k(x) g^{(k)}(x) dx`. -/
def bernoulliInt (g : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, bernoulliFun k x * iteratedDeriv k g x

/-- Integration by parts for Bernoulli integrals:
`I_k + I_{k+1}/(k+1) = (B_{k+1}(1) g^{(k)}(1) - B_{k+1}(0) g^{(k)}(0)) / (k+1)`. -/
theorem bernoulliInt_succ (g : ℝ → ℝ) (hg : ∀ k, Differentiable ℝ (iteratedDeriv k g)) (k : ℕ) :
    bernoulliInt g k + bernoulliInt g (k + 1) / (k + 1) =
      (bernoulliFun (k + 1) 1 * iteratedDeriv k g 1 -
        bernoulliFun (k + 1) 0 * iteratedDeriv k g 0) / (k + 1) := by
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hv : ∀ x, HasDerivAt (iteratedDeriv k g) (iteratedDeriv (k + 1) g x) x := by
    intro x
    have := (hg k x).hasDerivAt
    rwa [← iteratedDeriv_succ] at this
  have hu : ∀ x, HasDerivAt (fun x => bernoulliFun (k + 1) x / (k + 1))
      (bernoulliFun k x) x := fun x => antideriv_bernoulliFun k x
  have hcont : ∀ j, Continuous (iteratedDeriv j g) := fun j => (hg j).continuous
  have hI := integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := fun x => bernoulliFun (k + 1) x / (k + 1)) (v := iteratedDeriv k g)
    (u' := fun x => bernoulliFun k x) (v' := fun x => iteratedDeriv (k + 1) g x)
    (fun x _ => hu x) (fun x _ => hv x)
    ((continuous_bernoulliFun k).intervalIntegrable _ _)
    ((hcont (k + 1)).intervalIntegrable _ _)
  unfold bernoulliInt
  have e1 : ∫ x in (0 : ℝ)..1, bernoulliFun (k + 1) x / (k + 1) * iteratedDeriv (k + 1) g x =
      (∫ x in (0 : ℝ)..1, bernoulliFun (k + 1) x * iteratedDeriv (k + 1) g x) / (k + 1) := by
    rw [← integral_div]
    congr 1; ext x; ring
  rw [e1] at hI
  have e2 : ∫ x in (0 : ℝ)..1, bernoulliFun k x * iteratedDeriv k g x =
      ∫ x in (0 : ℝ)..1, bernoulliFun k x * iteratedDeriv k g x := rfl
  have e3 : ((k : ℝ) + 1) ≠ 0 := hk
  field_simp
  field_simp at hI
  linarith

private theorem bernoulliFun_odd_zero (j : ℕ) (hj : 1 < 2 * j + 1) :
    bernoulliFun (2 * j + 1) 0 = 0 := by
  rw [bernoulliFun_eval_zero, bernoulli_eq_zero_of_odd (by simp) hj]
  simp

private theorem bernoulliFun_odd_one (j : ℕ) (hj : 1 < 2 * j + 1) :
    bernoulliFun (2 * j + 1) 1 = 0 := by
  rw [bernoulliFun_endpoints_eq_of_ne_one (by lia), bernoulliFun_odd_zero j hj]

private theorem bernoulliFun_four_zero : bernoulliFun 4 0 = -1 / 30 := by
  rw [bernoulliFun_eval_zero, bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]
  norm_num

/-- **Euler–Maclaurin on a unit interval, to order six.** For smooth `g`,
`∫₀¹ g = (g 0 + g 1)/2 - (g'(1) - g'(0))/12 + (g'''(1) - g'''(0))/720
  - B₆ (g⁽⁵⁾(1) - g⁽⁵⁾(0))/720 + I₆/720`, where `I₆ = ∫₀¹ B₆(x) g⁽⁶⁾(x) dx` is
`bernoulliInt g 6` and `B₆ = bernoulliFun 6 0` (the Bernoulli number). -/
theorem integral_unit_interval_six (g : ℝ → ℝ) (hg : ∀ k, Differentiable ℝ (iteratedDeriv k g)) :
    ∫ x in (0 : ℝ)..1, g x =
      (g 0 + g 1) / 2 - (iteratedDeriv 1 g 1 - iteratedDeriv 1 g 0) / 12
        + (iteratedDeriv 3 g 1 - iteratedDeriv 3 g 0) / 720
        - bernoulliFun 6 0 * (iteratedDeriv 5 g 1 - iteratedDeriv 5 g 0) / 720
        + bernoulliInt g 6 / 720 := by
  have h0 := bernoulliInt_succ g hg 0
  have h1 := bernoulliInt_succ g hg 1
  have h2 := bernoulliInt_succ g hg 2
  have h3 := bernoulliInt_succ g hg 3
  have h4 := bernoulliInt_succ g hg 4
  have h5 := bernoulliInt_succ g hg 5
  have e0 : bernoulliInt g 0 = ∫ x in (0 : ℝ)..1, g x := by
    simp [bernoulliInt, bernoulliFun_zero]
  have b3 := bernoulliFun_odd_zero 1 (by norm_num)
  have b3' := bernoulliFun_odd_one 1 (by norm_num)
  have b5 := bernoulliFun_odd_zero 2 (by norm_num)
  have b5' := bernoulliFun_odd_one 2 (by norm_num)
  have b2 : bernoulliFun 2 0 = 1 / 6 := by rw [bernoulliFun_two]; norm_num
  have b2' : bernoulliFun 2 1 = 1 / 6 := by rw [bernoulliFun_two]; norm_num
  have b6 : bernoulliFun 6 1 = bernoulliFun 6 0 :=
    bernoulliFun_endpoints_eq_of_ne_one (by norm_num)
  have b4 : bernoulliFun 4 1 = -1 / 30 := by
    rw [bernoulliFun_endpoints_eq_of_ne_one (by norm_num), bernoulliFun_four_zero]
  have b1 : bernoulliFun 1 0 = -1 / 2 := by rw [bernoulliFun_one]; norm_num
  have b1' : bernoulliFun 1 1 = 1 / 2 := by rw [bernoulliFun_one]; norm_num
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_add, iteratedDeriv_zero,
    Nat.reduceAdd, b1, b1', b2, b2', b3, b3', b4, bernoulliFun_four_zero, b5, b5', b6] at h0 h1 h2 h3 h4 h5
  rw [← e0]
  linarith

end Lightlike.HeatKernel
