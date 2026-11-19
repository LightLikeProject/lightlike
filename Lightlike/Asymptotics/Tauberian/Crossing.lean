import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The crossing kernel

`crossingDensity a x = ∑_{k ≥ 0} a^{k+1} x^k / ((k+1)! k!)`, which is `√(a/x) I₁(2 √(a x))` (the
kernel `ρ₀` of Mukhametzhanov–Zhiboedov (2.6), `a = π² c / 3`, up to the shift by `c/12`), has Laplace
transform `e^{a/β} - 1` (`integral_crossing_exp`).
-/

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Tauberian

/-- The series `∑_{k ≥ 0} a^{k+1} x^k / ((k+1)! k!)`. -/
def crossingTerm (a : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  a ^ (k + 1) * x ^ k / (((k + 1).factorial : ℝ) * (k.factorial : ℝ))

/-- The crossing density. -/
def crossingDensity (a x : ℝ) : ℝ := ∑' k : ℕ, crossingTerm a k x

lemma integral_pow_exp {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    ∫ x in Ioi (0 : ℝ), x ^ k * Real.exp (-β * x) = (k.factorial : ℝ) / β ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := β) (by positivity) hβ
  have e1 : (fun t : ℝ => t ^ ((k : ℝ) + 1 - 1) * Real.exp (-(β * t))) =
      fun t => t ^ k * Real.exp (-β * t) := by
    ext t; rw [add_sub_cancel_right, Real.rpow_natCast, neg_mul]
  rw [e1] at h
  rw [h, Real.Gamma_nat_eq_factorial,
    show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, one_div, inv_pow]
  field_simp

lemma integrableOn_pow_exp {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-β * x)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := β)
    (by have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith) one_pos hβ
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp [Real.rpow_natCast]

lemma hasSum_crossing_integral {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    HasSum (fun k : ℕ => ∫ x in Ioi (0 : ℝ), crossingTerm a k x * Real.exp (-β * x))
      (Real.exp (a / β) - 1) := by
  have h1 : ∀ k : ℕ, ∫ x in Ioi (0 : ℝ), crossingTerm a k x * Real.exp (-β * x) =
      (a / β) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
    intro k
    have : ∀ x : ℝ, crossingTerm a k x * Real.exp (-β * x) =
        (a ^ (k + 1) / (((k + 1).factorial : ℝ) * (k.factorial : ℝ))) * (x ^ k * Real.exp (-β * x)) := by
      intro x; unfold crossingTerm; ring
    simp_rw [this]
    rw [integral_const_mul, integral_pow_exp hβ k, div_pow]
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    have hk1 : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  simp_rw [h1]
  have := (NormedSpace.expSeries_div_hasSum_exp (a / β))
  rw [← hasSum_nat_add_iff' 1] at this
  rw [← Real.exp_eq_exp_ℝ] at this
  simpa [Finset.sum_range_one] using this

lemma crossingTerm_nonneg {a : ℝ} (ha : 0 < a) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ crossingTerm a k x := by
  unfold crossingTerm; positivity

/-- **D1: the Laplace transform of the crossing density** (MZ (2.7)): for `a, β > 0`,
`∫₀^∞ crossingDensity a x · e^{-β x} dx = e^{a/β} - 1`. -/
theorem integral_crossing_exp {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∫ x in Ioi (0 : ℝ), crossingDensity a x * Real.exp (-β * x) = Real.exp (a / β) - 1 := by
  have hint : ∀ k : ℕ, IntegrableOn (fun x : ℝ => crossingTerm a k x * Real.exp (-β * x)) (Ioi 0) := by
    intro k
    have : ∀ x : ℝ, crossingTerm a k x * Real.exp (-β * x) =
        (a ^ (k + 1) / (((k + 1).factorial : ℝ) * (k.factorial : ℝ))) * (x ^ k * Real.exp (-β * x)) := by
      intro x; unfold crossingTerm; ring
    simp_rw [this]
    exact (integrableOn_pow_exp hβ k).const_mul _
  have hnorm : ∀ k : ℕ, ∫ x in Ioi (0 : ℝ), ‖crossingTerm a k x * Real.exp (-β * x)‖ =
      ∫ x in Ioi (0 : ℝ), crossingTerm a k x * Real.exp (-β * x) := by
    intro k
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    exact Real.norm_of_nonneg (mul_nonneg (crossingTerm_nonneg ha k (le_of_lt hx)) (Real.exp_pos _).le)
  have hsum := hasSum_crossing_integral ha hβ
  have := integral_tsum_of_summable_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun k x => crossingTerm a k x * Real.exp (-β * x)) hint
    (by simp_rw [hnorm]; exact hsum.summable)
  rw [← hsum.tsum_eq, this]
  refine integral_congr_ae ?_
  filter_upwards with x
  unfold crossingDensity
  rw [tsum_mul_right]

end Lightlike.Tauberian
