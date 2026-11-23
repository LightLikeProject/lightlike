import Mathlib
import Lightlike.Geometry.HeatKernel.EulerMaclaurinSum
import Lightlike.Geometry.HeatKernel.SphereSummand
import Lightlike.Geometry.HeatKernel.Expansion

/-!
# The heat trace of the unit round `S²`

The Laplace–Beltrami spectrum of the unit round `S²` is `l(l+1)` with multiplicity `2l+1`
(`l = 0, 1, 2, …`), so the heat trace is `∑_l (2l+1) e^{-t l(l+1)}`. We *define* it by this series
(`sphereTrace`) and prove, by Euler–Maclaurin summation of order six
(`Lightlike.HeatKernel.abs_sum_sub_le`) applied to `sphereG t`, the trust check of the row

`∑ (2l+1) e^{-t l(l+1)} = 1/t + 1/3 + t/15 + O(t²)`   as `t → 0⁺`.

## Main results

* `Lightlike.HeatKernel.summable_sphereG`: the series converges for `t > 0`.
* `Lightlike.HeatKernel.hasHeatExpansionTo_sphereTrace`: `HasHeatExpansionTo 2 3 sphereTrace sphereCoeff`
  with `sphereCoeff = (1, 1/3, 1/15)`; here `a₁ = 1/3 = (4π)⁻¹ · vol(S²) · R/6` with `R = 2`.
-/

open Filter Topology Asymptotics

noncomputable section

namespace Lightlike.HeatKernel

/-- The heat trace of the unit round `S²`: `∑_{l ≥ 0} (2l+1) e^{-t l(l+1)}`. -/
def sphereTrace (t : ℝ) : ℝ := ∑' l : ℕ, sphereG t (l : ℝ)

/-- The first three heat coefficients `(a₀, a₁, a₂) = (1, 1/3, 1/15)` of `S²` (the rest set to `0`:
only the first three are meaningful here). -/
def sphereCoeff : ℕ → ℝ
  | 0 => 1
  | 1 => 1 / 3
  | 2 => 1 / 15
  | _ => 0

/-- The series `∑ (2l+1) e^{-t l(l+1)}` converges for `t > 0`. -/
theorem summable_sphereG {t : ℝ} (ht : 0 < t) : Summable fun l : ℕ => sphereG t (l : ℝ) := by
  have hlt : Real.exp (-t) < 1 := by
    simpa using Real.exp_lt_exp.mpr (neg_lt_zero.mpr ht)
  have hr : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hlt
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have h2 := summable_geometric_of_lt_one (Real.exp_pos (-t)).le hlt
  refine Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_) ((h1.mul_left 2).add h2)
  · unfold sphereG; positivity
  · unfold sphereG
    have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have key : Real.exp (-(t * ((l : ℝ) * (l + 1)))) ≤ Real.exp (-t) ^ l := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg ht.le hl, mul_nonneg (mul_nonneg ht.le hl) hl]
    calc (2 * (l : ℝ) + 1) * Real.exp (-(t * ((l : ℝ) * (l + 1))))
        ≤ (2 * (l : ℝ) + 1) * Real.exp (-t) ^ l :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = 2 * ((l : ℝ) ^ 1 * Real.exp (-t) ^ l) + Real.exp (-t) ^ l := by ring

/-- The polynomial remainder: the Euler–Maclaurin boundary terms of `sphereG t` equal
`1/t + 1/3 + t/15 + t² q(t)`. -/
def sphereQ (t : ℝ) : ℝ :=
  (12 - t) / 720 - bernoulliFun 6 0 * (120 - 180 * t + 30 * t ^ 2 - t ^ 3) / 720

/-- Euler–Maclaurin bound for the `S²` heat trace, uniformly for `0 < t ≤ 1`. -/
theorem sphereTrace_bound : ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
    |sphereTrace t - (1 / t + 1 / 3 + t / 15 + t ^ 2 * sphereQ t)| ≤ C * t ^ 2 := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, |bernoulliFun 6 x| ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (continuous_bernoulliFun 6).continuousOn
    exact ⟨M, fun x hx => by simpa using hM x hx⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  set J : ℝ := ∫ u, |iteratedDeriv 6 gaussOdd u| with hJ
  have hJ0 : 0 ≤ J := MeasureTheory.integral_nonneg fun u => abs_nonneg _
  refine ⟨M / 720 * (2 * Real.exp 1 * J), fun t ht ht1 => ?_⟩
  have hS := (summable_sphereG ht).hasSum.tendsto_sum_nat
  have h := abs_sum_sub_le (sphereG t) (sphereG_smooth ht)
    (by simpa using (integrable_iteratedDeriv_sphereG ht 0).integrableOn)
    (by simpa using tendsto_iteratedDeriv_sphereG ht 0)
    (tendsto_iteratedDeriv_sphereG ht 1) (tendsto_iteratedDeriv_sphereG ht 3)
    (tendsto_iteratedDeriv_sphereG ht 5)
    (integrable_iteratedDeriv_sphereG ht 6).integrableOn _ hS M hM
  rw [integral_sphereG ht, iteratedDeriv_sphereG_one_zero, iteratedDeriv_sphereG_three_zero,
    iteratedDeriv_sphereG_five_zero] at h
  have hg0 : sphereG t 0 = 1 := by simpa using iteratedDeriv_sphereG_zero t
  rw [hg0] at h
  have hb := integral_abs_sphereG_six_le ht
  have hexp : Real.exp (t / 4) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
  have hform : (1 / t + 1 / 2 - (2 - t) / 12 + (-12 * t + 12 * t ^ 2 - t ^ 3) / 720
        - bernoulliFun 6 0 * (120 * t ^ 2 - 180 * t ^ 3 + 30 * t ^ 4 - t ^ 5) / 720)
      = 1 / t + 1 / 3 + t / 15 + t ^ 2 * sphereQ t := by
    unfold sphereQ; ring
  have h' : |sphereTrace t - (1 / t + 1 / 3 + t / 15 + t ^ 2 * sphereQ t)| ≤
      M / 720 * ∫ x in Set.Ioi (0 : ℝ), |iteratedDeriv 6 (sphereG t) x| := by
    rw [← hform]
    unfold sphereTrace
    convert h using 3
  refine h'.trans ?_
  calc M / 720 * ∫ x in Set.Ioi (0 : ℝ), |iteratedDeriv 6 (sphereG t) x|
      ≤ M / 720 * (2 * Real.exp (t / 4) * t ^ 2 * J) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ M / 720 * (2 * Real.exp 1 * J) * t ^ 2 := by
        have : 2 * Real.exp (t / 4) * t ^ 2 * J ≤ 2 * Real.exp 1 * J * t ^ 2 := by
          have h2 : Real.exp (t / 4) * J ≤ Real.exp 1 * J := mul_le_mul_of_nonneg_right hexp hJ0
          nlinarith [sq_nonneg t]
        calc M / 720 * (2 * Real.exp (t / 4) * t ^ 2 * J)
            ≤ M / 720 * (2 * Real.exp 1 * J * t ^ 2) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = M / 720 * (2 * Real.exp 1 * J) * t ^ 2 := by ring

/-- For `t > 0` the first three terms of the expansion are `1/t + 1/3 + t/15`. -/
theorem sphere_partial_sum (t : ℝ) :
    ∑ k ∈ Finset.range 3, sphereCoeff k * t ^ ((k : ℝ) - ((2 : ℕ) : ℝ) / 2) =
      1 / t + 1 / 3 + t / 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [sphereCoeff]
  rw [Real.rpow_neg_one]
  ring

/-- **Heat trace of the unit round `S²`** (trust check of the row):
`∑_{l} (2l+1) e^{-t l(l+1)} = 1/t + 1/3 + t/15 + O(t²)` as `t → 0⁺`, i.e. the expansion
`HasHeatExpansionTo 2 3` with coefficients `a₀ = 1`, `a₁ = 1/3`, `a₂ = 1/15`. -/
theorem hasHeatExpansionTo_sphereTrace : HasHeatExpansionTo 2 3 sphereTrace sphereCoeff := by
  obtain ⟨C, hC⟩ := sphereTrace_bound
  have hrp : (fun t : ℝ => t ^ (((3 : ℕ) : ℝ) - ((2 : ℕ) : ℝ) / 2)) = fun t => t ^ 2 := by
    funext t
    have : ((3 : ℕ) : ℝ) - ((2 : ℕ) : ℝ) / 2 = ((2 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast]
  unfold HasHeatExpansionTo
  rw [hrp]
  have h1 : (fun t => sphereTrace t - (1 / t + 1 / 3 + t / 15 + t ^ 2 * sphereQ t))
      =O[𝓝[>] (0 : ℝ)] fun t => t ^ 2 := by
    refine IsBigO.of_bound C ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos ht.1 2)]
    exact hC t ht.1 ht.2
  have hq : Continuous sphereQ := by unfold sphereQ; fun_prop
  have h2 : (fun t : ℝ => t ^ 2 * sphereQ t) =O[𝓝[>] (0 : ℝ)] fun t => t ^ 2 := by
    have hq1 : sphereQ =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
      ((hq.tendsto 0).mono_left nhdsWithin_le_nhds).isBigO_one ℝ
    simpa using (isBigO_refl (fun t : ℝ => t ^ 2) (𝓝[>] (0 : ℝ))).mul hq1
  refine (h1.add h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [sphere_partial_sum t]
  ring

end Lightlike.HeatKernel
