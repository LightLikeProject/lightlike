import Mathlib
import Lightlike.Geometry.HeatKernel.EulerMaclaurinSum
import Lightlike.Geometry.HeatKernel.Sphere3Summand
import Lightlike.Geometry.HeatKernel.Expansion
import Lightlike.Geometry.HeatKernel.Torus

/-!
# The heat trace of the unit round `S³`

The Laplace–Beltrami spectrum of the unit round `S³` is `l(l+2)` with multiplicity `(l+1)²`, so the
heat trace is `∑_{l ≥ 0} (l+1)² e^{-t l(l+2)} = e^t ∑_{m ≥ 1} m² e^{-t m²}`. We *define* it by the
first series (`sphere3Trace`) and prove, by Euler–Maclaurin summation of order six applied to
`s3G t x = x² e^{-t x²}` (all odd derivatives at `0` vanish, `s3G t 0 = 0`),

`∑ (l+1)² e^{-t l(l+2)} = (√π/4) t^{-3/2} (1 + t + t²/2) + O(t^{3/2})`   as `t → 0⁺`.

In geometric terms (`vol S³ = 2π²`, `R = 6`, `|Ric|² = |Riem|²/… = 12`):
`a₀ = (4π)^{-3/2} · 2π² = √π/4`, `a₁ = a₀ R/6 = √π/4`, `a₂ = √π/8`.

## Main results

* `sphere3Trace_eq`: `sphere3Trace t = e^t ∑_{m} m² e^{-t m²}`.
* `hasHeatExpansionTo_sphere3Trace`: `HasHeatExpansionTo 3 3 sphere3Trace sphere3Coeff`.
-/

open Filter Topology Asymptotics

noncomputable section

namespace Lightlike.HeatKernel

/-- The heat trace of the unit round `S³`: `∑_{l ≥ 0} (l+1)² e^{-t l(l+2)}`. -/
def sphere3Trace (t : ℝ) : ℝ :=
  ∑' l : ℕ, ((l : ℝ) + 1) ^ 2 * Real.exp (-(t * ((l : ℝ) * ((l : ℝ) + 2))))

/-- The coefficients `(a₀, a₁, a₂) = (√π/4, √π/4, √π/8)` of `S³` (the rest set to `0`). -/
def sphere3Coeff : ℕ → ℝ
  | 0 => Real.sqrt Real.pi / 4
  | 1 => Real.sqrt Real.pi / 4
  | 2 => Real.sqrt Real.pi / 8
  | _ => 0

/-- The series `∑ j² e^{-t j²}` converges for `t > 0`. -/
theorem summable_s3G {t : ℝ} (ht : 0 < t) : Summable fun j : ℕ => s3G t (j : ℝ) := by
  have hlt : Real.exp (-t) < 1 := by
    simpa using Real.exp_lt_exp.mpr (neg_lt_zero.mpr ht)
  have hr : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hlt
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr
  refine Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_) h1
  · unfold s3G; positivity
  · unfold s3G
    have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have key : Real.exp (-(t * (l : ℝ) ^ 2)) ≤ Real.exp (-t) ^ l := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      rcases Nat.eq_zero_or_pos l with h | h
      · subst h; simp
      · have h1 : (1 : ℝ) ≤ l := by exact_mod_cast h
        nlinarith [mul_nonneg ht.le hl, mul_nonneg ht.le (sub_nonneg.mpr h1), mul_nonneg (mul_nonneg ht.le hl) (sub_nonneg.mpr h1)]
    exact mul_le_mul_of_nonneg_left key (by positivity)

/-- The `S³` heat trace is `e^t ∑_{m ≥ 0} m² e^{-t m²}`. -/
theorem sphere3Trace_eq {t : ℝ} (ht : 0 < t) :
    sphere3Trace t = Real.exp t * ∑' j : ℕ, s3G t (j : ℝ) := by
  have h0 : s3G t ((0 : ℕ) : ℝ) = 0 := by simp [s3G]
  rw [(summable_s3G ht).tsum_eq_zero_add, h0, zero_add, ← tsum_mul_left]
  unfold sphere3Trace
  refine tsum_congr fun l => ?_
  simp only [s3G, Nat.cast_add, Nat.cast_one]
  rw [mul_left_comm (Real.exp t), ← Real.exp_add]
  congr 2
  ring

/-- Euler–Maclaurin bound for the sum `∑ j² e^{-t j²}`: error `O(t^{3/2})`. -/
theorem s3_sum_bound : ∃ C : ℝ, ∀ t : ℝ, 0 < t →
    |(∑' j : ℕ, s3G t (j : ℝ)) - Real.sqrt Real.pi / 4 * t ^ (-(3 / 2) : ℝ)| ≤
      C * t ^ (3 / 2 : ℝ) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, |bernoulliFun 6 x| ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (continuous_bernoulliFun 6).continuousOn
    exact ⟨M, fun x hx => by simpa using hM x hx⟩
  set J : ℝ := ∫ u, |iteratedDeriv 6 gaussEven u| with hJ
  have hJ0 : 0 ≤ J := MeasureTheory.integral_nonneg fun u => abs_nonneg _
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨M / 720 * J, fun t ht => ?_⟩
  have hS := (summable_s3G ht).hasSum.tendsto_sum_nat
  have h := abs_sum_sub_le (s3G t) (s3G_smooth ht)
    (by simpa using (integrable_iteratedDeriv_s3G ht 0).integrableOn)
    (by simpa using tendsto_iteratedDeriv_s3G ht 0)
    (tendsto_iteratedDeriv_s3G ht 1) (tendsto_iteratedDeriv_s3G ht 3)
    (tendsto_iteratedDeriv_s3G ht 5)
    (integrable_iteratedDeriv_s3G ht 6).integrableOn _ hS M hM
  rw [integral_s3G ht, iteratedDeriv_s3G_odd_zero ht (by decide : Odd 1),
    iteratedDeriv_s3G_odd_zero ht (by decide : Odd 3),
    iteratedDeriv_s3G_odd_zero ht (by decide : Odd 5)] at h
  have hg0 : s3G t 0 = 0 := by simp [s3G]
  rw [hg0] at h
  have hb := integral_abs_s3G_six_le ht
  have hpow : t ^ 2 * (Real.sqrt t)⁻¹ = t ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le, show (t ^ 2 : ℝ) = t ^ (2 : ℝ) by
      rw [Real.rpow_two], ← Real.rpow_add ht]
    norm_num
  rw [hpow] at hb
  have h' : |(∑' j : ℕ, s3G t (j : ℝ)) - Real.sqrt Real.pi / 4 * t ^ (-(3 / 2) : ℝ)| ≤
      M / 720 * ∫ x in Set.Ioi (0 : ℝ), |iteratedDeriv 6 (s3G t) x| := by
    convert h using 3
    ring
  refine h'.trans ?_
  calc M / 720 * ∫ x in Set.Ioi (0 : ℝ), |iteratedDeriv 6 (s3G t) x|
      ≤ M / 720 * (t ^ (3 / 2 : ℝ) * J) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = M / 720 * J * t ^ (3 / 2 : ℝ) := by ring

end Lightlike.HeatKernel
