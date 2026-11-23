import Mathlib
import Lightlike.Geometry.HeatKernel.Sphere3Trace
import Lightlike.Geometry.HeatKernel.Consistency

/-!
# The `S³` heat-trace expansion and its Seeley–DeWitt coefficients

From the Euler–Maclaurin bound for `∑ m² e^{-t m²}` (`s3_sum_bound`) and the Taylor bound
`e^t = 1 + t + t²/2 + O(t³)` we obtain the third trust check of the geometry:

`∑_{l ≥ 0} (l+1)² e^{-t l(l+2)} = (√π/4) (t^{-3/2} + t^{-1/2} + t^{1/2}/2) + O(t^{3/2})`.

This is the expansion of `-Δ` on the unit round `S³` (`V = 2π²`, `R = 6`, `|Ric|² = 12`,
`|Riem|² = 12`): `a₁ = (4π)^{-3/2} V R/6 = a₀`, in agreement with `heatCoeffs`.

## Main results

* `hasHeatExpansionTo_sphere3Trace`: `HasHeatExpansionTo 3 3 sphere3Trace sphere3Coeff`.
* `hasHeatExpansionTo_sphere3Trace_geom`: the same with the coefficients `heatCoeffs 3 (2π²) 6 12 12`.
-/

open Filter Topology Asymptotics Real

noncomputable section

namespace Lightlike.HeatKernel

/-- The three terms of the expansion of `S³`, as a function of `t > 0`. -/
theorem sphere3_partial_sum {t : ℝ} (ht : 0 < t) :
    ∑ k ∈ Finset.range 3, sphere3Coeff k * t ^ ((k : ℝ) - ((3 : ℕ) : ℝ) / 2) =
      Real.sqrt π / 4 * t ^ (-(3 / 2) : ℝ) * (1 + t + t ^ 2 / 2) := by
  have e0 : t ^ ((0 : ℝ) - 3 / 2) = t ^ (-(3 / 2) : ℝ) := by
    norm_num
  have e1 : t ^ ((1 : ℝ) - 3 / 2) = t ^ (-(3 / 2) : ℝ) * t := by
    rw [← Real.rpow_add_one ht.ne']; norm_num
  have e2 : t ^ ((2 : ℝ) - 3 / 2) = t ^ (-(3 / 2) : ℝ) * t ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sphere3Coeff, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, zero_add]
  rw [e0, e1, e2]
  ring

/-- `e^t = 1 + t + t²/2 + O(t³)` as `t → 0⁺`. -/
theorem exp_sub_taylor_isBigO :
    (fun t : ℝ => Real.exp t - (1 + t + t ^ 2 / 2)) =O[𝓝[>] (0 : ℝ)] fun t => t ^ (3 : ℝ) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  have hb := Real.exp_bound (x := t) (by rw [abs_of_pos ht.1]; exact ht.2) (n := 3) (by norm_num)
  have hs : ∑ m ∈ Finset.range 3, t ^ m / (m.factorial : ℝ) = 1 + t + t ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs, abs_of_pos ht.1] at hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht.1 _),
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine hb.trans ?_
  have : ((Nat.succ 3 : ℕ) : ℝ) / ((Nat.factorial 3 : ℕ) * (3 : ℕ)) ≤ 1 := by
    norm_num [Nat.factorial]
  have h3 : (0 : ℝ) ≤ t ^ 3 := pow_nonneg ht.1.le 3
  nlinarith

/-- **Heat trace of the unit round `S³`**:
`∑_l (l+1)² e^{-t l(l+2)} = (√π/4)(t^{-3/2} + t^{-1/2} + t^{1/2}/2) + O(t^{3/2})`, i.e.
`HasHeatExpansionTo 3 3` with `a₀ = a₁ = √π/4`, `a₂ = √π/8`. -/
theorem hasHeatExpansionTo_sphere3Trace : HasHeatExpansionTo 3 3 sphere3Trace sphere3Coeff := by
  obtain ⟨C, hC⟩ := s3_sum_bound
  unfold HasHeatExpansionTo
  have hrp : (fun t : ℝ => t ^ (((3 : ℕ) : ℝ) - ((3 : ℕ) : ℝ) / 2)) = fun t => t ^ (3 / 2 : ℝ) := by
    funext t; norm_num
  rw [hrp]
  have hE : (fun t : ℝ => (∑' j : ℕ, s3G t (j : ℝ)) - Real.sqrt π / 4 * t ^ (-(3 / 2) : ℝ))
      =O[𝓝[>] (0 : ℝ)] fun t => t ^ (3 / 2 : ℝ) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht _)]
    exact hC t ht
  have hexp : (fun t : ℝ => Real.exp t) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((Real.continuous_exp.tendsto 0).mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  have h1 := (hexp.mul hE).congr_right fun t => one_mul _
  have h2 := (isBigO_mul_rpow (isBigO_refl (fun t : ℝ => t ^ (-(3 / 2) : ℝ)) (𝓝[>] (0 : ℝ)))
    exp_sub_taylor_isBigO).const_mul_left (Real.sqrt π / 4)
  have e : (-(3 / 2) : ℝ) + 3 = 3 / 2 := by norm_num
  rw [e] at h2
  refine (h1.add h2).congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [sphere3Trace_eq ht, sphere3_partial_sum ht]
    ring
  · filter_upwards with t
    simp

/-- `S³` has volume `2π²`, scalar curvature `6`, `|Ric|² = 12`, `|Riem|² = 12`; the coefficients
`(4π)^{-3/2} · 2π² · (1, R/6, (5R² - 2|Ric|² + 2|Riem|²)/360)` are `(√π/4)(1, 1, 1/2)`. -/
theorem heatCoeffs_sphere3 (k : ℕ) (hk : k < 3) :
    heatCoeffs 3 (2 * π ^ 2) 6 12 12 k = sphere3Coeff k := by
  have h : (4 * π) ^ (-(((3 : ℕ) : ℝ) / 2)) * (2 * π ^ 2) = Real.sqrt π / 4 := by
    have hπ := Real.pi_pos
    have h4 : (4 * π) ^ (-(((3 : ℕ) : ℝ) / 2)) = ((2 * Real.sqrt π) ^ 3)⁻¹ := by
      have : (4 * π) = (2 * Real.sqrt π) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hπ.le]; ring
      rw [this, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_neg (by positivity)]
      congr 1
      norm_num
    rw [h4]
    have hs : Real.sqrt π ^ 2 = π := Real.sq_sqrt hπ.le
    have hs0 : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr hπ).ne'
    field_simp
    nlinarith [hs]
  interval_cases k
  · simp only [heatCoeffs, sphere3Coeff]; rw [h]
  · simp only [heatCoeffs, sphere3Coeff]; linarith [h]
  · simp only [heatCoeffs, sphere3Coeff]; linarith [h]

/-- **Heat trace of the unit round `S³`, geometric form**: the expansion has the Seeley–DeWitt
coefficients `a₀, a₁, a₂` of `-Δ` with `V = 2π²`, `R = 6`, `|Ric|² = |Riem|² = 12`;
in particular `a₁ = (4π)^{-3/2} V R/6`. -/
theorem hasHeatExpansionTo_sphere3Trace_geom :
    HasHeatExpansionTo 3 3 sphere3Trace (heatCoeffs 3 (2 * π ^ 2) 6 12 12) :=
  hasHeatExpansionTo_sphere3Trace.congr_coeff fun k hk => (heatCoeffs_sphere3 k hk).symm

end Lightlike.HeatKernel
