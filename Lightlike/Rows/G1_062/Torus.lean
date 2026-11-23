import Mathlib
import Lightlike.Rows.G1_062.Defs

/-!
# Heat trace of the circle: exponentially small corrections

For the circle `ℝ/Lℤ` the Laplace spectrum is `(2πn/L)²`, `n ∈ ℤ`, each with multiplicity one.
By Poisson summation (`Real.tsum_exp_neg_mul_int_sq`) and the Jacobi theta bound
`norm_jacobiTheta_sub_one_le`, the heat trace is `L/√(4πt)` up to an error `O(e^{-L²/(4t)})`.

## Main results

* `Lightlike.Rows.G1_062.exp_neg_div_isBigO_pow`: `e^{-c/t} = O(t^N)` as `t → 0⁺`.
* `Lightlike.Rows.G1_062.circleTrace_sub_isBigO`: `Z_{S¹_L}(t) - L/√(4π) t^{-1/2}` is exponentially
  small as `t → 0⁺`.
-/

open Filter Topology Asymptotics Complex

namespace Lightlike.Rows.G1_062

/-- `e^{-c/t}` vanishes faster than any power of `t` as `t → 0⁺`. -/
theorem exp_neg_div_isBigO_pow {c : ℝ} (hc : 0 < c) (N : ℕ) :
    (fun t : ℝ => Real.exp (-c / t)) =O[𝓝[>] 0] fun t => t ^ N := by
  have hx : Tendsto (fun t : ℝ => c * t⁻¹) (𝓝[>] 0) atTop :=
    Tendsto.const_mul_atTop hc tendsto_inv_nhdsGT_zero
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).comp hx
  have h2 : Tendsto (fun t : ℝ => Real.exp (-c / t) / t ^ N) (𝓝[>] 0) (𝓝 0) := by
    have h3 := h1.const_mul ((c ^ N)⁻¹)
    rw [mul_zero] at h3
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    simp only [Function.comp]
    rw [mul_pow, inv_pow, neg_div, div_eq_mul_inv c t, neg_mul_eq_mul_neg]
    field_simp
  have h4 : (fun t : ℝ => Real.exp (-c / t)) =o[𝓝[>] 0] fun t => t ^ N := by
    rw [isLittleO_iff_tendsto']
    · exact h2
    · filter_upwards [self_mem_nhdsWithin] with t ht h0
      exact absurd h0 (pow_ne_zero _ (ne_of_gt ht))
  exact h4.isBigO

/-- The real theta sum is the complex Jacobi theta function at `i y`. -/
theorem ofReal_tsum_exp_eq_jacobiTheta {y : ℝ} :
    ((∑' n : ℤ, Real.exp (-Real.pi * y * (n : ℝ) ^ 2) : ℝ) : ℂ) = jacobiTheta (I * y) := by
  rw [Complex.ofReal_tsum, jacobiTheta]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  have : I * I = -1 := Complex.I_mul_I
  linear_combination (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * y) * this

/-- For `y ≥ 1`, the real theta sum `∑ₙ e^{-π y n²}` differs from `1` by `O(e^{-π y})`. -/
theorem abs_tsum_exp_sub_one_le {y : ℝ} (hy : 1 ≤ y) :
    |(∑' n : ℤ, Real.exp (-Real.pi * y * (n : ℝ) ^ 2)) - 1|
      ≤ 2 / (1 - Real.exp (-Real.pi)) * Real.exp (-Real.pi * y) := by
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  have h := norm_jacobiTheta_sub_one_le (τ := I * y) (by simpa using hy0)
  have him : (I * (y : ℂ)).im = y := by simp
  rw [him, ← ofReal_tsum_exp_eq_jacobiTheta] at h
  have e1 : ‖(((∑' n : ℤ, Real.exp (-Real.pi * y * (n : ℝ) ^ 2) : ℝ) : ℂ) - 1)‖
      = |(∑' n : ℤ, Real.exp (-Real.pi * y * (n : ℝ) ^ 2)) - 1| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [e1] at h
  refine h.trans ?_
  have hp : Real.exp (-Real.pi * y) ≤ Real.exp (-Real.pi) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hlt : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  have hpos : 0 < 1 - Real.exp (-Real.pi) := by linarith
  have : 1 - Real.exp (-Real.pi) ≤ 1 - Real.exp (-Real.pi * y) := by linarith
  have hpos2 : 0 < 1 - Real.exp (-Real.pi * y) := lt_of_lt_of_le hpos this
  gcongr

/-- The heat trace of the circle of length `L`: spectrum `(2πn/L)²`, `n ∈ ℤ`, multiplicity one. -/
noncomputable def circleTrace (L : ℝ) : ℝ → ℝ :=
  heatTrace (fun n : ℤ => (2 * Real.pi * n / L) ^ 2) (fun _ => 1)

/-- Poisson-resummed form of the circle heat trace:
`Z(t) = L/√(4π) · t^{-1/2} · ∑ₙ e^{-π (L²/(4π t)) n²}`. -/
theorem circleTrace_eq {L : ℝ} (hL : 0 < L) {t : ℝ} (ht : 0 < t) :
    circleTrace L t = L / Real.sqrt (4 * Real.pi) * t ^ (-(1 / 2 : ℝ)) *
      ∑' n : ℤ, Real.exp (-Real.pi * (L ^ 2 / (4 * Real.pi * t)) * (n : ℝ) ^ 2) := by
  have hpi := Real.pi_pos
  have ha : 0 < 4 * Real.pi * t / L ^ 2 := by positivity
  have h := Real.tsum_exp_neg_mul_int_sq ha
  have e1 : circleTrace L t =
      ∑' n : ℤ, Real.exp (-Real.pi * (4 * Real.pi * t / L ^ 2) * (n : ℝ) ^ 2) := by
    unfold circleTrace heatTrace
    refine tsum_congr fun n => ?_
    simp only [Nat.cast_one, one_mul]
    congr 1
    field_simp
    ring
  have e2 : ∀ n : ℤ, -Real.pi / (4 * Real.pi * t / L ^ 2) * (n : ℝ) ^ 2
      = -Real.pi * (L ^ 2 / (4 * Real.pi * t)) * (n : ℝ) ^ 2 := by
    intro n
    field_simp
  rw [e1, h]
  simp_rw [e2]
  have e3 : (4 * Real.pi * t / L ^ 2) ^ (1 / 2 : ℝ)
      = Real.sqrt (4 * Real.pi) / L * t ^ (1 / 2 : ℝ) := by
    rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) ht.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    have e4 : ((L ^ 2)⁻¹) ^ (1 / 2 : ℝ) = L⁻¹ := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_inv, Real.sqrt_sq hL.le]
    rw [e4]
    ring
  rw [e3, Real.rpow_neg ht.le]
  have : Real.sqrt (4 * Real.pi) ≠ 0 := by positivity
  have : t ^ (1 / 2 : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Circle heat trace.** For all `K ≥ 1`, `Z_{S¹_L}(t) = L/√(4π) · t^{-1/2} + O(t^{K-1/2})` as
`t → 0⁺`: the circle heat trace has `a₀ = L/√(4π)` and all higher coefficients zero. -/
theorem circleTrace_hasHeatExpansion {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 1 ≤ K) :
    HasHeatExpansion (circleTrace L) 1
      (fun k => if k = 0 then L / Real.sqrt (4 * Real.pi) else 0) K := by
  have hpi := Real.pi_pos
  set c : ℝ := L / Real.sqrt (4 * Real.pi) with hc
  have hsum : ∀ t : ℝ, ∑ k ∈ Finset.range K,
      (fun k : ℕ => if k = 0 then c else 0) k * t ^ ((k : ℝ) - ((1 : ℕ) : ℝ) / 2)
      = c * t ^ (-(1 / 2 : ℝ)) := by
    intro t
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd (Finset.mem_range.mpr hK) h
  unfold HasHeatExpansion
  simp_rw [hsum]
  -- the exponential error
  have hexp := exp_neg_div_isBigO_pow (c := L ^ 2 / 4) (by positivity) K
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < L ^ 2 / (4 * Real.pi) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by positivity))
  have hbound : (fun t : ℝ => ∑' n : ℤ, Real.exp (-Real.pi * (L ^ 2 / (4 * Real.pi * t))
      * (n : ℝ) ^ 2) - 1) =O[𝓝[>] 0] fun t => Real.exp (-(L ^ 2 / 4) / t) := by
    refine IsBigO.of_bound (2 / (1 - Real.exp (-Real.pi))) ?_
    filter_upwards [hpos, hsmall] with t ht hts
    have hy : 1 ≤ L ^ 2 / (4 * Real.pi * t) := by
      rw [le_div_iff₀ (by positivity)]
      rw [lt_div_iff₀ (by positivity)] at hts
      nlinarith
    have := abs_tsum_exp_sub_one_le hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine this.trans (le_of_eq ?_)
    congr 2
    field_simp
  have h2 : (fun t : ℝ => c * t ^ (-(1 / 2 : ℝ)) * (∑' n : ℤ, Real.exp (-Real.pi *
      (L ^ 2 / (4 * Real.pi * t)) * (n : ℝ) ^ 2) - 1)) =O[𝓝[>] 0]
      fun t => t ^ (-(1 / 2 : ℝ)) * t ^ K := by
    have := ((isBigO_refl (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) _).const_mul_left c).mul
      (hbound.trans hexp)
    exact this
  have h3 : (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * t ^ K) =ᶠ[𝓝[>] 0]
      fun t => t ^ ((K : ℝ) - ((1 : ℕ) : ℝ) / 2) := by
    filter_upwards [hpos] with t ht
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]
    congr 1
    push_cast
    ring
  refine (h2.trans h3.isBigO).congr' ?_ (EventuallyEq.rfl)
  filter_upwards [hpos] with t ht
  rw [circleTrace_eq hL ht]
  ring

end Lightlike.Rows.G1_062
