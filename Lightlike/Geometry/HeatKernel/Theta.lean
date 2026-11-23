import Mathlib
import Lightlike.Geometry.HeatKernel.Expansion

/-!
# The heat trace of the circle (one-dimensional flat torus)

For the circle `ℝ/2πℤ` the Laplacian has eigenvalues `k²`, `k ∈ ℤ`, so the heat trace is
`thetaSum t = Σ_{k ∈ ℤ} e^{-t k²}`. Poisson summation (Mathlib's `Real.tsum_exp_neg_mul_int_sq`)
gives `thetaSum t = √(π/t) · Σ_k e^{-π² k²/t}`, hence
`thetaSum t - √(π/t) = O(t^N)` for every `N` as `t → 0⁺`: the expansion has `a₀ = √π` (that is
`vol · (4π)^{-1/2}` with `vol = 2π`) and no further term, in particular no `t⁰` term.

## Main results

* `thetaSum_eq`: the Poisson-summation identity.
* `thetaSum_sub_isBigO`: `thetaSum t - √(π/t) = O(t^N)` for every real `N`.
* `hasHeatExpansion_thetaSum`: `HasHeatExpansion 1 thetaSum (a₀ = √π, a_k = 0 for k ≥ 1)`.
-/

open Filter Topology Asymptotics Real

noncomputable section

namespace Lightlike.HeatKernel

/-- The heat trace `Σ_{k∈ℤ} e^{-t k²}` of the circle `ℝ/2πℤ`. -/
def thetaSum (t : ℝ) : ℝ := ∑' k : ℤ, Real.exp (-t * (k : ℝ) ^ 2)

/-- **Poisson summation for the circle heat trace**:
`Σ e^{-t k²} = √(π/t) Σ e^{-π² k²/t}` for `t > 0`. -/
theorem thetaSum_eq {t : ℝ} (ht : 0 < t) :
    thetaSum t = Real.sqrt (π / t) * ∑' k : ℤ, Real.exp (-(π * (π / t)) * (k : ℝ) ^ 2) := by
  have hπ := Real.pi_pos
  have h := Real.tsum_exp_neg_mul_int_sq (a := t / π) (div_pos ht hπ)
  have e1 : ∀ k : ℤ, -π * (t / π) * (k : ℝ) ^ 2 = -t * (k : ℝ) ^ 2 := by
    intro k; field_simp
  have e2 : ∀ k : ℤ, -π / (t / π) * (k : ℝ) ^ 2 = -(π * (π / t)) * (k : ℝ) ^ 2 := by
    intro k; field_simp
  simp only [e1, e2] at h
  have e3 : (1 : ℝ) / (t / π) ^ (1 / 2 : ℝ) = Real.sqrt (π / t) := by
    rw [← Real.sqrt_eq_rpow, one_div, ← Real.sqrt_inv, inv_div]
  rw [e3] at h
  exact h

/-- `exp(-c/t) = o(t^s)` as `t → 0⁺`, for `c > 0`. -/
theorem exp_neg_div_isLittleO {c : ℝ} (hc : 0 < c) (s : ℝ) :
    (fun t : ℝ => Real.exp (-c / t)) =o[𝓝[>] (0 : ℝ)] fun t => t ^ s := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop hc (-s)).comp_tendsto
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
  refine h.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp [Function.comp, div_eq_mul_inv]
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp [Function.comp, Real.inv_rpow ht.le, Real.rpow_neg ht.le]

/-- For `s ≥ 1`: `|Σ e^{-π s k²} - 1| ≤ C e^{-π s}`, from Mathlib's bound on `jacobiTheta`. -/
theorem abs_tsum_sub_one_le {s : ℝ} (hs : 1 ≤ s) :
    |(∑' k : ℤ, Real.exp (-(π * s) * (k : ℝ) ^ 2)) - 1| ≤
      2 / (1 - Real.exp (-π)) * Real.exp (-π * s) := by
  have hπ := Real.pi_pos
  have hs0 : 0 < s := by linarith
  set τ : ℂ := (s : ℂ) * Complex.I with hτ
  have him : τ.im = s := by simp [hτ]
  have hτpos : 0 < τ.im := by rw [him]; exact hs0
  have hcast : ((∑' k : ℤ, Real.exp (-(π * s) * (k : ℝ) ^ 2) : ℝ) : ℂ) = jacobiTheta τ := by
    rw [Complex.ofReal_tsum, jacobiTheta]
    refine tsum_congr fun k => ?_
    rw [Complex.ofReal_exp]
    congr 1
    simp only [hτ]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hb := norm_jacobiTheta_sub_one_le hτpos
  rw [him] at hb
  have h1 : ‖jacobiTheta τ - 1‖ = |(∑' k : ℤ, Real.exp (-(π * s) * (k : ℝ) ^ 2)) - 1| := by
    rw [← hcast, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [h1] at hb
  refine hb.trans ?_
  have hexp : Real.exp (-π * s) ≤ Real.exp (-π) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hlt : Real.exp (-π) < 1 := by
    simpa using Real.exp_lt_exp.mpr (show -π < 0 by linarith)
  have hpos : 0 < 1 - Real.exp (-π) := by linarith
  have : 2 / (1 - Real.exp (-π * s)) ≤ 2 / (1 - Real.exp (-π)) :=
    div_le_div_of_nonneg_left (by norm_num) hpos (by linarith)
  exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

/-- **No `t⁰` term for the circle:** `Σ e^{-t k²} - √(π/t) = O(t^N)` for every real `N`. -/
theorem thetaSum_sub_isBigO (N : ℝ) :
    (fun t => thetaSum t - Real.sqrt (π / t)) =O[𝓝[>] (0 : ℝ)] fun t => t ^ N := by
  have hπ := Real.pi_pos
  -- bound on the correction factor
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, 1 ≤ π / t := by
    have : ∀ᶠ t : ℝ in 𝓝[>] 0, t < π ∧ 0 < t := by
      filter_upwards [Ioo_mem_nhdsGT hπ] with t ht using ⟨ht.2, ht.1⟩
    filter_upwards [this] with t ht
    rw [le_div_iff₀ ht.2]; linarith [ht.1]
  have h2 : (fun t : ℝ => (∑' k : ℤ, Real.exp (-(π * (π / t)) * (k : ℝ) ^ 2)) - 1)
      =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-(π * π) / t) := by
    refine IsBigO.of_bound (2 / (1 - Real.exp (-π))) ?_
    filter_upwards [hev, self_mem_nhdsWithin] with t ht (ht0 : 0 < t)
    have := abs_tsum_sub_one_le ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    convert this using 2
    congr 1
    field_simp
  have h3 := h2.trans_isLittleO (exp_neg_div_isLittleO (mul_pos hπ hπ) (N + 1 / 2))
  have h1 : (fun t : ℝ => Real.sqrt (π / t)) =O[𝓝[>] (0 : ℝ)] fun t => t ^ (-(1 / 2) : ℝ) := by
    refine IsBigO.of_bound (Real.sqrt π) ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht0 : 0 < t)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (div_pos hπ ht0)),
      abs_of_pos (Real.rpow_pos_of_pos ht0 _), Real.sqrt_div hπ.le, Real.rpow_neg ht0.le,
      div_eq_mul_inv]
    simp only [Real.sqrt_eq_rpow]
    exact le_rfl
  have h4 := (h1.mul_isLittleO h3).isBigO
  refine h4.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t (ht0 : 0 < t)
    rw [thetaSum_eq ht0]
    ring
  · filter_upwards [self_mem_nhdsWithin] with t (ht0 : 0 < t)
    rw [← Real.rpow_add ht0]
    ring_nf

/-- **Heat-trace expansion of the circle:** `Σ_k e^{-t k²} ∼ √π · t^{-1/2}`, all further
coefficients `a_k` (`k ≥ 1`) being `0`. -/
theorem hasHeatExpansion_thetaSum :
    HasHeatExpansion 1 thetaSum (fun k => if k = 0 then Real.sqrt π else 0) := by
  have hπ := Real.pi_pos
  have hq : ∀ t : ℝ, 0 < t → Real.sqrt (π / t) = Real.sqrt π * t ^ (-(1 / 2) : ℝ) := by
    intro t ht
    rw [Real.sqrt_div hπ.le, Real.rpow_neg ht.le, Real.sqrt_eq_rpow, div_eq_mul_inv]
    simp only [Real.sqrt_eq_rpow]
  have hq' : (fun t : ℝ => Real.sqrt (π / t)) =O[𝓝[>] (0 : ℝ)] fun t => t ^ (-(1 / 2) : ℝ) :=
    (isBigO_const_mul_self (Real.sqrt π) (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) _).congr'
      (by filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t) using (hq t ht).symm)
      EventuallyEq.rfl
  intro N
  cases N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, Nat.cast_zero, Nat.cast_one]
    have := (thetaSum_sub_isBigO (-(1 / 2))).add hq'
    refine this.congr_left ?_ |>.congr_right ?_
    · intro t; ring
    · intro t; norm_num
  | succ N =>
    refine (thetaSum_sub_isBigO ((N + 1 : ℕ) - (1 : ℕ) / 2 : ℝ)).congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hs : ∑ k ∈ Finset.range (N + 1),
        (if k = 0 then Real.sqrt π else 0) * t ^ ((k : ℝ) - ((1 : ℕ) : ℝ) / 2)
        = Real.sqrt π * t ^ (-(1 / 2) : ℝ) := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; simp at h
    rw [hs, hq t ht]

end Lightlike.HeatKernel
