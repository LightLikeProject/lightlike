import Mathlib
import Lightlike.Geometry.HeatKernel.Expansion

/-!
# Heat-trace expansion with a constant potential `E`

Pass 4 of row G1-018. For the Laplace-type operator `D = -(Δ + E)` with a constant scalar potential
`E = c`, `e^{-tD} = e^{tc} e^{tΔ}`, so the heat trace is `e^{tc}` times the trace of `e^{tΔ}`.
The Seeley–DeWitt coefficient is then `a₁ = (4π)^{-n/2} V (6E + R)/6`, the "6E" of
Vassilevich (key `vassilevich-2003`, eq. (4.27)).

## Main results

* `exp_mul_taylor_isBigO`: `e^{ct} = Σ_{j<M} c^j t^j / j! + O(t^M)`.
* `hasHeatExpansionTo_monomial_exp`: the expansion of `t^{i-n/2} e^{ct}`.
-/

open Filter Topology Asymptotics Real

noncomputable section

namespace Lightlike.HeatKernel

/-- **Taylor remainder of `e^{ct}`.** For `M > 0`,
`e^{ct} - Σ_{j<M} c^j/j! t^j = O(t^M)` as `t → 0⁺`. -/
theorem exp_mul_taylor_isBigO (c : ℝ) {M : ℕ} (hM : 0 < M) :
    (fun t : ℝ => Real.exp (c * t) - ∑ j ∈ Finset.range M, c ^ j / (j.factorial : ℝ) * t ^ j)
      =O[𝓝[>] (0 : ℝ)] fun t => t ^ M := by
  refine IsBigO.of_bound (|c| ^ M * (((M.succ : ℕ) : ℝ) / ((M.factorial : ℕ) * (M : ℕ)))) ?_
  have hδ : (0 : ℝ) < 1 / (|c| + 1) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
  have ht0 : 0 < t := ht.1
  have hct : |c * t| ≤ 1 := by
    rw [abs_mul, abs_of_pos ht0]
    have h1 : t * (|c| + 1) < 1 := by
      have := ht.2
      rw [lt_div_iff₀ (by positivity)] at this
      exact this
    nlinarith [abs_nonneg c]
  have hb := Real.exp_bound hct hM
  have hs : ∑ m ∈ Finset.range M, (c * t) ^ m / (m.factorial : ℝ) =
      ∑ j ∈ Finset.range M, c ^ j / (j.factorial : ℝ) * t ^ j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow]; ring
  rw [hs, abs_mul, abs_of_pos ht0, mul_pow] at hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos ht0 M)]
  calc _ ≤ |c| ^ M * t ^ M * (((M.succ : ℕ) : ℝ) / ((M.factorial : ℕ) * (M : ℕ))) := hb
    _ = _ := by ring

/-- **Expansion of a shifted exponential.** For `M > 0`, the function `t^{i - n/2} e^{ct}` has the
expansion to order `i + M` with coefficients `c^{k-i}/(k-i)!` for `k ≥ i` (and `0` for `k < i`). -/
theorem hasHeatExpansionTo_monomial_exp (n i : ℕ) (c : ℝ) {M : ℕ} (hM : 0 < M) :
    HasHeatExpansionTo n (i + M) (fun t => t ^ ((i : ℝ) - n / 2) * Real.exp (c * t))
      (fun k => if i ≤ k then c ^ (k - i) / ((k - i).factorial : ℝ) else 0) := by
  unfold HasHeatExpansionTo
  have h := (isBigO_refl (fun t : ℝ => t ^ ((i : ℝ) - n / 2)) (𝓝[>] (0 : ℝ))).mul
    (exp_mul_taylor_isBigO c hM)
  refine h.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [Finset.sum_range_add]
    have h0 : ∑ k ∈ Finset.range i, (if i ≤ k then c ^ (k - i) / ((k - i).factorial : ℝ) else 0) *
        t ^ ((k : ℝ) - n / 2) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk' : ¬ i ≤ k := by simpa using hk
      simp [hk']
    rw [h0, zero_add, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left]
    have : t ^ (((i + j : ℕ) : ℝ) - n / 2) = t ^ ((i : ℝ) - n / 2) * t ^ j := by
      rw [← Real.rpow_natCast t j, ← Real.rpow_add ht]
      congr 1; push_cast; ring
    rw [this]; ring
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    show t ^ ((i : ℝ) - n / 2) * t ^ M = t ^ (((i + M : ℕ) : ℝ) - n / 2)
    rw [← Real.rpow_natCast t M, ← Real.rpow_add ht]
    congr 1; push_cast; ring

end Lightlike.HeatKernel
