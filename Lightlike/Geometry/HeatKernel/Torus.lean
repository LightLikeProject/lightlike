import Mathlib
import Lightlike.Geometry.HeatKernel.Theta

/-!
# The heat trace of the flat torus `ℝⁿ/(2πℤ)ⁿ`

The Laplacian of the flat torus `ℝⁿ/(2πℤ)ⁿ` has eigenvalues `|k|² = Σ kᵢ²`, `k ∈ ℤⁿ`, so the heat
trace is `torusTrace n t = Σ_{k ∈ ℤⁿ} e^{-t |k|²}`. It factors as `(Σ_{k∈ℤ} e^{-t k²})ⁿ`, and the
circle result (`Theta.lean`) gives `torusTrace n t - (π/t)^{n/2} = O(t^N)` for all `N`: the expansion
is `(4π)^{-n/2} · vol · t^{-n/2}` with `vol = (2π)ⁿ` and has no `t⁰` term (nor any other).

## Main results

* `tsum_pi_prod`: `Σ_{k : Fin n → ℤ} ∏ f (kᵢ) = (Σ f)ⁿ`.
* `torusTrace_eq_thetaSum_pow`: `torusTrace n t = thetaSum t ^ n` for `t > 0`.
* `torusTrace_sub_isBigO`: `torusTrace n t - (π/t)^{n/2} = O(t^N)`, every real `N`.
* `hasHeatExpansion_torusTrace`: the full expansion (`a₀ = π^{n/2}`, all other `a_k = 0`).
-/

open Filter Topology Asymptotics Real

noncomputable section

namespace Lightlike.HeatKernel

/-- Tuples version of the product of sums: for `f` absolutely summable on `ℤ`,
`Σ_{k : Fin n → ℤ} ∏ᵢ f (kᵢ) = (Σ f)ⁿ`, the family being absolutely summable. -/
theorem tsum_pi_prod (f : ℤ → ℝ) (hf : Summable fun k => ‖f k‖) (n : ℕ) :
    (Summable fun k : Fin n → ℤ => ‖∏ i, f (k i)‖) ∧
      ∑' k : Fin n → ℤ, ∏ i, f (k i) = (∑' k, f k) ^ n := by
  induction n with
  | zero => simp; exact Summable.of_finite
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e := Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)
    have hprod : ∀ z : ℤ × (Fin n → ℤ),
        ∏ i, f ((Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)) z i) = f z.1 * ∏ i, f (z.2 i) := by
      intro z
      simp [Fin.prod_univ_succ]
    have hs : Summable fun z : ℤ × (Fin n → ℤ) =>
        ‖∏ i, f ((Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)) z i)‖ := by
      simp_rw [hprod]
      exact Summable.mul_norm (f := fun k => f k) (g := fun k : Fin n → ℤ => ∏ i, f (k i)) hf ih1
    refine ⟨?_, ?_⟩
    · exact (Equiv.summable_iff (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ))).mp hs
    · rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)).tsum_eq]
      simp_rw [hprod]
      rw [← tsum_mul_tsum_of_summable_norm (f := fun k => f k)
        (g := fun k : Fin n → ℤ => ∏ i, f (k i)) hf ih1, ih2, pow_succ, mul_comm]

/-- Summability of the Gaussian terms `e^{-t k²}` over `ℤ`, for `t > 0`. -/
theorem summable_exp_neg_int_sq {t : ℝ} (ht : 0 < t) :
    Summable fun k : ℤ => Real.exp (-t * (k : ℝ) ^ 2) := by
  have hgeo : Summable fun n : ℕ => Real.exp (-t) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simpa using ht)
  have hN : Summable fun n : ℕ => Real.exp (-t * ((n : ℤ) : ℝ) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hgeo
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    push_cast
    nlinarith
  refine Summable.of_nat_of_neg hN ?_
  simpa using hN

/-- The heat trace `Σ_{k ∈ ℤⁿ} e^{-t |k|²}` of the flat torus `ℝⁿ/(2πℤ)ⁿ`. -/
def torusTrace (n : ℕ) (t : ℝ) : ℝ :=
  ∑' k : Fin n → ℤ, Real.exp (-t * ∑ i, ((k i : ℤ) : ℝ) ^ 2)

/-- The torus trace is the `n`-th power of the circle trace. -/
theorem torusTrace_eq_thetaSum_pow (n : ℕ) {t : ℝ} (ht : 0 < t) :
    torusTrace n t = thetaSum t ^ n := by
  have hs : Summable fun k : ℤ => ‖Real.exp (-t * (k : ℝ) ^ 2)‖ := by
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using summable_exp_neg_int_sq ht
  have h := (tsum_pi_prod (fun k : ℤ => Real.exp (-t * (k : ℝ) ^ 2)) hs n).2
  unfold torusTrace thetaSum
  rw [← h]
  refine tsum_congr fun k => ?_
  rw [← Real.exp_sum, Finset.mul_sum]

/-- Product rule for power-type `O`-estimates at `0⁺`. -/
theorem isBigO_mul_rpow {f g : ℝ → ℝ} {a b : ℝ} (hf : f =O[𝓝[>] (0 : ℝ)] fun t => t ^ a)
    (hg : g =O[𝓝[>] (0 : ℝ)] fun t => t ^ b) :
    (fun t => f t * g t) =O[𝓝[>] (0 : ℝ)] fun t => t ^ (a + b) := by
  refine (hf.mul hg).congr' EventuallyEq.rfl ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [Real.rpow_add ht]

/-- `√(π/t) = O(t^{-1/2})` as `t → 0⁺`. -/
theorem sqrt_pi_div_isBigO :
    (fun t : ℝ => Real.sqrt (π / t)) =O[𝓝[>] (0 : ℝ)] fun t => t ^ (-(1 / 2) : ℝ) := by
  refine IsBigO.of_bound (Real.sqrt π) ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht0 : 0 < t)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (div_pos pi_pos ht0)),
    abs_of_pos (Real.rpow_pos_of_pos ht0 _), Real.sqrt_div pi_pos.le, Real.rpow_neg ht0.le,
    div_eq_mul_inv]
  simp only [Real.sqrt_eq_rpow]
  exact le_rfl

/-- `thetaSum t = O(t^{-1/2})` as `t → 0⁺`. -/
theorem thetaSum_isBigO :
    thetaSum =O[𝓝[>] (0 : ℝ)] fun t => t ^ (-(1 / 2) : ℝ) := by
  have := (thetaSum_sub_isBigO (-(1 / 2))).add sqrt_pi_div_isBigO
  exact this.congr_left (fun t => by ring)

/-- `thetaSum t ^ n = O(t^{-n/2})`. -/
theorem thetaSum_pow_isBigO (n : ℕ) :
    (fun t => thetaSum t ^ n) =O[𝓝[>] (0 : ℝ)] fun t => t ^ (-((n : ℝ) / 2)) := by
  refine (thetaSum_isBigO.pow n).congr' EventuallyEq.rfl ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  congr 1
  ring

/-- `thetaSum t ^ n - (√(π/t))^n = O(t^N)` for every real `N`. -/
theorem thetaSum_pow_sub_isBigO (n : ℕ) (N : ℝ) :
    (fun t => thetaSum t ^ n - Real.sqrt (π / t) ^ n) =O[𝓝[>] (0 : ℝ)] fun t => t ^ N := by
  induction n generalizing N with
  | zero => simpa using (isBigO_zero (fun t : ℝ => t ^ N) (𝓝[>] (0 : ℝ)))
  | succ n ih =>
    have h1 := isBigO_mul_rpow (thetaSum_pow_isBigO n)
      (thetaSum_sub_isBigO (N + (n : ℝ) / 2))
    have h2 := isBigO_mul_rpow sqrt_pi_div_isBigO (ih (N + 1 / 2))
    have e1 : -((n : ℝ) / 2) + (N + (n : ℝ) / 2) = N := by ring
    have e2 : -(1 / 2 : ℝ) + (N + 1 / 2) = N := by ring
    rw [e1] at h1
    rw [e2] at h2
    refine (h1.add h2).congr_left ?_
    intro t
    ring

/-- **No `t⁰` term for the flat torus:** `torusTrace n t - (π/t)^{n/2} = O(t^N)` for every
real `N` as `t → 0⁺`. -/
theorem torusTrace_sub_isBigO (n : ℕ) (N : ℝ) :
    (fun t => torusTrace n t - (π / t) ^ ((n : ℝ) / 2)) =O[𝓝[>] (0 : ℝ)] fun t => t ^ N := by
  refine (thetaSum_pow_sub_isBigO n N).congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have : (π / t) ^ ((n : ℝ) / 2) = Real.sqrt (π / t) ^ n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (_ ^ (1 / 2 : ℝ)) n,
      ← Real.rpow_mul (div_pos pi_pos ht).le]
    congr 1
    ring
  rw [torusTrace_eq_thetaSum_pow n ht, this]

/-- **Heat-trace expansion of the flat torus** `ℝⁿ/(2πℤ)ⁿ`:
`Σ_{k∈ℤⁿ} e^{-t|k|²} ∼ π^{n/2} t^{-n/2}`, i.e. `a₀ = (4π)^{-n/2} vol` with `vol = (2π)ⁿ`,
and `a_k = 0` for all `k ≥ 1` (in particular `a₁ = 0`, as `R = 0`). -/
theorem hasHeatExpansion_torusTrace (n : ℕ) :
    HasHeatExpansion n (torusTrace n) (fun k => if k = 0 then π ^ ((n : ℝ) / 2) else 0) := by
  have hq : ∀ t : ℝ, 0 < t → (π / t) ^ ((n : ℝ) / 2) = π ^ ((n : ℝ) / 2) * t ^ (-((n : ℝ) / 2)) := by
    intro t ht
    rw [Real.div_rpow pi_pos.le ht.le, Real.rpow_neg ht.le, div_eq_mul_inv]
  have hq' : (fun t : ℝ => (π / t) ^ ((n : ℝ) / 2)) =O[𝓝[>] (0 : ℝ)]
      fun t => t ^ (-((n : ℝ) / 2)) :=
    (isBigO_const_mul_self (π ^ ((n : ℝ) / 2)) (fun t : ℝ => t ^ (-((n : ℝ) / 2))) _).congr'
      (by filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t) using (hq t ht).symm)
      EventuallyEq.rfl
  intro N
  cases N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, Nat.cast_zero, zero_sub]
    have := (torusTrace_sub_isBigO n (-((n : ℝ) / 2))).add hq'
    refine this.congr_left ?_
    intro t; ring
  | succ N =>
    refine (torusTrace_sub_isBigO n ((N + 1 : ℕ) - (n : ℝ) / 2)).congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hs : ∑ k ∈ Finset.range (N + 1),
        (if k = 0 then π ^ ((n : ℝ) / 2) else 0) * t ^ ((k : ℝ) - (n : ℝ) / 2)
        = π ^ ((n : ℝ) / 2) * t ^ (-((n : ℝ) / 2)) := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; simp at h
    rw [hs, hq t ht]

end Lightlike.HeatKernel
