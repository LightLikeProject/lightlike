import Lightlike.Geometry.HeatKernel.Expansion

/-!
# Uniqueness of heat-trace coefficients

If `HasHeatExpansionTo n m K a` and `HasHeatExpansionTo n m K b`, then `a k = b k` for all
`k < m`. This makes the coefficients `a₀, a₁, …` of a heat-trace expansion well defined.

## Main results

* `Lightlike.HeatKernel.HasHeatExpansionTo.coeff_unique`
* `Lightlike.HeatKernel.HasHeatExpansion.coeff_unique`
-/

open Filter Topology Asymptotics

noncomputable section

namespace Lightlike.HeatKernel

/-- `t^{m+1-n/2} = O(t^{m-n/2})` as `t → 0⁺`. -/
lemma rpow_succ_isBigO (n m : ℕ) :
    (fun t : ℝ => t ^ (((m + 1 : ℕ) : ℝ) - n / 2)) =O[𝓝[>] (0 : ℝ)]
      fun t => t ^ ((m : ℝ) - n / 2) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  have h0 : t ^ (((m + 1 : ℕ) : ℝ) - n / 2) = t ^ ((m : ℝ) - n / 2) * t := by
    rw [← Real.rpow_add_one ht.1.ne']
    congr 1
    push_cast
    ring
  rw [h0, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos ht.1]
  have := mul_le_of_le_one_right (abs_nonneg (t ^ ((m : ℝ) - n / 2))) ht.2
  linarith

/-- A finite combination `Σ_{k<m} d k t^{k-n/2}` that is `O(t^{m-n/2})` has all coefficients zero. -/
lemma coeff_eq_zero_of_isBigO (n : ℕ) :
    ∀ (m : ℕ) (d : ℕ → ℝ),
      (fun t : ℝ => ∑ k ∈ Finset.range m, d k * t ^ ((k : ℝ) - n / 2)) =O[𝓝[>] (0 : ℝ)]
        (fun t => t ^ ((m : ℝ) - n / 2)) → ∀ k < m, d k = 0
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | m + 1, d, h, k, hk => by
    have hm : (fun t : ℝ => ∑ k ∈ Finset.range m, d k * t ^ ((k : ℝ) - n / 2))
        =O[𝓝[>] (0 : ℝ)] fun t => t ^ ((m : ℝ) - n / 2) := by
      have h1 := h.trans (rpow_succ_isBigO n m)
      have h2 : (fun t : ℝ => d m * t ^ ((m : ℝ) - n / 2)) =O[𝓝[>] (0 : ℝ)]
          fun t => t ^ ((m : ℝ) - n / 2) := (isBigO_refl _ _).const_mul_left _
      refine (h1.sub h2).congr_left ?_
      intro t
      simp [Finset.sum_range_succ]
    have hk0 := coeff_eq_zero_of_isBigO n m d hm
    have hdm : d m = 0 := by
      by_contra hne
      have hs : ∀ t : ℝ, ∑ k ∈ Finset.range (m + 1), d k * t ^ ((k : ℝ) - n / 2)
          = d m * t ^ ((m : ℝ) - n / 2) := by
        intro t
        rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun j hj => by
          rw [hk0 j (Finset.mem_range.mp hj), zero_mul]), zero_add]
      obtain ⟨C, hC⟩ := h.bound
      have hpos : 0 < |d m| / (|C| + 1) := div_pos (abs_pos.mpr hne) (by positivity)
      have hev : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), False := by
        filter_upwards [hC, Ioo_mem_nhdsGT hpos] with t ht htt
        obtain ⟨ht0, htc⟩ := htt
        rw [hs t] at ht
        set x := t ^ ((m : ℝ) - n / 2) with hx
        have hxp : 0 < x := Real.rpow_pos_of_pos ht0 _
        have h0 : t ^ (((m + 1 : ℕ) : ℝ) - n / 2) = x * t := by
          rw [hx, ← Real.rpow_add_one ht0.ne']
          congr 1
          push_cast
          ring
        rw [h0, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hxp,
          abs_of_pos ht0] at ht
        have h3 : |d m| * x ≤ (C * t) * x := by nlinarith
        have h4 : |d m| ≤ C * t := le_of_mul_le_mul_right h3 hxp
        have h5 : t * (|C| + 1) < |d m| := (lt_div_iff₀ (by positivity)).mp htc
        nlinarith [le_abs_self C, abs_nonneg C]
      obtain ⟨t, ht⟩ := hev.exists
      exact ht
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
    · exact hk0 k hlt
    · rw [heq]; exact hdm

/-- **Uniqueness of heat-trace coefficients.** Two finite-order expansions of the same `K` to
order `m` have the same coefficients `a k = b k` for `k < m`. -/
theorem HasHeatExpansionTo.coeff_unique {n m : ℕ} {K : ℝ → ℝ} {a b : ℕ → ℝ}
    (ha : HasHeatExpansionTo n m K a) (hb : HasHeatExpansionTo n m K b) :
    ∀ k < m, a k = b k := by
  have h := coeff_eq_zero_of_isBigO n m (fun k => b k - a k) (by
    refine (ha.sub hb).congr_left ?_
    intro t
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring)
  intro k hk
  have := h k hk
  linarith

/-- Coefficients of a full heat-trace expansion are unique. -/
theorem HasHeatExpansion.coeff_unique {n : ℕ} {K : ℝ → ℝ} {a b : ℕ → ℝ}
    (ha : HasHeatExpansion n K a) (hb : HasHeatExpansion n K b) : a = b := by
  funext k
  exact HasHeatExpansionTo.coeff_unique (ha (k + 1)) (hb (k + 1)) k (Nat.lt_succ_self k)

end Lightlike.HeatKernel
