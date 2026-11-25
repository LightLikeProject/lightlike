import Mathlib
import Lightlike.Geometry.HeatTraceExpansion.Sums

/-!
# One level of the midpoint expansion

For `p, m : ℕ` there is a constant `c` such that for all `h ∈ (0, 1]`
`| - gu p 0 - ∑_{k<m+1} ((h/2)^k - (-(h/2))^k)/k! · ∑'_j gu (p+k) (mid h j) | ≤ c h^m`.
This is the sum over `j` of `midpoint_bound` on `[j h, (j+1) h]`, the left side telescoping to
`gu p (N h) - gu p 0`, followed by `N → ∞`.
-/

open Set Filter Topology

namespace Lightlike.Geometry.HeatTraceExpansion

lemma gu_tendsto_zero (p : ℕ) {h : ℝ} (h0 : 0 < h) :
    Tendsto (fun N : ℕ => gu p ((N : ℝ) * h)) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := gu_le p
  have hlim : Tendsto (fun N : ℕ => (C / h) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : 0 ≤ (N : ℝ) * h := by positivity
  have h1 := hC ((N : ℝ) * h) ((N : ℝ) * h) hx le_rfl
  rw [Real.norm_eq_abs]
  refine h1.trans ?_
  have hNh : 0 < (N : ℝ) * h := by positivity
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : (N : ℝ) * h ≤ (1 + (N : ℝ) * h) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this hC0]

/-- The remainder of the midpoint formula on the `j`-th interval. -/
noncomputable def remJ (p n : ℕ) (h : ℝ) (j : ℕ) : ℝ :=
  gu p (((j + 1 : ℕ) : ℝ) * h) - gu p ((j : ℝ) * h)
    - ∑ k ∈ Finset.range n, gu (p + k) (mid h j) * ((h / 2) ^ k - (-(h / 2)) ^ k) / (k.factorial : ℝ)

lemma remJ_bound (p m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ j : ℕ,
    |remJ p (m + 1) h j| ≤ C * h ^ m * (h / (1 + (j : ℝ) * h) ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := gu_le (p + (m + 1))
  refine ⟨2 * C, by positivity, fun h h0 j => ?_⟩
  have hchain : IsChain (fun i => gu (p + i)) := fun i => gu_chain (p + i)
  have hx : 0 ≤ (j : ℝ) * h := by positivity
  have hmid : mid h j - h / 2 = (j : ℝ) * h := by unfold mid; ring
  have hmid' : mid h j + h / 2 = ((j + 1 : ℕ) : ℝ) * h := by unfold mid; push_cast; ring
  have key := midpoint_bound (fun i => gu (p + i)) hchain (mid h j) (h / 2) (C / (1 + (j : ℝ) * h) ^ 2)
    (by positivity) (m + 1) (by
      intro y hy
      rw [hmid] at hy
      exact hC _ y hx hy.1)
  simp only [add_zero, hmid, hmid'] at key
  have hr : (h / 2) ^ (m + 1) / ((m + 1).factorial : ℝ) ≤ h ^ (m + 1) := by
    have hf : (1 : ℝ) ≤ ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    calc (h / 2) ^ (m + 1) / ((m + 1).factorial : ℝ) ≤ (h / 2) ^ (m + 1) :=
          div_le_self (by positivity) hf
      _ ≤ h ^ (m + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hW : 0 < (1 + (j : ℝ) * h) ^ 2 := by positivity
  unfold remJ
  refine key.trans ?_
  have e1 : 2 * (C / (1 + (j : ℝ) * h) ^ 2 * (h / 2) ^ (m + 1) / ((m + 1).factorial : ℝ))
      = 2 * (C / (1 + (j : ℝ) * h) ^ 2) * ((h / 2) ^ (m + 1) / ((m + 1).factorial : ℝ)) := by ring
  rw [e1]
  calc 2 * (C / (1 + (j : ℝ) * h) ^ 2) * ((h / 2) ^ (m + 1) / ((m + 1).factorial : ℝ))
      ≤ 2 * (C / (1 + (j : ℝ) * h) ^ 2) * h ^ (m + 1) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
    _ = 2 * C * h ^ m * (h / (1 + (j : ℝ) * h) ^ 2) := by ring

/-- One level of the midpoint expansion. -/
theorem level (p m : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
    |-gu p 0 - ∑ k ∈ Finset.range (m + 1),
        ((h / 2) ^ k - (-(h / 2)) ^ k) / (k.factorial : ℝ) * ∑' j : ℕ, gu (p + k) (mid h j)|
      ≤ c * h ^ m := by
  obtain ⟨C, hC0, hC⟩ := remJ_bound p m
  refine ⟨2 * C, by positivity, fun h h0 h1 => ?_⟩
  -- partial sum identity
  have hE : ∀ N : ℕ, ∑ j ∈ Finset.range N, remJ p (m + 1) h j
      = gu p ((N : ℝ) * h) - gu p 0 - ∑ k ∈ Finset.range (m + 1),
        ((h / 2) ^ k - (-(h / 2)) ^ k) / (k.factorial : ℝ) *
          ∑ j ∈ Finset.range N, gu (p + k) (mid h j) := by
    intro N
    unfold remJ
    rw [Finset.sum_sub_distrib]
    have htel := Finset.sum_range_sub (fun j : ℕ => gu p ((j : ℝ) * h)) N
    simp only [Nat.cast_zero, zero_mul] at htel
    rw [htel, Finset.sum_comm]
    simp only [Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hbd : ∀ N : ℕ, |∑ j ∈ Finset.range N, remJ p (m + 1) h j| ≤ 2 * C * h ^ m := by
    intro N
    calc |∑ j ∈ Finset.range N, remJ p (m + 1) h j|
        ≤ ∑ j ∈ Finset.range N, |remJ p (m + 1) h j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range N, C * h ^ m * (h / (1 + (j : ℝ) * h) ^ 2) :=
          Finset.sum_le_sum fun j _ => hC h h0 j
      _ = C * h ^ m * ∑ j ∈ Finset.range N, h / (1 + (j : ℝ) * h) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ C * h ^ m * 2 := mul_le_mul_of_nonneg_left (by linarith [sumW_le h0 N]) (by positivity)
      _ = 2 * C * h ^ m := by ring
  have hlim : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, remJ p (m + 1) h j) atTop
      (𝓝 (-gu p 0 - ∑ k ∈ Finset.range (m + 1),
        ((h / 2) ^ k - (-(h / 2)) ^ k) / (k.factorial : ℝ) * ∑' j : ℕ, gu (p + k) (mid h j))) := by
    simp_rw [hE]
    have h1' := gu_tendsto_zero p h0
    have h2 : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (m + 1),
        ((h / 2) ^ k - (-(h / 2)) ^ k) / (k.factorial : ℝ) *
          ∑ j ∈ Finset.range N, gu (p + k) (mid h j)) atTop
        (𝓝 (∑ k ∈ Finset.range (m + 1),
        ((h / 2) ^ k - (-(h / 2)) ^ k) / (k.factorial : ℝ) * ∑' j : ℕ, gu (p + k) (mid h j))) := by
      refine tendsto_finsetSum _ fun k _ => Tendsto.const_mul _ ?_
      exact (summable_gu_mid (p + k) h0 h1).hasSum.tendsto_sum_nat
    simpa [sub_eq_add_neg] using (h1'.sub_const (gu p 0)).sub h2
  exact le_of_tendsto' hlim.abs hbd

end Lightlike.Geometry.HeatTraceExpansion

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_062.gu_tendsto_zero := _root_.Lightlike.Geometry.HeatTraceExpansion.gu_tendsto_zero
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_062.level := _root_.Lightlike.Geometry.HeatTraceExpansion.level
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_062.remJ := _root_.Lightlike.Geometry.HeatTraceExpansion.remJ
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_062.remJ_bound := _root_.Lightlike.Geometry.HeatTraceExpansion.remJ_bound
