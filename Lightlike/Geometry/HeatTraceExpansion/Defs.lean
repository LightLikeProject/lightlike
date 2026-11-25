import Mathlib

/-!
# Heat traces and their small-time expansions

For a Laplace-type operator with discrete spectrum, the heat trace is `Z(t) = ∑ᵢ mᵢ e^{-t λᵢ}`.
Its small-time asymptotic expansion on a compact `d`-manifold has the Seeley–DeWitt form
`Z(t) ≃ ∑ₖ aₖ t^{k - d/2}` (`vassilevich-2003`, the heat kernel expansion; `bgv-1992`).
This file fixes the objects the row G1-062 talks about:

* `Lightlike.Geometry.HeatTraceExpansion.heatTrace`: the heat trace of a weighted spectrum.
* `Lightlike.Geometry.HeatTraceExpansion.HasHeatExpansion`: `Z` has the expansion with the coefficients `a`
  up to order `K` in dimension `d`.

## Main results

* `Lightlike.Geometry.HeatTraceExpansion.HasHeatExpansion.coeff_unique`: the coefficients are unique, so "the
  `t⁰` term vanishes" is a meaningful statement.
-/

open Filter Topology

namespace Lightlike.Geometry.HeatTraceExpansion

/-- The heat trace `∑ᵢ mᵢ e^{-t λᵢ}` of a spectrum `ev` with multiplicities `mult`. -/
noncomputable def heatTrace {ι : Type*} (ev : ι → ℝ) (mult : ι → ℕ) (t : ℝ) : ℝ :=
  ∑' i, (mult i : ℝ) * Real.exp (-t * ev i)

/-- `Z` has the small-time expansion `Z(t) = ∑_{k<K} a k · t^{k - d/2} + O(t^{K - d/2})`
as `t → 0⁺`, for a `d`-dimensional manifold (`d` is the dimension). -/
def HasHeatExpansion (Z : ℝ → ℝ) (d : ℕ) (a : ℕ → ℝ) (K : ℕ) : Prop :=
  (fun t => Z t - ∑ k ∈ Finset.range K, a k * t ^ ((k : ℝ) - d / 2)) =O[𝓝[>] 0]
    fun t => t ^ ((K : ℝ) - d / 2)

/-- A finite combination `∑_{k<K} c k · t^{k - d/2}` that is `O(t^{K - d/2})` as `t → 0⁺` has
all coefficients zero. -/
theorem coeff_eq_zero_of_isBigO (c : ℕ → ℝ) (d K : ℕ)
    (h : (fun t : ℝ => ∑ k ∈ Finset.range K, c k * t ^ ((k : ℝ) - d / 2)) =O[𝓝[>] 0]
      fun t => t ^ ((K : ℝ) - d / 2)) : ∀ k < K, c k = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hjK
  set g : ℝ → ℝ := fun t => ∑ k ∈ Finset.Ico j K, c k * t ^ (k - j) with hg
  -- the sum equals `t^{j - d/2} * g t`
  have hsum : ∀ t : ℝ, 0 < t →
      ∑ k ∈ Finset.range K, c k * t ^ ((k : ℝ) - d / 2) = t ^ ((j : ℝ) - d / 2) * g t := by
    intro t ht
    have h1 : ∑ k ∈ Finset.range K, c k * t ^ ((k : ℝ) - d / 2)
        = ∑ k ∈ Finset.Ico j K, c k * t ^ ((k : ℝ) - d / 2) := by
      symm
      apply Finset.sum_subset
      · intro k hk
        simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
        omega
      · intro k hk hk'
        simp only [Finset.mem_Ico, Finset.mem_range, not_and] at hk hk'
        have : c k = 0 := ih k (by omega) (by omega)
        simp [this]
    rw [h1, hg, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have : (k : ℝ) - d / 2 = ((j : ℝ) - d / 2) + ((k - j : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk.1]; ring
    rw [this, Real.rpow_add ht, Real.rpow_natCast]
    ring
  have hK : ∀ t : ℝ, 0 < t →
      t ^ ((K : ℝ) - d / 2) = t ^ ((j : ℝ) - d / 2) * t ^ (K - j) := by
    intro t ht
    have : (K : ℝ) - d / 2 = ((j : ℝ) - d / 2) + ((K - j : ℕ) : ℝ) := by
      rw [Nat.cast_sub hjK.le]; ring
    rw [this, Real.rpow_add ht, Real.rpow_natCast]
  obtain ⟨C, hC⟩ := h.bound
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hbd : ∀ᶠ t : ℝ in 𝓝[>] 0, |g t| ≤ C * t ^ (K - j) := by
    filter_upwards [hC, hpos] with t ht ht0
    rw [hsum t ht0, hK t ht0, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos ht0 _), abs_of_pos (pow_pos ht0 _)] at ht
    have hp := Real.rpow_pos_of_pos ht0 ((j : ℝ) - d / 2)
    nlinarith [abs_nonneg (g t), hp]
  have hcont : Continuous g := by
    rw [hg]; fun_prop
  have hg0 : g 0 = c j := by
    rw [hg]
    simp only
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      simp only [Finset.mem_Ico] at hk
      have : k - j ≠ 0 := by omega
      simp [this]
    · intro hj
      exact absurd (Finset.mem_Ico.mpr ⟨le_refl _, hjK⟩) hj
  have hlim1 : Tendsto g (𝓝[>] 0) (𝓝 (c j)) := by
    rw [← hg0]
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hKj : K - j ≠ 0 := by omega
  have hlim2 : Tendsto (fun t : ℝ => C * t ^ (K - j)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => C * t ^ (K - j)) (𝓝 0) (𝓝 (C * 0 ^ (K - j))) :=
      ((continuous_const.mul (continuous_id.pow _)).tendsto 0)
    rw [zero_pow hKj, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim3 : Tendsto (fun t => |g t|) (𝓝[>] 0) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun t => abs_nonneg _) hbd hlim2
  have hlim4 : Tendsto (fun t => |g t|) (𝓝[>] 0) (𝓝 |c j|) := hlim1.abs
  have := tendsto_nhds_unique hlim4 hlim3
  exact abs_eq_zero.mp this

/-- **Uniqueness of the heat expansion coefficients**: two expansions of the same function in the
same dimension and to the same order have the same coefficients. -/
theorem HasHeatExpansion.coeff_unique {Z : ℝ → ℝ} {d K : ℕ} {a b : ℕ → ℝ}
    (ha : HasHeatExpansion Z d a K) (hb : HasHeatExpansion Z d b K) :
    ∀ k < K, a k = b k := by
  have h := hb.sub ha
  have h' : (fun t : ℝ => ∑ k ∈ Finset.range K, (a k - b k) * t ^ ((k : ℝ) - d / 2)) =O[𝓝[>] 0]
      fun t => t ^ ((K : ℝ) - d / 2) := by
    refine h.congr_left ?_
    intro t
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  intro k hk
  have := coeff_eq_zero_of_isBigO (fun k => a k - b k) d K h' k hk
  linarith

end Lightlike.Geometry.HeatTraceExpansion

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_062.HasHeatExpansion := _root_.Lightlike.Geometry.HeatTraceExpansion.HasHeatExpansion
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_062.HasHeatExpansion.coeff_unique := _root_.Lightlike.Geometry.HeatTraceExpansion.HasHeatExpansion.coeff_unique
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_062.coeff_eq_zero_of_isBigO := _root_.Lightlike.Geometry.HeatTraceExpansion.coeff_eq_zero_of_isBigO
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_062.heatTrace := _root_.Lightlike.Geometry.HeatTraceExpansion.heatTrace
