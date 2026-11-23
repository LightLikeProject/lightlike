import Lightlike.Upstream.GeodesicExpansion.Corollaries
import Mathlib

/-!
# Directional limit of the squared Riemannian distance

* `IsRiemMetric.tendsto_chartDist_sq_div`: for `x ∈ U` and a direction `u`,
  `d(x, x + t u)² / t² → g_x(u, u)` as `t → 0`, `t ≠ 0` (chart form).
* `IsRiemMetric.tendsto_riemannianEDist_sq_div`: the same for Mathlib's `riemannianEDist`.
-/

open Matrix Set Filter Topology Metric MeasureTheory Manifold Bundle
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Upstream.GeodesicExpansion

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
  {U : TopologicalSpace.Opens (Fin n → ℝ)}

/-- **Directional limit of the squared distance (chart form).** For `x ∈ U` and `u`,
`d(x, x + t u)² / t² → g_x(u, u)` as `t → 0` with `t ≠ 0`. -/
theorem IsRiemMetric.tendsto_chartDist_sq_div (hg : IsRiemMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (u : Fin n → ℝ) :
    Tendsto (fun t : ℝ => chartDist g U x (x + t • u) ^ 2 / t ^ 2) (𝓝[≠] 0)
      (𝓝 (u ⬝ᵥ (g x *ᵥ u))) := by
  obtain ⟨C, r, hr, h⟩ := hg.chartDist_sq_third (K := {x}) isCompact_singleton
    (Set.singleton_subset_iff.mpr hx)
  have hc : Continuous fun t : ℝ => ‖t • u‖ := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ‖t • u‖ < r :=
    (hc.tendsto 0).eventually (gt_mem_nhds (by simpa using hr))
  have hlim : Tendsto (fun t : ℝ => C * (|t| * ‖u‖ ^ 3)) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => C * (|t| * ‖u‖ ^ 3)) (𝓝 0) (𝓝 (C * (|(0 : ℝ)| * ‖u‖ ^ 3))) :=
      (continuous_const.mul ((continuous_abs).mul continuous_const)).tendsto 0
    simp only [abs_zero, zero_mul, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with t ht ht0
  have ht0' : t ≠ 0 := ht0
  have hb := h x rfl (t • u) ht.le
  have hq : (t • u) ⬝ᵥ (g x *ᵥ (t • u)) = t ^ 2 * (u ⬝ᵥ (g x *ᵥ u)) := by
    simp [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    ring
  rw [hq, norm_smul, Real.norm_eq_abs] at hb
  have htp : 0 < t ^ 2 := by positivity
  rw [Real.norm_eq_abs]
  have : chartDist g U x (x + t • u) ^ 2 / t ^ 2 - u ⬝ᵥ (g x *ᵥ u) =
      (chartDist g U x (x + t • u) ^ 2 - t ^ 2 * (u ⬝ᵥ (g x *ᵥ u))) / t ^ 2 := by
    field_simp
  rw [this, abs_div, abs_of_pos htp, div_le_iff₀ htp]
  calc _ ≤ C * (|t| * ‖u‖) ^ 3 := hb
    _ = C * (|t| * ‖u‖ ^ 3) * t ^ 2 := by
        rw [mul_pow, ← sq_abs t]; ring

open scoped Classical in
/-- **Directional limit of the squared Riemannian distance (Mathlib form).** For `x ∈ U` and a
direction `u`, the squared `riemannianEDist` from `x` to the chart point `x + t u` (when this lies
in `U`) divided by `t²` tends to `g_x(u, u)` as `t → 0`. -/
theorem IsRiemMetric.tendsto_riemannianEDist_sq_div (hg : IsRiemMetric g U) (x : U)
    (u : Fin n → ℝ) :
    letI := hg.riemannianBundle
    Tendsto (fun t : ℝ =>
        if ht : (x : Fin n → ℝ) + t • u ∈ U then
          (riemannianEDist 𝓘(ℝ, Fin n → ℝ) x ⟨_, ht⟩).toReal ^ 2 / t ^ 2 else 0)
      (𝓝[≠] 0) (𝓝 (u ⬝ᵥ (g (x : Fin n → ℝ) *ᵥ u))) := by
  let := hg.riemannianBundle
  have hlim := hg.tendsto_chartDist_sq_div x.2 u
  have hU : ∀ᶠ t in 𝓝 (0 : ℝ), (x : Fin n → ℝ) + t • u ∈ U := by
    have hcont : Continuous fun t : ℝ => (x : Fin n → ℝ) + t • u := by fun_prop
    exact (hcont.continuousAt (x := 0)).eventually_mem
      (s := (U : Set (Fin n → ℝ))) (by simpa using U.isOpen.mem_nhds x.2)
  refine hlim.congr' ?_
  filter_upwards [nhdsWithin_le_nhds hU] with t ht
  simp only [ht, ↓reduceDIte]
  rw [← hg.chartDist_eq_toReal_riemannianEDist x ⟨_, ht⟩]

end Lightlike.Upstream.GeodesicExpansion
