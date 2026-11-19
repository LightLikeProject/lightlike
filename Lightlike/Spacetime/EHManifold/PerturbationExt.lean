import Lightlike.Spacetime.EHManifold.Perturbation

/-!
# The chart components of a compactly supported perturbation, extended by zero

For a smooth symmetric bilinear field `h` that vanishes outside a compact set `K` inside the domain of the
chart at `x₀`, `SymBilinField.coordCompExt h x₀` is the matrix of components of `h` on the chart target and
`0` elsewhere. It is smooth on all of `ℝⁿ` (`contDiff_coordCompExt`), symmetric, and supported in the chart
image of `K` (`tsupport_coordCompExt_subset`).

Supporting definitions for the Einstein–Hilbert variation on a manifold; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff Matrix

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

open Classical in
/-- The components of `h` in the chart at `x₀`, extended by zero outside the chart target. -/
def SymBilinField.coordCompExt (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M)
    (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  if y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target then h.coordComp x₀ y else 0

lemma SymBilinField.coordCompExt_of_mem (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    h.coordCompExt x₀ y = h.coordComp x₀ y := by
  simp only [SymBilinField.coordCompExt, if_pos hy]

lemma SymBilinField.coordCompExt_symm (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M)
    (y : Fin n → ℝ) (i j : Fin n) : h.coordCompExt x₀ y i j = h.coordCompExt x₀ y j i := by
  by_cases hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target
  · rw [h.coordCompExt_of_mem x₀ hy]
    exact h.coordComp_symm x₀ y i j
  · simp only [SymBilinField.coordCompExt, if_neg hy, Matrix.zero_apply]

variable (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) {K : Set M}

/-- Outside the chart image of `K` the extended components vanish. -/
lemma SymBilinField.coordCompExt_eq_zero (hsupp : ∀ x, x ∉ K → h.h x = 0) {y : Fin n → ℝ}
    (hy : y ∉ extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K) : h.coordCompExt x₀ y = 0 := by
  by_cases hyt : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target
  · rw [h.coordCompExt_of_mem x₀ hyt]
    have hp : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∉ K := fun hK =>
      hy ⟨_, hK, (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv hyt⟩
    ext i j
    simp only [SymBilinField.coordComp, hsupp _ hp, ContinuousLinearMap.zero_apply, Matrix.zero_apply]
  · simp only [SymBilinField.coordCompExt, if_neg hyt]

/-- The extended components are smooth on all of `ℝⁿ`. -/
theorem SymBilinField.contDiff_coordCompExt (hK : IsCompact K)
    (hK0 : K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (hsupp : ∀ x, x ∉ K → h.h x = 0)
    (i j : Fin n) : ContDiff ℝ ∞ (fun y => h.coordCompExt x₀ y i j) := by
  have hTc : IsClosed (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K) :=
    (hK.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hK0)).isClosed
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target
  · have hT : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target ∈ 𝓝 y := (isOpen_extChartAt_target x₀).mem_nhds hy
    refine ((h.coordComp_smooth x₀ i j).contDiffAt hT).congr_of_eventuallyEq ?_
    filter_upwards [hT] with z hz
    rw [h.coordCompExt_of_mem x₀ hz]
  · have hyK : y ∉ extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K := fun hyK => hy (by
      obtain ⟨p, hp, rfl⟩ := hyK
      exact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (hK0 hp))
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hTc.isOpen_compl.mem_nhds hyK] with z hz
    rw [h.coordCompExt_eq_zero x₀ hsupp hz, Matrix.zero_apply]

/-- The extended components are supported in the chart image of `K`. -/
theorem SymBilinField.tsupport_coordCompExt_subset (hK : IsCompact K)
    (hK0 : K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (hsupp : ∀ x, x ∉ K → h.h x = 0)
    (i j : Fin n) :
    tsupport (fun y => h.coordCompExt x₀ y i j) ⊆ extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K := by
  have hTc : IsClosed (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' K) :=
    (hK.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hK0)).isClosed
  refine closure_minimal (fun y hy => ?_) hTc
  by_contra hyK
  exact hy (by
    show h.coordCompExt x₀ y i j = 0
    rw [h.coordCompExt_eq_zero x₀ hsupp hyK, Matrix.zero_apply])

end Lightlike
