import Lightlike.Spacetime.EHManifold.Perturbation

/-!
# `g + t h` is a metric for small `t` when `h` has compact support

`NondegMetric.exists_addSmul_nondegenerate`: for a metric `g` (of any signature) on a manifold and a smooth
symmetric bilinear field `h` that vanishes outside a compact set, there is `ε > 0` such that `g + t h` is
nondegenerate at every point for `|t| < ε`. So `g.addSmul h t` is a metric for these `t`.

Supporting lemma for the Einstein–Hilbert variation on a manifold; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology Metric
open scoped Manifold ContDiff Matrix

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- If the matrix of components of `g + t h` at a point of a chart is invertible, the form `g + t h` is
nondegenerate there. -/
lemma NondegMetric.addSmul_nondegenerate_of_det (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (t : ℝ) (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (hdet : (g.coordMetric x₀ y + t • h.coordComp x₀ y).det ≠ 0)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
    (hv : ∀ w, g.g _ v w + t * h.h _ v w = 0) : v = 0 := by
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hmat : LinearMap.BilinForm.toMatrix (coordBasis x₀ hp)
      (g.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) +
        t • h.h ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)).toBilinForm =
      g.coordMetric x₀ y + t • h.coordComp x₀ y := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, Matrix.add_apply, Matrix.smul_apply,
      g.coordMetric_eq x₀ hy, h.coordComp_eq x₀ hy]
    rfl
  have hnd := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (coordBasis x₀ hp)).mpr
    (by rw [hmat]; exact hdet)
  exact hnd.1 v fun w => hv w

/-- The same at a point `x` given as the inverse chart image of `y`. -/
lemma NondegMetric.addSmul_nondegenerate_of_det' (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (t : ℝ) (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (hdet : (g.coordMetric x₀ y + t • h.coordComp x₀ y).det ≠ 0) (x : M)
    (hx : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y = x)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) (hv : ∀ w, g.g x v w + t * h.h x v w = 0) : v = 0 := by
  subst hx
  exact g.addSmul_nondegenerate_of_det h t x₀ hy hdet v hv

/-- A matrix-valued function `G + t H` with continuous entries has nonzero determinant near a point where
`det G ≠ 0`, for small `t`. -/
lemma exists_nhds_det_add_smul_ne_zero (G H : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (y₀ : Fin n → ℝ) (hG : ∀ i j, ContinuousAt (fun y => G y i j) y₀)
    (hH : ∀ i j, ContinuousAt (fun y => H y i j) y₀) (hne : (G y₀).det ≠ 0) :
    ∃ ε > 0, ∃ w ∈ 𝓝 y₀, ∀ t : ℝ, |t| < ε → ∀ y ∈ w, (G y + t • H y).det ≠ 0 := by
  have hentry : ∀ i j, ContinuousAt (fun q : ℝ × (Fin n → ℝ) => G q.2 i j + q.1 * H q.2 i j)
      ((0 : ℝ), y₀) := by
    intro i j
    have h1 : ContinuousAt (fun q : ℝ × (Fin n → ℝ) => G q.2 i j) ((0 : ℝ), y₀) :=
      ContinuousAt.comp (g := fun y => G y i j) (f := Prod.snd) (x := ((0 : ℝ), y₀)) (hG i j)
        continuousAt_snd
    have h2 : ContinuousAt (fun q : ℝ × (Fin n → ℝ) => H q.2 i j) ((0 : ℝ), y₀) :=
      ContinuousAt.comp (g := fun y => H y i j) (f := Prod.snd) (x := ((0 : ℝ), y₀)) (hH i j)
        continuousAt_snd
    exact h1.add (continuousAt_fst.mul h2)
  have hF : ContinuousAt (fun q : ℝ × (Fin n → ℝ) => (G q.2 + q.1 • H q.2).det) ((0 : ℝ), y₀) := by
    simp only [Matrix.det_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine tendsto_finset_sum _ fun σ _ => ?_
    refine ContinuousAt.const_smul (c := Equiv.Perm.sign σ) ?_
    exact tendsto_finset_prod _ fun i _ => hentry (σ i) i
  have hne' : (G ((0 : ℝ), y₀).2 + ((0 : ℝ), y₀).1 • H ((0 : ℝ), y₀).2).det ≠ 0 := by
    show (G y₀ + (0 : ℝ) • H y₀).det ≠ 0
    rw [zero_smul, add_zero]
    exact hne
  have hev := hF.eventually_ne hne'
  obtain ⟨u, w, hu, h0u, hw, hyw, huw⟩ := mem_nhds_prod_iff'.1 hev
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hu 0 h0u
  refine ⟨ε, hε, w, hw.mem_nhds hyw, fun t ht y hy => ?_⟩
  have htu : t ∈ u := hball (by rw [mem_ball_zero_iff, Real.norm_eq_abs]; exact ht)
  exact huw (show (t, y) ∈ u ×ˢ w from ⟨htu, hy⟩)

/-- Near every point, `g + t h` is nondegenerate for small `t`. -/
lemma NondegMetric.exists_nhds_addSmul_nondegenerate (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) :
    ∃ U ∈ 𝓝 x₀, ∃ ε > 0, ∀ t : ℝ, |t| < ε → ∀ x ∈ U, ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      (∀ w, g.g x v w + t * h.h x v w = 0) → v = 0 := by
  have hy₀ : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x₀ ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    mem_extChartAt_target x₀
  have hT : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target ∈ 𝓝 (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x₀) :=
    (isOpen_extChartAt_target x₀).mem_nhds hy₀
  obtain ⟨ε, hε, w, hw, hprop⟩ := exists_nhds_det_add_smul_ne_zero (g.coordMetric x₀)
    (h.coordComp x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x₀)
    (fun i j => (g.coordMetric_smooth x₀ i j).continuousOn.continuousAt hT)
    (fun i j => (h.coordComp_smooth x₀ i j).continuousOn.continuousAt hT)
    (g.coordMetric_isUnit_det x₀ hy₀).ne_zero
  refine ⟨(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source ∩ extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ ⁻¹' w,
    Filter.inter_mem (extChartAt_source_mem_nhds x₀) ((continuousAt_extChartAt x₀).preimage_mem_nhds hw),
    ε, hε, ?_⟩
  intro t ht x hx v hv
  exact g.addSmul_nondegenerate_of_det' h t x₀ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hx.1)
    (hprop t ht _ hx.2) x ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hx.1) v hv

/-- **`g + t h` is nondegenerate for small `t`**, when `h` vanishes outside a compact set. -/
theorem NondegMetric.exists_addSmul_nondegenerate (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) {K : Set M} (hK : IsCompact K)
    (hsupp : ∀ x, x ∉ K → h.h x = 0) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → ∀ (x : M) (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x),
      (∀ w, g.g x v w + t * h.h x v w = 0) → v = 0 := by
  have hKε : ∃ ε > 0, ∀ t : ℝ, |t| < ε → ∀ x ∈ K, ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      (∀ w, g.g x v w + t * h.h x v w = 0) → v = 0 := by
    refine hK.induction_on (p := fun S => ∃ ε > 0, ∀ t : ℝ, |t| < ε → ∀ x ∈ S,
      ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x, (∀ w, g.g x v w + t * h.h x v w = 0) → v = 0)
      ⟨1, one_pos, fun t _ x hx => absurd hx (notMem_empty x)⟩ ?_ ?_ ?_
    · rintro S T hST ⟨ε, hε, hT⟩
      exact ⟨ε, hε, fun t ht x hx => hT t ht x (hST hx)⟩
    · rintro S T ⟨ε₁, hε₁, hS⟩ ⟨ε₂, hε₂, hT⟩
      refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun t ht x hx => ?_⟩
      rcases hx with hx | hx
      · exact hS t (ht.trans_le (min_le_left _ _)) x hx
      · exact hT t (ht.trans_le (min_le_right _ _)) x hx
    · intro x _
      obtain ⟨U, hU, ε, hε, hprop⟩ := g.exists_nhds_addSmul_nondegenerate h x
      exact ⟨U, mem_nhdsWithin_of_mem_nhds hU, ε, hε, hprop⟩
  obtain ⟨ε, hε, hprop⟩ := hKε
  refine ⟨ε, hε, fun t ht x v hv => ?_⟩
  by_cases hx : x ∈ K
  · exact hprop t ht x hx v hv
  · refine g.nondegenerate x v fun w => ?_
    have h1 := hv w
    rw [hsupp x hx] at h1
    simpa using h1

end Lightlike
