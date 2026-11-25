import Lightlike.Spacetime.PenroseSingularity.GeodesicChartIndep

/-!
# Null geodesics read in any chart (G1-012)

`isNullGeodesicOn_of_chart`: the null version of `isGeodesicCurveOn_of_chart`.
-/

open Bundle Manifold Set Filter Topology Matrix
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- The bilinear contraction is the dot product with the matrix-vector product. -/
theorem bil_eq_dotProduct (G : Matrix (Fin n) (Fin n) ℝ) (u w : Fin n → ℝ) :
    bil G u w = u ⬝ᵥ (G *ᵥ w) := by
  simp only [bil, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The pulled-back metric evaluated on a vector is the metric on the image vector. -/
theorem bil_pullback (G : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (φ : (Fin n → ℝ) → (Fin n → ℝ))
    (y v : Fin n → ℝ) :
    bil (pullback G φ y) v v = bil (G (φ y)) (jac φ y *ᵥ v) (jac φ y *ᵥ v) := by
  rw [bil_eq_dotProduct, bil_eq_dotProduct, pullback_eq_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- **A null geodesic in any chart is a null geodesic curve.** The chart geodesic `γ` of the
coordinate metric of the chart at `x₀`, with velocity `w`, nonzero and null at every `s ∈ O`, is a
null geodesic on `O` in the sense of `IsNullGeodesicOn`. -/
theorem isNullGeodesicOn_of_chart (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (x₀ : M) {γ : ℝ → M}
    {O : Set ℝ} (hO : IsOpen O) (hsrc : ∀ s ∈ O, γ s ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    {w : ℝ → Fin n → ℝ} (hw0 : ∀ s ∈ O, w s ≠ 0)
    (hnull : ∀ s ∈ O, bil (g.coordMetric x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (γ s))) (w s) (w s) = 0)
    (hgeo : Lightlike.Geodesic.IsGeodesicOn (g.coordMetric x₀)
      (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (γ s)) w O) :
    IsNullGeodesicOn g γ O := by
  intro t ht
  set ψ₀ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hψ₀
  set x₁ := γ t with hx₁
  set ψ₁ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ with hψ₁
  set c : ℝ → Fin n → ℝ := fun s => ψ₀ (γ s) with hc
  -- the curve is continuous on `O`
  have hcont : ∀ s ∈ O, ContinuousAt γ s := by
    intro s hs
    have hcs : ContinuousAt c s := (hgeo.pos s hs).continuousAt
    have hsymm : ContinuousAt ψ₀.symm (c s) :=
      (continuousOn_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) x₀).continuousAt
        ((isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x₀).mem_nhds (ψ₀.map_source (hsrc s hs)))
    have := hsymm.comp hcs
    refine this.congr ?_
    filter_upwards [hO.mem_nhds hs] with r hr
    exact ψ₀.left_inv (hsrc r hr)
  -- the neighbourhood on which the curve stays in the chart at `γ t`
  set O' : Set ℝ := O ∩ γ ⁻¹' ψ₁.source with hO'
  have hO'nhds : O' ∈ 𝓝 t :=
    Filter.inter_mem (hO.mem_nhds ht)
      ((hcont t ht).preimage_mem_nhds ((isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) x₁).mem_nhds
        (mem_extChartAt_source x₁)))
  have hO'open : ∀ s ∈ O', O' ∈ 𝓝 s := by
    intro s hs
    exact Filter.inter_mem (hO.mem_nhds hs.1)
      ((hcont s hs.1).preimage_mem_nhds ((isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) x₁).mem_nhds hs.2))
  have hV : ∀ s ∈ O', c s ∈ transitionDom (n := n) x₀ x₁ := fun s hs =>
    ⟨ψ₀.map_source (hsrc s hs.1), by
      have e : ψ₀.symm (c s) = γ s := ψ₀.left_inv (hsrc s hs.1)
      show ψ₀.symm (c s) ∈ ψ₁.source
      rw [e]; exact hs.2⟩
  have hg₁ := g.toNondegMetric.isCoordMetric_coordMetric x₁
  have hφ := isChartChange_transition g.toNondegMetric x₀ x₁
  have hgeo' : Lightlike.Geodesic.IsGeodesicOn
      (Lightlike.pullback (g.coordMetric x₁) (ψ₁ ∘ ψ₀.symm)) c w O' :=
    (show Lightlike.Geodesic.IsGeodesicOn (g.coordMetric x₀) c w O' from
      ⟨fun s hs => hgeo.pos s hs.1, fun s hs => hgeo.vel s hs.1⟩).congr_metric
        (isOpen_transitionDom x₀ x₁) (fun y hy => (pullback_transition g.toNondegMetric x₀ x₁ hy).symm)
        hV
  have himg := hgeo'.map_chartChange hg₁ hφ (fun s hs => hV s hs)
  have heq : ∀ s ∈ O', ψ₁ (ψ₀.symm (c s)) = ψ₁ (γ s) := fun s hs => by
    rw [ψ₀.left_inv (hsrc s hs.1)]
  refine ⟨fun s => Lightlike.jac (ψ₁ ∘ ψ₀.symm) (c s) *ᵥ w s, O', hO'nhds, fun s hs => hs.2, ?_, ?_, ?_⟩
  rotate_left
  · have hOt : t ∈ O' := ⟨ht, mem_extChartAt_source x₁⟩
    intro h0
    exact hw0 t ht (Matrix.eq_zero_of_mulVec_eq_zero (hφ.isUnit_det _ (hV t hOt)).ne_zero h0)
  · have hOt : t ∈ O' := ⟨ht, mem_extChartAt_source x₁⟩
    show bil (g.coordMetric (γ t) (ψ₁ (γ t))) (Lightlike.jac (ψ₁ ∘ ψ₀.symm) (c t) *ᵥ w t)
      (Lightlike.jac (ψ₁ ∘ ψ₀.symm) (c t) *ᵥ w t) = 0
    have e1 : bil (g.coordMetric (γ t) (ψ₁ (γ t))) (Lightlike.jac (ψ₁ ∘ ψ₀.symm) (c t) *ᵥ w t)
        (Lightlike.jac (ψ₁ ∘ ψ₀.symm) (c t) *ᵥ w t) =
        bil (Lightlike.pullback (g.coordMetric (γ t)) (ψ₁ ∘ ψ₀.symm) (c t)) (w t) (w t) := by
      rw [bil_pullback, Function.comp_apply, heq t hOt]
    rw [e1, pullback_transition g.toNondegMetric x₀ x₁ (hV t hOt)]
    exact hnull t ht
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · refine (himg.pos s hs).congr_of_eventuallyEq ?_
    filter_upwards [hO'open s hs] with r hr
    exact (heq r hr).symm
  · refine (himg.vel s hs).congr_deriv ?_
    show Lightlike.Geodesic.accel (g.coordMetric x₁) ((ψ₁ ∘ ψ₀.symm) (c s)) _ = Lightlike.Geodesic.accel (g.coordMetric x₁) (ψ₁ (γ s)) _
    rw [Function.comp_apply, heq s hs]

end Lightlike.Penrose
