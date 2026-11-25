import Lightlike.Rows.G1_012.GeodesicChartIndep

/-!
# A geodesic curve read in any chart is a chart geodesic (G1-012)

`geodesicOn_chart_of_curve` is the converse of `isGeodesicCurveOn_of_chart`: a geodesic curve on an
open set which stays in the source of the chart at `x` is a geodesic of the coordinate metric of
that chart, with the velocity the derivative of the chart expression.
-/

open Bundle Manifold Set Filter Topology Matrix
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **A geodesic curve is a geodesic in every chart containing it.** -/
theorem geodesicOn_chart_of_curve (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (x : M) {γ : ℝ → M}
    {O : Set ℝ} (hO : IsOpen O) (hsrc : ∀ s ∈ O, γ s ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source)
    (h : IsGeodesicCurveOn g γ O) :
    ∃ w : ℝ → Fin n → ℝ, Lightlike.Geodesic.IsGeodesicOn (g.coordMetric x)
      (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ s)) w O := by
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hψ
  set u : ℝ → Fin n → ℝ := fun s => ψ (γ s) with hu
  have hg₁ := g.toNondegMetric.isCoordMetric_coordMetric x
  -- the local statement at each time
  have hloc : ∀ t ∈ O, ∃ (w : ℝ → Fin n → ℝ) (N : Set ℝ), N ∈ 𝓝 t ∧ N ⊆ O ∧
      Lightlike.Geodesic.IsGeodesicOn (g.coordMetric x) u w N := by
    intro t ht
    obtain ⟨w₀, O₀, hO₀, hsrc₀, hgeo₀⟩ := h t ht
    set x₀ := γ t with hx₀
    set ψ₀ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hψ₀
    set c : ℝ → Fin n → ℝ := fun s => ψ₀ (γ s) with hc
    -- an open neighbourhood on which everything is defined
    obtain ⟨N, hNO, hNo, htN⟩ : ∃ N : Set ℝ, N ⊆ O₀ ∩ O ∧ IsOpen N ∧ t ∈ N := by
      obtain ⟨N, hN, hNo, htN⟩ := mem_nhds_iff.1 (Filter.inter_mem hO₀ (hO.mem_nhds ht))
      exact ⟨N, hN, hNo, htN⟩
    have hV : ∀ s ∈ N, c s ∈ transitionDom (n := n) x₀ x := fun s hs =>
      ⟨ψ₀.map_source (hsrc₀ s (hNO hs).1), by
        have e : ψ₀.symm (c s) = γ s := ψ₀.left_inv (hsrc₀ s (hNO hs).1)
        show ψ₀.symm (c s) ∈ ψ.source
        rw [e]; exact hsrc s (hNO hs).2⟩
    have hφ := isChartChange_transition g.toNondegMetric x₀ x
    have hgeoN : Lightlike.Geodesic.IsGeodesicOn
        (Lightlike.pullback (g.coordMetric x) (ψ ∘ ψ₀.symm)) c w₀ N :=
      (show Lightlike.Geodesic.IsGeodesicOn (g.coordMetric x₀) c w₀ N from
        ⟨fun s hs => hgeo₀.pos s (hNO hs).1, fun s hs => hgeo₀.vel s (hNO hs).1⟩).congr_metric
          (isOpen_transitionDom x₀ x) (fun y hy => (pullback_transition g.toNondegMetric x₀ x hy).symm)
          hV
    have himg := hgeoN.map_chartChange hg₁ hφ (fun s hs => hV s hs)
    have heq : ∀ s ∈ N, ψ (ψ₀.symm (c s)) = u s := fun s hs => by
      simp only [hu]; rw [ψ₀.left_inv (hsrc₀ s (hNO hs).1)]
    refine ⟨fun s => Lightlike.jac (ψ ∘ ψ₀.symm) (c s) *ᵥ w₀ s, N, hNo.mem_nhds htN,
      fun s hs => (hNO hs).2, ?_, ?_⟩
    · intro s hs
      refine (himg.pos s hs).congr_of_eventuallyEq ?_
      filter_upwards [hNo.mem_nhds hs] with r hr
      exact (heq r hr).symm
    · intro s hs
      refine (himg.vel s hs).congr_deriv ?_
      show Lightlike.Geodesic.accel (g.coordMetric x) ((ψ ∘ ψ₀.symm) (c s)) _ =
        Lightlike.Geodesic.accel (g.coordMetric x) (u s) _
      rw [Function.comp_apply, heq s hs]
  -- global velocity: the derivative of the chart expression
  refine ⟨fun s => deriv u s, ?_, ?_⟩
  · intro t ht
    obtain ⟨w, N, hN, -, hgeo⟩ := hloc t ht
    exact (hgeo.pos t (mem_of_mem_nhds hN)).differentiableAt.hasDerivAt.congr_deriv rfl
  · intro t ht
    obtain ⟨w, N, hN, -, hgeo⟩ := hloc t ht
    have hdw : deriv u =ᶠ[𝓝 t] w := by
      have : ∀ᶠ s in 𝓝 t, s ∈ interior N := by
        exact interior_mem_nhds.2 hN
      filter_upwards [this] with s hs
      exact (hgeo.pos s (interior_subset hs)).deriv
    refine ((hgeo.vel t (mem_of_mem_nhds hN)).congr_of_eventuallyEq hdw).congr_deriv ?_
    rw [(hgeo.pos t (mem_of_mem_nhds hN)).deriv]

end Lightlike.Penrose
