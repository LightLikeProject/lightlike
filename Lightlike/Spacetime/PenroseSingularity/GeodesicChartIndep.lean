import Lightlike.Spacetime.PenroseSingularity.Defs
import Lightlike.Spacetime.ChartTransition

/-!
# Geodesics read in any chart are geodesic curves (G1-012, G1-006 manifold lift)

`IsGeodesicCurveOn` (`Defs.lean`) reads a curve near each `t` in the chart at `γ t`. `isGeodesicCurveOn_of_chart`
shows the notion is chart independent in the useful direction: a curve that is a geodesic of the coordinate metric of
**any** chart `extChartAt x₀` on an open parameter set is a geodesic curve on that set, by the transition map
(`ChartTransition.lean`) and `IsGeodesicOn.map_chartChange`.

Limits: the transition lemma carries the standing hypotheses of `NondegMetric.coordMetric_chart_change`
(`T2Space`, `SecondCountableTopology`, `C²`, a Borel measurable structure), which are the conventions of space-time.
-/

open Bundle Manifold Set Filter Topology Matrix
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **A geodesic in any chart is a geodesic curve.** -/
theorem isGeodesicCurveOn_of_chart (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (x₀ : M) {γ : ℝ → M}
    {O : Set ℝ} (hO : IsOpen O) (hsrc : ∀ s ∈ O, γ s ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    {w : ℝ → Fin n → ℝ}
    (hgeo : Lightlike.Geodesic.IsGeodesicOn (g.coordMetric x₀)
      (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (γ s)) w O) :
    IsGeodesicCurveOn g γ O := by
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
  refine ⟨fun s => Lightlike.jac (ψ₁ ∘ ψ₀.symm) (c s) *ᵥ w s, O', hO'nhds, fun s hs => hs.2, ?_⟩
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · refine (himg.pos s hs).congr_of_eventuallyEq ?_
    filter_upwards [hO'open s hs] with r hr
    exact (heq r hr).symm
  · refine (himg.vel s hs).congr_deriv ?_
    show Lightlike.Geodesic.accel (g.coordMetric x₁) ((ψ₁ ∘ ψ₀.symm) (c s)) _ = Lightlike.Geodesic.accel (g.coordMetric x₁) (ψ₁ (γ s)) _
    rw [Function.comp_apply, heq s hs]

end Lightlike.Penrose
