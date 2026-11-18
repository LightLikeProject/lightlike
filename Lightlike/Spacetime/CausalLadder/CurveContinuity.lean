import Lightlike.Spacetime.Causal.CausalCurve

/-!
# A locally Lipschitz curve is continuous

`Lightlike.Causal.IsLocallyLipschitzOn` is stated chart by chart. The curve it describes is
continuous as a map into the manifold, since near every parameter it is the inverse chart applied to
a Lipschitz map.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A locally Lipschitz curve is continuous. -/
theorem IsLocallyLipschitzOn.continuousOn {γ : ℝ → M} {s : Set ℝ}
    (h : IsLocallyLipschitzOn (I := I) γ s) : ContinuousOn γ s := by
  intro t ht
  obtain ⟨K, U, hU, hm, hl⟩ := h t ht
  set x := γ t with hx
  have htU : t ∈ U := mem_of_mem_nhdsWithin ht hU
  have hc : ContinuousWithinAt (extChartAt I x ∘ γ) U t := hl.continuousOn.continuousWithinAt htU
  have hsym : ContinuousWithinAt (extChartAt I x).symm (extChartAt I x).target
      (extChartAt I x (γ t)) :=
    (continuousOn_extChartAt_symm x) _ ((extChartAt I x).map_source (hm htU))
  have hmaps : MapsTo (extChartAt I x ∘ γ) U (extChartAt I x).target := fun t' ht' =>
    (extChartAt I x).map_source (hm ht')
  have hcomp : ContinuousWithinAt ((extChartAt I x).symm ∘ (extChartAt I x ∘ γ)) U t :=
    ContinuousWithinAt.comp (f := extChartAt I x ∘ γ) hsym hc hmaps
  have heq : ((extChartAt I x).symm ∘ (extChartAt I x ∘ γ)) =ᶠ[𝓝[U] t] γ := by
    filter_upwards [self_mem_nhdsWithin] with t' ht'
    exact (extChartAt I x).left_inv (hm ht')
  have h2 : ContinuousWithinAt γ U t :=
    hcomp.congr_of_eventuallyEq heq.symm ((extChartAt I x).left_inv (hm htU)).symm
  exact h2.mono_of_mem_nhdsWithin hU

end Lightlike.Causal
