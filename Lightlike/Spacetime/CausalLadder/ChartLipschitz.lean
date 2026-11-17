import Lightlike.Spacetime.Causal.CausalCurve

/-!
# A locally Lipschitz curve is Lipschitz in any one chart on a compact interval

`Lightlike.Causal.IsLocallyLipschitzOn` asks for a Lipschitz image in the chart at each point of the
curve. On a compact interval whose image lies in the source of the chart at `p`, the curve is then
Lipschitz in the chart at `p`: the coordinate changes are `C¹`, hence locally Lipschitz, and a
locally Lipschitz function on a compact set is Lipschitz.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A locally Lipschitz curve, whose image on `s` lies in the source of the chart at `p`, is
locally Lipschitz on `s` in the chart at `p`. -/
theorem locallyLipschitzOn_chart_comp {γ : ℝ → M} {s : Set ℝ} (hγ : IsLocallyLipschitzOn (I := I) γ s)
    (p : M) (hsrc : ∀ t ∈ s, γ t ∈ (extChartAt I p).source) :
    LocallyLipschitzOn s (extChartAt I p ∘ γ) := by
  intro t ht
  obtain ⟨K, U, hU, hmaps, hlip⟩ := hγ t ht
  set x := γ t with hx
  -- the coordinate change is `C¹` within the range of `I`
  have hy : extChartAt I x x ∈ ((extChartAt I x).symm ≫ extChartAt I p).source := by
    refine ⟨(extChartAt I x).map_source (mem_extChartAt_source x), ?_⟩
    simpa [(extChartAt I x).left_inv (mem_extChartAt_source x)] using hsrc t ht
  have hcd := contDiffWithinAt_ext_coord_change (I := I) (n := ∞) p x hy
  obtain ⟨K', V, hV, hKV⟩ := (hcd.of_le (by exact_mod_cast le_top)).exists_lipschitzOnWith
    I.convex_range
  -- the chart image of the curve is continuous at `t` and has values in `range I`
  have hcont : ContinuousWithinAt (extChartAt I x ∘ γ) s t := by
    have := hlip.continuousOn.continuousWithinAt (mem_of_mem_nhdsWithin ht hU)
    exact this.mono_of_mem_nhdsWithin hU
  have hrange : ∀ u, extChartAt I x (γ u) ∈ range I := fun u => by simp
  have hVmem : V ∈ 𝓝[range I] (extChartAt I x x) := hV
  have hev : ∀ᶠ u in 𝓝[s] t, extChartAt I x (γ u) ∈ V := by
    have h1 : Tendsto (extChartAt I x ∘ γ) (𝓝[s] t) (𝓝[range I] (extChartAt I x x)) :=
      tendsto_nhdsWithin_iff.2 ⟨hcont, Eventually.of_forall hrange⟩
    exact h1 hVmem
  refine ⟨K' * K, _, hev.and hU, ?_⟩
  have hcomp : LipschitzOnWith (K' * K)
      ((extChartAt I p ∘ (extChartAt I x).symm) ∘ (extChartAt I x ∘ γ)) {u | extChartAt I x (γ u) ∈ V ∧ u ∈ U} := by
    refine hKV.comp (hlip.mono fun u hu => hu.2) fun u hu => hu.1
  have heq : ∀ u ∈ {u | extChartAt I x (γ u) ∈ V ∧ u ∈ U},
      ((extChartAt I p ∘ (extChartAt I x).symm) ∘ (extChartAt I x ∘ γ)) u =
        (extChartAt I p ∘ γ) u := by
    intro u hu
    simp only [Function.comp_apply]
    rw [(extChartAt I x).left_inv (hmaps hu.2)]
  intro u hu v hv
  have := hcomp hu hv
  rwa [heq u hu, heq v hv] at this

/-- On a compact interval, the chart image at `p` of a locally Lipschitz curve in the source of the
chart is Lipschitz. -/
theorem exists_lipschitzOnWith_chart_comp {γ : ℝ → M} {a b : ℝ}
    (hγ : IsLocallyLipschitzOn (I := I) γ (Icc a b)) (p : M)
    (hsrc : ∀ t ∈ Icc a b, γ t ∈ (extChartAt I p).source) :
    ∃ K, LipschitzOnWith K (extChartAt I p ∘ γ) (Icc a b) :=
  (locallyLipschitzOn_chart_comp hγ p hsrc).exists_lipschitzOnWith_of_compact isCompact_Icc

end Lightlike.Causal
