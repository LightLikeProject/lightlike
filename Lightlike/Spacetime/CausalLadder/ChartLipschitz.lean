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

/-- Conversely, a Lipschitz curve in the chart at `p`, with values in the target of the chart,
gives a locally Lipschitz curve in `M`: `(extChartAt I p).symm ∘ u`. -/
theorem isLocallyLipschitzOn_chart_symm {u : ℝ → E} {s : Set ℝ} {K : NNReal}
    (hu : LipschitzOnWith K u s) (p : M) (htarget : ∀ t ∈ s, u t ∈ (extChartAt I p).target) :
    IsLocallyLipschitzOn (I := I) ((extChartAt I p).symm ∘ u) s := by
  intro t ht
  set x := (extChartAt I p).symm (u t) with hx
  have hxsrc : x ∈ (extChartAt I p).source := (extChartAt I p).map_target (htarget t ht)
  have hy : u t ∈ ((extChartAt I p).symm ≫ extChartAt I x).source :=
    ⟨htarget t ht, mem_extChartAt_source x⟩
  have hcd := contDiffWithinAt_ext_coord_change (I := I) (n := ∞) x p hy
  obtain ⟨K', V, hV, hKV⟩ := (hcd.of_le (by exact_mod_cast le_top)).exists_lipschitzOnWith
    I.convex_range
  have hrange : ∀ t ∈ s, u t ∈ range I := fun t ht =>
    extChartAt_target_subset_range p (htarget t ht)
  have htm : (extChartAt I p).target ∈ 𝓝[range I] (u t) :=
    extChartAt_target_mem_nhdsWithin_of_mem (htarget t ht)
  have hnhds : 𝓝[(extChartAt I p).target] (u t) = 𝓝[range I] (u t) := by
    rw [← nhdsWithin_inter_of_mem htm, inter_eq_left.2 (extChartAt_target_subset_range p)]
  -- the set where the chart change is defined, as a neighbourhood within the range of `I`
  have hS : {y | (extChartAt I p).symm y ∈ (extChartAt I x).source} ∈ 𝓝[range I] (u t) := by
    rw [← hnhds]
    exact (continuousOn_extChartAt_symm p (u t) (htarget t ht)).preimage_mem_nhdsWithin
      ((isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x))
  have hcont : ContinuousWithinAt u s t := hu.continuousOn.continuousWithinAt ht
  have hev : ∀ᶠ t' in 𝓝[s] t, u t' ∈ V ∩ {y | (extChartAt I p).symm y ∈ (extChartAt I x).source} := by
    have h1 : Tendsto u (𝓝[s] t) (𝓝[range I] (u t)) :=
      tendsto_nhdsWithin_iff.2 ⟨hcont, eventually_nhdsWithin_of_forall hrange⟩
    exact h1 (inter_mem hV hS)
  refine ⟨K' * K, {t' | t' ∈ s ∧ u t' ∈ V ∩ {y | (extChartAt I p).symm y ∈ (extChartAt I x).source}},
    ?_, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin, hev] with t' h1 h2 using ⟨h1, h2⟩
  · intro t' ht'
    exact ht'.2.2
  · have hcomp : LipschitzOnWith (K' * K)
        ((extChartAt I x ∘ (extChartAt I p).symm) ∘ u)
        {t' | t' ∈ s ∧ u t' ∈ V ∩ {y | (extChartAt I p).symm y ∈ (extChartAt I x).source}} :=
      hKV.comp (hu.mono fun t' ht' => ht'.1) fun t' ht' => ht'.2.1
    exact hcomp

end Lightlike.Causal
