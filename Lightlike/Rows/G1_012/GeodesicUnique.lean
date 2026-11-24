import Lightlike.Rows.G1_012.Defs

/-!
# Uniqueness of geodesic curves on a manifold (G1-012, G1-006 manifold lift)

* `IsGeodesicCurveOn.eventuallyEq`: two geodesic curves through the same point with the same chart velocity agree near
  that parameter (local uniqueness of the chart ODE, `IsGeodesicOn.eventuallyEq`).
* `IsGeodesicCurveOn.eqOn`: on an open interval, with `[T2Space M]`, two geodesic curves that agree to first order at
  one parameter agree on the whole interval (open-closed argument).
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)

/-- **Local uniqueness.** -/
theorem IsGeodesicCurveOn.eventuallyEq {γ γ' : ℝ → M} {J : Set ℝ} {t₀ : ℝ} (hJ : J ∈ 𝓝 t₀)
    (h : IsGeodesicCurveOn g γ J) (h' : IsGeodesicCurveOn g γ' J) (h0 : γ t₀ = γ' t₀)
    (h1 : deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t₀) (γ s)) t₀ =
      deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t₀) (γ' s)) t₀) :
    γ =ᶠ[𝓝 t₀] γ' := by
  have ht₀ : t₀ ∈ J := mem_of_mem_nhds hJ
  obtain ⟨w, O, hO, hsrc, hg⟩ := h t₀ ht₀
  obtain ⟨w', O', hO', hsrc', hg'⟩ := h' t₀ ht₀
  simp only [← h0] at hsrc' hg'
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t₀) with hψ
  have hw : w t₀ = w' t₀ := by
    have e1 := (hg.pos t₀ (mem_of_mem_nhds hO)).deriv
    have e2 := (hg'.pos t₀ (mem_of_mem_nhds hO')).deriv
    rw [← e1, ← e2]
    exact h1
  have hU := g.toNondegMetric.isCoordMetric_coordMetric (γ t₀)
  have hx : ψ (γ t₀) ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t₀)).target :=
    ψ.map_source (mem_extChartAt_source (γ t₀))
  have key := hg.eventuallyEq hU hO hO' hg' hx (congrArg ψ h0) hw
  filter_upwards [key, hO, hO'] with s hs hsO hsO'
  have e : ψ (γ s) = ψ (γ' s) := congrArg Prod.fst hs
  have a1 : γ s = ψ.symm (ψ (γ s)) := (ψ.left_inv (hsrc s hsO)).symm
  have a2 : γ' s = ψ.symm (ψ (γ' s)) := (ψ.left_inv (hsrc' s hsO')).symm
  rw [a1, a2, e]

/-- A geodesic curve is continuous on its (open) parameter set. -/
theorem IsGeodesicCurveOn.continuousAt {γ : ℝ → M} {J : Set ℝ} (h : IsGeodesicCurveOn g γ J)
    {t : ℝ} (ht : t ∈ J) : ContinuousAt γ t := by
  obtain ⟨w, O, hO, hsrc, hg⟩ := h t ht
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) with hψ
  have hcs : ContinuousAt (fun s => ψ (γ s)) t := (hg.pos t (mem_of_mem_nhds hO)).continuousAt
  have hsymm : ContinuousAt ψ.symm (ψ (γ t)) :=
    (continuousOn_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) (γ t)).continuousAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) (γ t)).mem_nhds
        (ψ.map_source (mem_extChartAt_source (γ t))))
  have := ContinuousAt.comp (f := fun s => ψ (γ s)) (x := t) hsymm hcs
  refine this.congr ?_
  filter_upwards [hO] with r hr
  exact ψ.left_inv (hsrc r hr)

/-- **Global uniqueness of geodesic curves** on an open interval, in a Hausdorff manifold: two geodesic curves that
agree to first order (position and chart velocity at `γ t₀`) at one parameter `t₀` agree on the whole interval. -/
theorem IsGeodesicCurveOn.eqOn [T2Space M] {γ γ' : ℝ → M} {J : Set ℝ} (hJo : IsOpen J) (hJc : IsPreconnected J)
    (h : IsGeodesicCurveOn g γ J) (h' : IsGeodesicCurveOn g γ' J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (h0 : γ t₀ = γ' t₀)
    (h1 : deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t₀) (γ s)) t₀ =
      deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t₀) (γ' s)) t₀) :
    EqOn γ γ' J := by
  set u : Set ℝ := {t | γ =ᶠ[𝓝 t] γ'} with hu
  have huo : IsOpen u := isOpen_iff_mem_nhds.2 fun t ht => by
    filter_upwards [ht.eventually_nhds] with s hs using hs
  have hsub : J ⊆ u := by
    refine hJc.subset_of_closure_inter_subset huo ⟨t₀, ht₀, ?_⟩ ?_
    · exact IsGeodesicCurveOn.eventuallyEq g (hJo.mem_nhds ht₀) h h' h0 h1
    · rintro t ⟨hcl, htJ⟩
      have hl : (𝓝[u] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
      have hJt : J ∈ 𝓝 t := hJo.mem_nhds htJ
      have hueq : ∀ᶠ s in 𝓝[u] t, γ s = γ' s :=
        eventually_mem_nhdsWithin.mono fun s hs => hs.self_of_nhds
      have hpos : γ t = γ' t :=
        tendsto_nhds_unique_of_eventuallyEq
          ((IsGeodesicCurveOn.continuousAt g h htJ).tendsto.mono_left nhdsWithin_le_nhds)
          ((IsGeodesicCurveOn.continuousAt g h' htJ).tendsto.mono_left nhdsWithin_le_nhds) hueq
      obtain ⟨w, O, hO, hsrc, hg⟩ := h t htJ
      obtain ⟨w', O', hO', hsrc', hg'⟩ := h' t htJ
      simp only [← hpos] at hsrc' hg'
      set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) with hψ
      have hwc : ContinuousAt w t := (hg.vel t (mem_of_mem_nhds hO)).continuousAt
      have hwc' : ContinuousAt w' t := (hg'.vel t (mem_of_mem_nhds hO')).continuousAt
      have hweq : ∀ᶠ s in 𝓝[u] t, w s = w' s := by
        have hOO : ∀ᶠ s in 𝓝[u] t, s ∈ O ∧ s ∈ O' :=
          Filter.Eventually.and (nhdsWithin_le_nhds hO) (nhdsWithin_le_nhds hO')
        filter_upwards [hOO, eventually_mem_nhdsWithin] with s hs hsu
        have hev : (fun r => ψ (γ r)) =ᶠ[𝓝 s] fun r => ψ (γ' r) := by
          filter_upwards [hsu] with r hr using by rw [hr]
        have e1 := (hg.pos s hs.1).deriv
        have e2 := (hg'.pos s hs.2).deriv
        rw [← e1, ← e2]
        exact hev.deriv_eq
      have hwt : w t = w' t :=
        tendsto_nhds_unique_of_eventuallyEq (hwc.tendsto.mono_left nhdsWithin_le_nhds)
          (hwc'.tendsto.mono_left nhdsWithin_le_nhds) hweq
      refine IsGeodesicCurveOn.eventuallyEq g hJt h h' hpos ?_
      have e1 := (hg.pos t (mem_of_mem_nhds hO)).deriv
      have e2 := (hg'.pos t (mem_of_mem_nhds hO')).deriv
      rw [e1, e2]
      exact hwt
  exact fun t ht => (hsub ht).self_of_nhds

end Lightlike.Penrose
