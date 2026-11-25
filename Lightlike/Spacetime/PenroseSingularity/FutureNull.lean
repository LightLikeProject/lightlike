import Lightlike.Spacetime.PenroseSingularity.LocalGenerators
import Lightlike.Spacetime.PenroseSingularity.NullGeodGlue
import Lightlike.Spacetime.PenroseSingularity.NullVariation

/-!
# The future direction of a null geodesic is constant (G1-012)

A null geodesic on an interval `[a, b]` whose velocity points to the future of the time orientation
at one parameter does so at every parameter (`isFutureNullGeodesicOn_of_forall`): the function
`g(γ', X)` is continuous and does not vanish (a nonzero null vector is not orthogonal to a timelike
one).
-/

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}

/-- **The future direction of a null geodesic is constant.** -/
theorem isFutureNullGeodesicOn_of_one (T : Causal.TimeOrientation g) {γ : ℝ → M} {a b : ℝ}
    (hab : a < b) (hnull : IsNullGeodesicOn g γ (Icc a b))
    (hs₀ : ∃ s₀ ∈ Icc a b, g.g (γ s₀) (Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc a b) s₀)
      (T.X (γ s₀)) < 0) : IsFutureNullGeodesicOn T γ (Icc a b) := by
  refine ⟨hnull, ?_⟩
  set F : ℝ → ℝ := fun t => g.g (γ t) (Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc a b) t)
    (T.X (γ t)) with hF
  have hL := fun x => g.isLorentzianCoordMetric_coordMetric x
  -- the velocity in the chart at a point of the curve
  have hvelchart : ∀ x : M, ∀ t ∈ Icc a b, ∀ (w : ℝ → Fin n → ℝ), γ t ∈
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source →
      HasDerivAt (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ s)) (w t) t →
      MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ (Icc a b) t →
      F t = Lightlike.bil (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ t))) (w t)
        (timeCoord T x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ t))) := by
    intro x t ht w hsrc hder hmd
    have h1 := Causal.hasDerivWithinAt_chart_comp (I := 𝓘(ℝ, Fin n → ℝ)) x hmd hsrc
    have h2 := (uniqueDiffOn_Icc hab t ht).eq_deriv _ h1 hder.hasDerivWithinAt
    have hvq := eq_symmL_of_tTriv x (γ t) (mem_baseSet_of_mem_source x (γ t) hsrc) _ h2
    have hXq := timeOrientation_eq_symmL T x (γ t) hsrc
    simp only [hF]
    rw [hvq, hXq, metric_eq_bil_at g.toNondegMetric x (γ t) hsrc]
  -- nonvanishing
  have hne : ∀ t ∈ Icc a b, F t ≠ 0 := by
    intro t ht h0
    obtain ⟨w, O, hO, hsrc, hgeo, hw0, hbil⟩ := hnull t ht
    obtain ⟨hmd, -⟩ := geodesic_local_velocity hab ht hO hsrc hgeo.pos
    have hq := mem_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) (γ t)
    have h1 := hvelchart (γ t) t ht w hq (hgeo.pos t (mem_of_mem_nhds hO)) hmd
    rw [h0] at h1
    set y := extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) (γ t) with hy
    have hyt : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t)).target :=
      (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t)).map_source hq
    have hLf := Lightlike.Geodesic.isLorentzianForm_matForm (hL (γ t)) hyt
    have hqq : ∀ a b, Lightlike.Geodesic.pairing (g.coordMetric (γ t)) y a b =
        matForm (g.coordMetric (γ t) y) a b := fun a b =>
      Lightlike.Geodesic.pairing_eq_matForm _ _ a b
    have hX := timeCoord_timelike T (γ t) hyt
    have hwX : matForm (g.coordMetric (γ t) y) (w t) (timeCoord T (γ t) y) = 0 := by
      rw [← hqq, pairing_eq_bil]; exact h1.symm
    have hww : matForm (g.coordMetric (γ t) y) (w t) (w t) ≤ 0 := by
      rw [← hqq, pairing_eq_bil]; exact hbil.le
    exact hw0 (hLf.eq_zero_of_orthogonal_timelike (X := timeCoord T (γ t) y)
      (by rw [← hqq]; exact hX) hwX hww)
  -- continuity
  have hcont : ContinuousOn F (Icc a b) := by
    intro s hs
    obtain ⟨w, O, hO, hsrc, hgeo, hw0, hbil⟩ := hnull s hs
    set x := γ s with hx
    have hev : F =ᶠ[𝓝[Icc a b] s] fun t => Lightlike.bil
        (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ t))) (w t)
        (timeCoord T x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ t))) := by
      filter_upwards [nhdsWithin_le_nhds hO, self_mem_nhdsWithin] with t htO htI
      obtain ⟨w', O', hO', hsrc', hgeo', -, -⟩ := hnull t htI
      obtain ⟨hmd, -⟩ := geodesic_local_velocity hab htI hO' hsrc' hgeo'.pos
      exact hvelchart x t htI w (hsrc t htO) (hgeo.pos t htO) hmd
    have hq := mem_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) x
    have hytx : extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ s) ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target :=
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_source (hsrc s (mem_of_mem_nhds hO))
    have hRHS : ContinuousAt (fun t => Lightlike.bil
        (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ t))) (w t)
        (timeCoord T x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ t)))) s := by
      have hu : ContinuousAt (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ t)) s :=
        (hgeo.pos s (mem_of_mem_nhds hO)).continuousAt
      have hX : ContinuousAt (fun t => timeCoord T x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ t))) s :=
        ContinuousAt.comp (f := fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ t))
          ((continuousOn_timeCoord T x).continuousAt
            ((isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x).mem_nhds hytx)) hu
      have := Lightlike.Geodesic.continuousAt_pairing_curve (hL x).1 hu (hgeo.vel s (mem_of_mem_nhds hO)).continuousAt hX
        hytx
      refine this.congr ?_
      filter_upwards with t
      exact pairing_eq_bil _ _ _ _
    refine hRHS.continuousWithinAt.congr_of_eventuallyEq hev ?_
    obtain ⟨hmd, -⟩ := geodesic_local_velocity hab hs hO hsrc hgeo.pos
    exact hvelchart x s hs w (hsrc s (mem_of_mem_nhds hO)) (hgeo.pos s (mem_of_mem_nhds hO)) hmd
  obtain ⟨s₀, hs₀I, hs₀neg⟩ := hs₀
  intro t ht
  by_contra hcon
  have hpos : 0 < F t := lt_of_le_of_ne (not_lt.1 hcon) (hne t ht).symm
  have hpc := isPreconnected_Icc.image F hcont
  have h0 : (0 : ℝ) ∈ Icc (F s₀) (F t) := ⟨hs₀neg.le, hpos.le⟩
  obtain ⟨r, hr, hr0⟩ := hpc.Icc_subset ⟨s₀, hs₀I, rfl⟩ ⟨t, ht, rfl⟩ h0
  exact hne r hr hr0

end Lightlike.Penrose
