import Lightlike.Spacetime.PenroseSingularity.GeodesicUnique
import Lightlike.Spacetime.PenroseSingularity.ExpFlow
import Lightlike.Spacetime.PenroseSingularity.GeodesicChartIndep
import Lightlike.Spacetime.PenroseSingularity.ExpMap

/-!
# A geodesic with nonzero velocity at one time has nonzero velocity at all times (G1-012)

On an open interval, a geodesic curve whose velocity vanishes at one time agrees with the constant curve there
(geodesic uniqueness), so its velocity vanishes everywhere.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)

/-- **Nonzero velocity propagates along a geodesic curve on an open interval.** -/
theorem phase_snd_ne_zero {γ : ℝ → M} {J : Set ℝ} (hJo : IsOpen J) (hJc : IsPreconnected J)
    (h : IsGeodesicCurveOn g γ J) {t₀ t₁ : ℝ} (ht₀ : t₀ ∈ J) (ht₁ : t₁ ∈ J)
    (h0 : (phase (n := n) γ t₀).snd ≠ 0) : (phase (n := n) γ t₁).snd ≠ 0 := by
  intro h1
  obtain ⟨w, O, hO, hsrc, hgeo⟩ := h t₁ ht₁
  set O' : Set ℝ := interior O with hO'
  have hO'o : IsOpen O' := isOpen_interior
  have ht₁O' : t₁ ∈ O' := mem_interior_iff_mem_nhds.2 hO
  have hgeo' : Lightlike.Geodesic.IsGeodesicOn (g.coordMetric (γ t₁))
      (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t₁) (γ s)) w O' :=
    ⟨fun t ht => hgeo.pos t (interior_subset ht), fun t ht => hgeo.vel t (interior_subset ht)⟩
  obtain ⟨-, hphase⟩ := phase_coord g (γ t₁) hO'o (fun s hs => hsrc s (interior_subset hs)) hgeo' ht₁O'
  have hb : γ t₁ ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ t₁)).baseSet := mem_baseSet_trivializationAt _ _ _
  have hw : w t₁ = 0 := by
    rw [← hphase]
    have : (phase (n := n) γ t₁) = ⟨γ t₁, 0⟩ := by
      unfold phase at h1 ⊢; congr 1
    rw [this]
    exact ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ t₁)).linear ℝ hb).map_zero
  have hderiv := (hgeo.pos t₁ (mem_of_mem_nhds hO)).deriv
  have heq := IsGeodesicCurveOn.eqOn g hJo hJc h (isGeodesicCurveOn_const g (γ t₁) J) ht₁ rfl
    (by rw [hderiv, hw]; simp)
  have hev : γ =ᶠ[𝓝 t₀] fun _ => γ t₁ := Filter.eventually_of_mem (hJo.mem_nhds ht₀) heq
  apply h0
  unfold phase
  rw [hev.mfderiv_eq]
  simp
  rfl

/-- **A null geodesic on a closed interval is a geodesic curve on an open interval around it.** -/
theorem IsNullGeodesicOn.exists_open_interval {γ : ℝ → M} {L : ℝ} (hL : 0 ≤ L)
    (h : IsNullGeodesicOn g γ (Icc 0 L)) :
    ∃ ε > 0, IsGeodesicCurveOn g γ (Ioo (-ε) (L + ε)) := by
  choose w O hO hsrc hgeo _ using h
  set U : Set ℝ := ⋃ t : Icc 0 L, interior (O t t.2) with hU
  have hUo : IsOpen U := isOpen_iUnion fun _ => isOpen_interior
  have hsub : Icc 0 L ⊆ U := fun t ht =>
    mem_iUnion.2 ⟨⟨t, ht⟩, mem_interior_iff_mem_nhds.2 (hO t ht)⟩
  have hgU : IsGeodesicCurveOn g γ U := by
    intro s hs
    obtain ⟨t, hst⟩ := mem_iUnion.1 hs
    have hcurve := isGeodesicCurveOn_of_chart g (γ t) isOpen_interior
      (fun r hr => hsrc t t.2 r (interior_subset hr))
      (w := w t t.2) ⟨fun r hr => (hgeo t t.2).pos r (interior_subset hr),
        fun r hr => (hgeo t t.2).vel r (interior_subset hr)⟩
    exact (hcurve s hst).imp fun _ ⟨O', hO', hr⟩ => ⟨O', hO', hr⟩
  obtain ⟨ε, hε, hth⟩ := isCompact_Icc.exists_thickening_subset_open hUo hsub
  refine ⟨ε, hε, hgU.mono fun r hr => hth ?_⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨if r < 0 then 0 else if r > L then L else r, ?_, ?_⟩
  · split_ifs with h1 h2
    · exact ⟨le_rfl, hL⟩
    · exact ⟨hL, le_rfl⟩
    · exact ⟨not_lt.1 h1, not_lt.1 h2⟩
  · rw [Real.dist_eq]
    split_ifs with h1 h2
    · rw [abs_lt]; constructor <;> linarith [hr.1]
    · rw [abs_lt]; constructor <;> linarith [hr.2]
    · simp [hε]

end Lightlike.Penrose
