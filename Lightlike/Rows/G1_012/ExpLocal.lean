import Lightlike.Rows.G1_012.GeodesicChartIndep
import Lightlike.Geodesic.ExpJoint

/-!
# The exponential map on a manifold, near a point (G1-012, G1-006 manifold lift)

`exists_manifold_exp`: for a Lorentzian manifold `(M, g)` and `x₀ : M` there are `ρ > 0` and a map
`Exp : ℝⁿ × ℝⁿ → M` (base point `p` and velocity `v`, both in the coordinates of the chart at `x₀`), continuous on
`ball (ψ x₀) ρ × ball 0 ρ`, with `Exp (p, 0) = ψ⁻¹ p` and such that `t ↦ Exp (p, t v)` is a geodesic curve of `M`
(`IsGeodesicCurveOn`) on `(-1, 1)` with chart velocity `v` at `0`. It is `ψ⁻¹ ∘ E` for the chart-level `E` of
`Geodesic.exists_expMap_joint`, with the geodesic property transported by `isGeodesicCurveOn_of_chart`.

This is the local form: patching geodesics along a segment that leaves one chart needs uniqueness on `M` and is not
part of this file. The normal exponential map of a compact surface is continuous near the zero section by this result.
-/

open Bundle Manifold Set Filter Topology Metric
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **The exponential map of a Lorentzian manifold near a point.** See the module docstring. -/
theorem exists_manifold_exp (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (x₀ : M) :
    ∃ (ρ : ℝ) (Exp : (Fin n → ℝ) × (Fin n → ℝ) → M), 0 < ρ ∧
      ContinuousOn Exp (ball (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x₀) ρ ×ˢ ball (0 : Fin n → ℝ) ρ) ∧
      (∀ p ∈ ball (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x₀) ρ, Exp (p, 0) = (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm p) ∧
      ∀ p ∈ ball (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x₀) ρ, ∀ v ∈ ball (0 : Fin n → ℝ) ρ,
        ∃ (γ : ℝ → M) (w : ℝ → Fin n → ℝ), γ 0 = (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm p ∧
          IsGeodesicCurveOn g γ (Ioo (-1) 1) ∧
          Lightlike.Geodesic.IsGeodesicOn (g.coordMetric x₀) (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (γ s)) w
            (Ioo (-1) 1) ∧ w 0 = v ∧ ∀ t ∈ Ioo (-1 : ℝ) 1, γ t = Exp (p, t • v) := by
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hψ
  have hg := g.toNondegMetric.isCoordMetric_coordMetric x₀
  have hx : ψ x₀ ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := ψ.map_source (mem_extChartAt_source x₀)
  obtain ⟨ρ, E, hρ, hE0, hsm, -, hEU, hgeo⟩ := Lightlike.Geodesic.exists_expMap_joint hg hx
  refine ⟨ρ, fun z => ψ.symm (E z), hρ, ?_, fun p hp => by simp [hE0 p hp], ?_⟩
  · exact (continuousOn_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) x₀).comp hsm.continuousOn
      (fun z hz => hEU z.1 hz.1 z.2 hz.2)
  · intro p hp v hv
    obtain ⟨γc, w, hγ0, hw0, hgeoc, hγE⟩ := hgeo p hp v hv
    have hsv : ∀ t ∈ Ioo (-1 : ℝ) 1, t • v ∈ ball (0 : Fin n → ℝ) ρ := by
      intro t ht
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs]
      have hv' : ‖v‖ < ρ := mem_ball_zero_iff.1 hv
      have : |t| < 1 := abs_lt.2 ⟨ht.1, ht.2⟩
      calc |t| * ‖v‖ ≤ 1 * ‖v‖ := by gcongr
        _ < ρ := by linarith
    have htgt : ∀ t ∈ Ioo (-1 : ℝ) 1, γc t ∈ ψ.target := by
      intro t ht
      rw [hγE t (Ioo_subset_Icc_self ht)]
      exact hEU p hp _ (hsv t ht)
    set γ : ℝ → M := fun s => ψ.symm (γc s) with hγ
    have hchart : ∀ s ∈ Ioo (-1 : ℝ) 1, ψ (γ s) = γc s := fun s hs => ψ.right_inv (htgt s hs)
    have hsrc : ∀ s ∈ Ioo (-1 : ℝ) 1, γ s ∈ ψ.source := fun s hs => ψ.map_target (htgt s hs)
    have hgeoγ : Lightlike.Geodesic.IsGeodesicOn (g.coordMetric x₀) (fun s => ψ (γ s)) w (Ioo (-1) 1) := by
      refine ⟨fun s hs => ?_, fun s hs => ?_⟩
      · refine (hgeoc.pos s (Ioo_subset_Ioo (by norm_num) (by norm_num) hs)).congr_of_eventuallyEq ?_
        filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
        exact hchart r hr
      · refine (hgeoc.vel s (Ioo_subset_Ioo (by norm_num) (by norm_num) hs)).congr_deriv ?_
        rw [hchart s hs]
    refine ⟨γ, w, ?_, isGeodesicCurveOn_of_chart g x₀ isOpen_Ioo hsrc hgeoγ, hgeoγ, hw0, fun t ht => ?_⟩
    · simp [hγ, hγ0]
    · simp [hγ, hγE t (Ioo_subset_Icc_self ht)]

end Lightlike.Penrose
