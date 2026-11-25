import Lightlike.Spacetime.PenroseSingularity.FamilyPoint
import Lightlike.Spacetime.PenroseSingularity.GeodesicNonzero

/-!
# A flow family through a given null geodesic (G1-012, step D3b wiring)

For a null geodesic `γ` on `[0, L]` and a smooth family `zS` of initial phases through the phase of `γ` at `0`,
there is a flow family on a neighbourhood of `[0, L]` that contains `γ`.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Penrose

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **A flow family through a null geodesic.** -/
theorem exists_flowFamily_of_generator (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) {γ : ℝ → M} {L : ℝ}
    (hL : 0 ≤ L) (hγ : IsNullGeodesicOn g γ (Icc 0 L))
    {zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {Sg₀ : Set (Fin m → ℝ)} (hSg₀ : IsOpen Sg₀)
    (hzS : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ zS Sg₀)
    {σ₀ : Fin m → ℝ} (hσ₀ : σ₀ ∈ Sg₀) (hz0 : zS σ₀ = phase (n := n) γ 0) :
    ∃ (Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M) (Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M))
      (J : Set ℝ) (Sg : Set (Fin m → ℝ)), FlowFamily g Γ zS Nz J Sg ∧ σ₀ ∈ Sg ∧ Icc 0 L ⊆ J ∧
      Sg ⊆ Sg₀ ∧ ∀ t ∈ Icc 0 L, Γ (zS σ₀) t = γ t := by
  obtain ⟨ε, hε, hgeo⟩ := hγ.exists_open_interval g hL
  have hI₀ : IsOpen (Ioo (-ε) (L + ε)) := isOpen_Ioo
  have hsub : Icc 0 L ⊆ Ioo (-ε) (L + ε) := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hflow := sflowGerm_along (g := g) hI₀ ordConnected_Ioo hgeo rfl
    (hsub ⟨le_rfl, hL⟩) hL hsub L ⟨hL, le_rfl⟩
  obtain ⟨Γ, Nz, J, Sg, hF, hσ, hJ, hSg⟩ := exists_flowFamily_of_sflow (gM := g) hL hflow hSg₀ hzS hσ₀ hz0
  refine ⟨Γ, Nz, J, Sg, hF, hσ, hJ, hSg, fun t ht => ?_⟩
  have hNz : zS σ₀ ∈ Nz := hF.mem_Nz σ₀ hσ
  have hK : IsOpen (J ∩ Ioo (-ε) (L + ε)) := hF.isOpen_J.inter hI₀
  have hKc : IsPreconnected (J ∩ Ioo (-ε) (L + ε)) :=
    (hF.convex_J.inter (convex_Ioo _ _)).isPreconnected
  have h0K : (0 : ℝ) ∈ J ∩ Ioo (-ε) (L + ε) := ⟨hF.zero_mem, hsub ⟨le_rfl, hL⟩⟩
  have := eqOn_of_phase_eq' g hK hKc ((hF.geo _ hNz).mono inter_subset_left)
    (hgeo.mono inter_subset_right) h0K (by rw [hF.phase_zero _ hNz, hz0])
  exact this ⟨hJ ht, hsub ht⟩

end Lightlike.Penrose
