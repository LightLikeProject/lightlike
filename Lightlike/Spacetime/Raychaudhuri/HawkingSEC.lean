import Lightlike.Spacetime.Raychaudhuri.HawkingManifold
import Lightlike.Spacetime.Raychaudhuri.FocusingSEC

/-!
# Hawking's bound under the strong energy condition (GE3, Tier 2)

The physical form of `hawking_bound_manifold`: in dimension four with `G = κ T`, `κ > 0`, and `T` satisfying the strong
energy condition, a uniform bound `Θ(γ 0) ≤ C < 0` on the initial expansion of a unit geodesic rotation-free congruence
bounds the length of its integral curves by `3 / |C|`.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin 4 → ℝ) M] [IsManifold 𝓘(ℝ, Fin 4 → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin 4 → ℝ) 2 M] [T2Space M]

/-- **Hawking's bound under the strong energy condition** (dimension four, `Λ = 0`): if `Θ(γ 0) ≤ C < 0` then the
integral curve of the unit geodesic rotation-free field `V` has parameter length `L ≤ 3 / |C|`. -/
theorem hawking_bound_strongEC (gL : LorentzianMetric 𝓘(ℝ, Fin 4 → ℝ) M 4)
    (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) M) [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita gL.toNondegMetric) {κ : ℝ} (hκ : 0 < κ)
    {T : Π x : M, TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x →L[ℝ] TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x →L[ℝ] ℝ}
    (hE : gL.toNondegMetric.EinsteinEq cov 0 κ (fun x v w => T x v w)) (hS : gL.StrongECField T)
    {V : Π p : M, TangentSpace 𝓘(ℝ, Fin 4 → ℝ) p}
    (hV : ContMDiff 𝓘(ℝ, Fin 4 → ℝ) (𝓘(ℝ, Fin 4 → ℝ).prod 𝓘(ℝ, Fin 4 → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin 4 → ℝ) M))) {γ : ℝ → M} {L C : ℝ}
    (hγ : ∀ s ∈ Ico 0 L, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 4 → ℝ) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ s))))
    (hgeo : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), cov V q (V q) = 0)
    (hnorm : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), gL.g q (V q) (V q) = -1)
    (hrot : ∀ s ∈ Ico 0 L, ∀ u w : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) (γ s),
      gL.g (γ s) (cov V (γ s) u) w = gL.g (γ s) (cov V (γ s) w) u)
    (hC : C < 0) (h0 : expansionM cov V (γ 0) ≤ C) : L ≤ 3 / |C| := by
  have hric := (LorentzianMetric.strongECField_iff_ricci hκ hE).1 hS
  have hR : ∀ s ∈ Ico 0 L, 0 ≤ cov.ricciAt (γ s) (V (γ s)) (V (γ s)) := fun s hs =>
    hric (γ s) (V (γ s)) (by rw [(hnorm s hs).self_of_nhds]; norm_num)
  have := hawking_bound_manifold cov gL h hV (by norm_num) hγ hgeo hnorm hrot hR hC h0
  norm_num at this
  exact this

end Lightlike
