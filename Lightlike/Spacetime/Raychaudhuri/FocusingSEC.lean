import Lightlike.Spacetime.RaychaudhuriManifold
import Lightlike.Spacetime.EnergyConditionsField

/-!
# Geodesic focusing under the strong energy condition (GE3)

`raychaudhuri_focusing_manifold` (`Lightlike/Spacetime/RaychaudhuriManifold.lean`) needs `Ric(V, V) ≥ 0` along the
integral curve. Under the Einstein equations `G = κ T` with `κ > 0` in dimension four, the strong energy condition of
`T` is exactly `Ric(ξ, ξ) ≥ 0` for timelike `ξ` (`strongECField_iff_ricci`). This file joins the two: the physical form of
the focusing theorem.

**Limits.** Dimension four, `Λ = 0` (a cosmological constant is absorbed into `T` by `einsteinEq_iff_absorb`); the congruence
is rotation-free, as in `raychaudhuri_focusing_manifold`.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin 4 → ℝ) M] [IsManifold 𝓘(ℝ, Fin 4 → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin 4 → ℝ) 2 M] [T2Space M]

/-- **Focusing of timelike geodesics under the strong energy condition** (see `kar-sengupta-2007`, gr-qc/0611123, for the focusing argument): for a
Lorentzian metric on a four-manifold with its Levi-Civita connection, `G = κ T` with `κ > 0` and `T` satisfying the strong
energy condition, a smooth vector field `V` that is unit, geodesic and rotation-free along an integral curve `γ` on `[0, L)`
and converging at `γ 0` (`Θ < 0`) gives `L ≤ 3 / |Θ(γ 0)|`. -/
theorem raychaudhuri_focusing_strongEC (gL : LorentzianMetric 𝓘(ℝ, Fin 4 → ℝ) M 4)
    (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) M) [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita gL.toNondegMetric) {κ : ℝ} (hκ : 0 < κ)
    {T : Π x : M, TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x →L[ℝ] TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x →L[ℝ] ℝ}
    (hE : gL.toNondegMetric.EinsteinEq cov 0 κ (fun x v w => T x v w)) (hS : gL.StrongECField T)
    {V : Π p : M, TangentSpace 𝓘(ℝ, Fin 4 → ℝ) p}
    (hV : ContMDiff 𝓘(ℝ, Fin 4 → ℝ) (𝓘(ℝ, Fin 4 → ℝ).prod 𝓘(ℝ, Fin 4 → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin 4 → ℝ) M))) {γ : ℝ → M} {L : ℝ}
    (hγ : ∀ s ∈ Ico 0 L, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 4 → ℝ) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ s))))
    (hgeo : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), cov V q (V q) = 0)
    (hnorm : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), gL.g q (V q) (V q) = -1)
    (hrot : ∀ s ∈ Ico 0 L, ∀ u w : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) (γ s),
      gL.g (γ s) (cov V (γ s) u) w = gL.g (γ s) (cov V (γ s) w) u)
    (h0 : expansionM cov V (γ 0) < 0) : L ≤ 3 / |expansionM cov V (γ 0)| := by
  have hric := (LorentzianMetric.strongECField_iff_ricci hκ hE).1 hS
  have hR : ∀ s ∈ Ico 0 L, 0 ≤ cov.ricciAt (γ s) (V (γ s)) (V (γ s)) := fun s hs =>
    hric (γ s) (V (γ s)) (by rw [(hnorm s hs).self_of_nhds]; norm_num)
  have := raychaudhuri_focusing_manifold cov gL h hV (by norm_num) hγ hgeo hnorm hrot hR h0
  norm_num at this
  exact this

end Lightlike
