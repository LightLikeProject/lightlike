import Lightlike.Spacetime.Raychaudhuri.RicciManifold
import Lightlike.Spacetime.EnergyConditionsField

/-!
# Ricci curvature of a perfect fluid along its flow, and focusing of the fluid (GE3, Tier 1)

For Einstein's equations `G = κ T` with a perfect-fluid source `T = (ρ + p) u ⊗ u + p g`, `g(u, u) = -1`, the Ricci tensor
in the direction of the flow is `Ric(u, u) = (κ/2)(ρ + 3p)` (`ricci_fluid_comoving`): the trace of Einstein's equations is
`R = κ(ρ - 3p)`, and `T(u, u) = ρ`. This is the form in which the source enters the Raychaudhuri equation.
With `ρ + 3p ≥ σ > 0` along the flow, the uniform Ricci bound of `RicciManifold.lean` gives
`raychaudhuri_focusing_fluid`: a geodesic, rotation-free, unit comoving congruence has length at most `3π/√(3 κ σ / 2)`.

**Limits.** Dimension four, `Λ = 0`, rotation-free congruence; the fluid velocity is the field `V` along which one focuses.
-/

open Bundle Manifold Set Real
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin 4 → ℝ) M] [IsManifold 𝓘(ℝ, Fin 4 → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin 4 → ℝ) 2 M] [T2Space M]

/-- **Ricci curvature along the flow of a perfect fluid**: under `G = κ T` with `T = fluidField u ρ p` and `g(u, u) = -1`
at `x`, `Ric(u, u) = (κ/2)(ρ + 3p)`. -/
theorem ricci_fluid_comoving (gL : LorentzianMetric 𝓘(ℝ, Fin 4 → ℝ) M 4)
    (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) M) {κ : ℝ}
    {u : Π x : M, TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x} {ρ p : M → ℝ}
    (hE : gL.toNondegMetric.EinsteinEq cov 0 κ (fun x v w => gL.fluidField u ρ p x v w))
    (x : M) (hu : gL.g x (u x) (u x) = -1) :
    cov.ricciAt x (u x) (u x) = κ / 2 * (ρ x + 3 * p x) := by
  rw [LorentzianMetric.ricciAt_of_einsteinEq hE x (u x) (u x), LorentzianMetric.scalarCurvatureAt_of_einsteinEq hE x]
  have htr : traceG (gL.g x) (gL.fluidField u ρ p x) (gL.lorentzian x).bilinForm_nondegenerate = 3 * p x - ρ x :=
    traceG_fluid (gL.lorentzian x) hu (ρ x) (p x)
  rw [htr, hu]
  show κ * fluidT (gL.g x) (u x) (ρ x) (p x) (u x) (u x) + _ = _
  rw [fluidT_apply, hu]
  ring

/-- **Focusing of a perfect-fluid flow** (Raychaudhuri; timelike Bonnet–Myers type): for a Lorentzian four-manifold with
`G = κ T`, `κ > 0`, `T` a perfect fluid with velocity `V` and `ρ + 3p ≥ σ > 0` along an integral curve `γ` of `V` on `[0, L)`,
if `V` is unit, geodesic and rotation-free near `γ`, then `L ≤ 3π/√(3 (κ σ / 2))`, whatever the initial expansion. -/
theorem raychaudhuri_focusing_fluid (gL : LorentzianMetric 𝓘(ℝ, Fin 4 → ℝ) M 4)
    (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) M) [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita gL.toNondegMetric) {κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ)
    {V : Π p : M, TangentSpace 𝓘(ℝ, Fin 4 → ℝ) p} {ρ p : M → ℝ}
    (hE : gL.toNondegMetric.EinsteinEq cov 0 κ (fun x v w => gL.fluidField V ρ p x v w))
    (hV : ContMDiff 𝓘(ℝ, Fin 4 → ℝ) (𝓘(ℝ, Fin 4 → ℝ).prod 𝓘(ℝ, Fin 4 → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin 4 → ℝ) M))) {γ : ℝ → M} {L : ℝ}
    (hγ : ∀ s ∈ Ico 0 L, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 4 → ℝ) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ s))))
    (hgeo : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), cov V q (V q) = 0)
    (hnorm : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), gL.g q (V q) (V q) = -1)
    (hrot : ∀ s ∈ Ico 0 L, ∀ u w : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) (γ s),
      gL.g (γ s) (cov V (γ s) u) w = gL.g (γ s) (cov V (γ s) w) u)
    (hρp : ∀ s ∈ Ico 0 L, σ ≤ ρ (γ s) + 3 * p (γ s)) :
    L ≤ π * (3 / √(3 * (κ / 2 * σ))) := by
  have hR : ∀ s ∈ Ico 0 L, κ / 2 * σ ≤ cov.ricciAt (γ s) (V (γ s)) (V (γ s)) := fun s hs => by
    rw [ricci_fluid_comoving gL cov hE (γ s) (hnorm s hs).self_of_nhds]
    exact mul_le_mul_of_nonneg_left (hρp s hs) (by positivity)
  have := raychaudhuri_focusing_ricci_manifold cov gL h hV (by norm_num) (by positivity) hγ hgeo hnorm hrot hR
  norm_num at this
  rw [Real.sqrt_mul (by norm_num)]
  exact this

end Lightlike
