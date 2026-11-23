import Lightlike.Spacetime.Raychaudhuri.RicciManifold
import Lightlike.Spacetime.EnergyConditionsField

/-!
# Focusing under the strong energy condition with a margin (GE3, Tier 1)

`raychaudhuri_focusing_strongEC` (`FocusingSEC.lean`) uses the strong energy condition `(T - ½ tr T · g)(ξ, ξ) ≥ 0`, which gives
`Ric(ξ, ξ) ≥ 0`. If the condition holds with a *margin* `ρ > 0` for unit timelike vectors,
`(T - ½ tr T · g)(ξ, ξ) ≥ ρ` when `g(ξ, ξ) = -1`, then `Ric(ξ, ξ) ≥ κ ρ` (`ricci_ge_of_strongEC_margin`), and the uniform
Ricci bound of `RicciManifold.lean` gives a length bound `L ≤ 3π/√(3 κ ρ)` independent of the initial expansion
(`raychaudhuri_focusing_strongEC_margin`).

**Limits.** Dimension four, `Λ = 0` (absorbed into `T` by `einsteinEq_iff_absorb`), rotation-free congruence.
-/

open Bundle Manifold Set Real
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin 4 → ℝ) M] [IsManifold 𝓘(ℝ, Fin 4 → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin 4 → ℝ) 2 M] [T2Space M]

/-- **A margin in the strong energy condition is a Ricci bound**: under `G = κ T`, if
`(T - ½ tr_g T · g)(ξ, ξ) ≥ ρ` for every unit timelike `ξ` (`g(ξ, ξ) = -1`), then `Ric(ξ, ξ) ≥ κ ρ` for those `ξ`. -/
theorem ricci_ge_of_strongEC_margin (gL : LorentzianMetric 𝓘(ℝ, Fin 4 → ℝ) M 4)
    (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) M) {κ ρ : ℝ} (hκ : 0 < κ)
    {T : Π x : M, TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x →L[ℝ] TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x →L[ℝ] ℝ}
    (hE : gL.toNondegMetric.EinsteinEq cov 0 κ (fun x v w => T x v w))
    (hρ : ∀ (x : M) (ξ : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x), gL.g x ξ ξ = -1 →
      ρ ≤ T x ξ ξ - (1 / 2) * traceG (gL.g x) (T x) (gL.lorentzian x).bilinForm_nondegenerate * gL.g x ξ ξ)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x) (hξ : gL.g x ξ ξ = -1) :
    κ * ρ ≤ cov.ricciAt x ξ ξ := by
  have h1 := LorentzianMetric.ricciAt_of_einsteinEq hE x ξ ξ
  have h2 := LorentzianMetric.scalarCurvatureAt_of_einsteinEq hE x
  have h3 := hρ x ξ hξ
  rw [h1, h2]
  have e : κ * T x ξ ξ + -κ * traceG (gL.g x) (T x) (gL.lorentzian x).bilinForm_nondegenerate / 2 * gL.g x ξ ξ =
      κ * (T x ξ ξ - 1 / 2 * traceG (gL.g x) (T x) (gL.lorentzian x).bilinForm_nondegenerate * gL.g x ξ ξ) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left h3 hκ.le

/-- **Focusing under the strong energy condition with a margin** (Raychaudhuri; timelike Bonnet–Myers type): for a Lorentzian
four-manifold with `G = κ T`, `κ > 0`, and `(T - ½ tr_g T · g)(ξ, ξ) ≥ ρ > 0` for unit timelike `ξ`, a smooth vector field
`V` that is unit, geodesic and rotation-free along an integral curve `γ` on `[0, L)` forces `L ≤ 3π/√(3 κ ρ)`, whatever the
initial expansion. -/
theorem raychaudhuri_focusing_strongEC_margin (gL : LorentzianMetric 𝓘(ℝ, Fin 4 → ℝ) M 4)
    (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) M) [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita gL.toNondegMetric) {κ ρ : ℝ} (hκ : 0 < κ) (hρ0 : 0 < ρ)
    {T : Π x : M, TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x →L[ℝ] TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x →L[ℝ] ℝ}
    (hE : gL.toNondegMetric.EinsteinEq cov 0 κ (fun x v w => T x v w))
    (hρ : ∀ (x : M) (ξ : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x), gL.g x ξ ξ = -1 →
      ρ ≤ T x ξ ξ - (1 / 2) * traceG (gL.g x) (T x) (gL.lorentzian x).bilinForm_nondegenerate * gL.g x ξ ξ)
    {V : Π p : M, TangentSpace 𝓘(ℝ, Fin 4 → ℝ) p}
    (hV : ContMDiff 𝓘(ℝ, Fin 4 → ℝ) (𝓘(ℝ, Fin 4 → ℝ).prod 𝓘(ℝ, Fin 4 → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin 4 → ℝ) M))) {γ : ℝ → M} {L : ℝ}
    (hγ : ∀ s ∈ Ico 0 L, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 4 → ℝ) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ s))))
    (hgeo : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), cov V q (V q) = 0)
    (hnorm : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), gL.g q (V q) (V q) = -1)
    (hrot : ∀ s ∈ Ico 0 L, ∀ u w : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) (γ s),
      gL.g (γ s) (cov V (γ s) u) w = gL.g (γ s) (cov V (γ s) w) u) :
    L ≤ π * (3 / √(3 * (κ * ρ))) := by
  have hR : ∀ s ∈ Ico 0 L, κ * ρ ≤ cov.ricciAt (γ s) (V (γ s)) (V (γ s)) := fun s hs =>
    ricci_ge_of_strongEC_margin gL cov hκ hE hρ (γ s) (V (γ s)) (hnorm s hs).self_of_nhds
  have := raychaudhuri_focusing_ricci_manifold cov gL h hV (by norm_num) (mul_pos hκ hρ0) hγ hgeo hnorm hrot hR
  norm_num at this
  rw [Real.sqrt_mul (by norm_num)]
  exact this

end Lightlike
