import Lightlike.Spacetime.EinsteinChart
import Lightlike.Spacetime.SchwarzschildManifold
/-!
# The Einstein equations with a source on an open subset of `ℝⁿ`

`openMetric_einsteinEq_iff`: for a Lorentzian coordinate metric `g` on an open set `U` and a source with components `Tm`, the Einstein
equations `G + Λ g = κ T` (`EinsteinEquations.lean`) for the Levi-Civita connection of the metric `openMetric U g hg` of the manifold `↥U`
hold iff the coordinate equations hold at every point of `U`. It combines `einsteinEq_iff_chart` (`EinsteinChart.lean`), the bridge
`openMetric_coordMetric` (`OpenCoordMetric.lean`) and the congruence of the Einstein tensor of two metrics that agree on an open
set (`SchwarzschildManifold.lean`).

**Limits.** Open subsets of `ℝⁿ` with a `C^∞` connection; the source is the field of bilinear forms `y ↦ matForm (Tm y)`.
-/

open Bundle Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
noncomputable section
namespace Lightlike
variable {n : ℕ}

/-- **The Einstein equations with a source on an open subset of `ℝⁿ` are the coordinate equations**: for a Lorentzian coordinate metric `g`
on an open set `U` and a source with components `Tm`, the equations `G + Λ g = κ T` for the Levi-Civita connection of `openMetric U g hg`
hold iff they hold for the coordinate components at every point of `U`. -/
theorem openMetric_einsteinEq_iff (U : Opens (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : IsLorentzianCoordMetric g U) (cov : Connection 𝓘(ℝ, Fin n → ℝ) U)
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (h : cov.IsLeviCivita (openMetric U g hg))
    (Λ κ : ℝ) (Tm : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) :
    (openMetric U g hg).EinsteinEq cov Λ κ (fun x v w => matForm (Tm x.1) v w) ↔
      ∀ y ∈ U, ∀ μ ν, einsteinTensor g μ ν y + Λ * g y μ ν = κ * Tm y μ ν := by
  refine (einsteinEq_iff_chart cov (openMetric U g hg) h Λ κ (fun x => matForm (Tm x.1))).trans ?_
  have hcongr : ∀ x₀ : U, ∀ z ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target,
      (openMetric U g hg).coordMetric x₀ z = g z := fun x₀ z hz => openMetric_coordMetric U g hg x₀ hz
  have hT : ∀ (x₀ : U) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) (μ ν : Fin n),
      matForm (Tm ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y : U).1)
        (coordField x₀ μ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
        (coordField x₀ ν ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) = Tm y μ ν := by
    intro x₀ y hy μ ν
    have hp := symm_mem_chartTriv_baseSet x₀ hy
    have e : ∀ k, coordField x₀ k ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) = Pi.single k 1 := fun k => by
      rw [← symmL_eq_coordField x₀ hp k, opens_symmL]; rfl
    rw [e μ, e ν, matForm_single, opens_extChartAt_symm U x₀ hy]
  have hmem : ∀ (x₀ : U) {y : Fin n → ℝ}, y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target → y ∈ (U : Set (Fin n → ℝ)) := by
    intro x₀ y hy
    have h2 : (((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y : U) : Fin n → ℝ) ∈ (U : Set (Fin n → ℝ)) :=
      ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y : U).2
    rwa [opens_extChartAt_symm U x₀ hy] at h2
  constructor
  · intro H y hy μ ν
    have hx₀ : (⟨y, hy⟩ : U) = ⟨y, hy⟩ := rfl
    set x₀ : U := ⟨y, hy⟩
    have hyt : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
      have := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (mem_extChartAt_source x₀)
      rwa [opens_extChartAt_apply] at this
    have e := H x₀ y hyt μ ν
    erw [hT x₀ hyt μ ν] at e
    rw [einsteinTensor_congr_on (U := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
      (isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x₀) (hcongr x₀) hyt, hcongr x₀ y hyt] at e
    exact e
  · intro H x₀ y hy μ ν
    have hyU := hmem x₀ hy
    erw [hT x₀ hy μ ν]
    rw [einsteinTensor_congr_on (U := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
      (isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x₀) (hcongr x₀) hy, hcongr x₀ y hy]
    exact H y hyU μ ν
end Lightlike
