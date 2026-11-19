import Lightlike.Spacetime.ChartAgreement
import Lightlike.Spacetime.EinsteinEquations
/-!
# The Einstein equations with a source are the coordinate equations in every chart

`einsteinEq_iff_chart`: for the Levi-Civita connection of a Lorentzian metric `g` and a source given by a field `T` of continuous
bilinear forms, the equations `G + Λ g = κ T` of `EinsteinEquations.lean` hold iff they hold for the coordinate components
(`einsteinTensor` of the chart metric, the components of `T` on the coordinate fields) at every point of every chart. This is
`satisfiesEinstein_iff_chart_proved` (`ChartAgreement.lean`) with a source and a coupling.

**Limits.** The setting of `ChartAgreement.lean` (Hausdorff `C²` manifolds modelled on `Fin n → ℝ`, a `C^∞` connection); the source is a
field of bilinear forms (no regularity is required of it).
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology
noncomputable section
namespace Lightlike
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
variable (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
  (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)

/-- **The Einstein equations with a source are the coordinate equations in every chart**: for the Levi-Civita connection of `g` and a
source given by a field of continuous bilinear forms `T`, `G + Λ g = κ T` holds iff it holds for the coordinate components in the
chart at every point. -/
theorem einsteinEq_iff_chart (h : cov.IsLeviCivita g) (Λ κ : ℝ)
    (T : Π x : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] ℝ) :
    g.EinsteinEq cov Λ κ (fun x v w => T x v w) ↔
      ∀ x₀ : M, ∀ y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target, ∀ μ ν : Fin n,
        einsteinTensor (g.coordMetric x₀) μ ν y + Λ * g.coordMetric x₀ y μ ν =
          κ * T ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) (coordField x₀ μ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
            (coordField x₀ ν ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) := by
  constructor
  · rintro ⟨-, hE⟩ x₀ y hy μ ν
    have hp := symm_mem_chartTriv_baseSet x₀ hy
    have e := hE _ (coordField x₀ μ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
      (coordField x₀ ν ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
    have hs : cov.ricciAt ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
        (coordField x₀ μ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
        (coordField x₀ ν ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) = ricci (g.coordMetric x₀) μ ν y := by
      rw [ricciAt_symm_proved cov g h.1 h.2 _ _ _]
      exact ricciAt_coord cov x₀ g h hy ν μ
    have hg : g.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
        (coordField x₀ μ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
        (coordField x₀ ν ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) = g.coordMetric x₀ y μ ν := by
      rw [coordField_apply x₀ μ hy, coordField_apply x₀ ν hy, g.coordMetric_eq x₀ hy]
    unfold Connection.einsteinField at e
    rw [hs, scalarCurvatureAt_coord cov x₀ g h hy, hg] at e
    unfold einsteinTensor
    linarith
  · intro hvac
    refine ⟨h, fun p v w => ?_⟩
    set φ := extChartAt 𝓘(ℝ, Fin n → ℝ) p with hφ
    have hzs : p ∈ φ.source := mem_extChartAt_source p
    have hy : φ p ∈ φ.target := φ.map_source hzs
    have hp : p ∈ (tTriv (E := Fin n → ℝ) p).baseSet := by
      simpa [tTriv, TangentBundle.trivializationAt_baseSet] using (mem_chart_source (Fin n → ℝ) p)
    have hvac' := hvac p (φ p) hy
    have hc : ∀ σ ν : Fin n, cov.ricciAt p (coordBasis p hp σ) (coordBasis p hp ν) -
        (cov.scalarCurvatureAt g p / 2 - Λ) * g.g p (coordBasis p hp σ) (coordBasis p hp ν) -
        κ * T p (coordBasis p hp σ) (coordBasis p hp ν) = 0 := by
      intro σ ν
      have e := hvac' σ ν
      have hr := ricciAt_coord cov p g h hy σ ν
      have hs := scalarCurvatureAt_coord cov p g h hy
      have hg := g_coordField g p σ ν hy
      rw [hφ, (extChartAt 𝓘(ℝ, Fin n → ℝ) p).left_inv hzs] at hr hs hg e
      have hr' := ricciAt_coord cov p g h hy ν σ
      rw [hφ, (extChartAt 𝓘(ℝ, Fin n → ℝ) p).left_inv hzs] at hr'
      have e1 : ∀ k, coordBasis p hp k = coordField p k p := fun k =>
        (coordBasis_apply p hp k).trans (symmL_eq_coordField p hp k)
      rw [e1 σ, e1 ν]
      have hsym := ricciAt_symm_proved cov g h.1 h.2 p (coordField p σ p) (coordField p ν p)
      rw [hr, hs, hg]
      have hrs : ricci (g.coordMetric p) ν σ (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) =
          ricci (g.coordMetric p) σ ν (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) := by
        rw [← hr, hsym, hr']
      unfold einsteinTensor at e
      linarith
    set B : TangentSpace 𝓘(ℝ, Fin n → ℝ) p →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) p →ₗ[ℝ] ℝ :=
      RicB cov p hp - (cov.scalarCurvatureAt g p / 2 - Λ) • (g.g p).toBilinForm - κ • (T p).toBilinForm with hB
    have hB0 : B = 0 := by
      refine LinearMap.BilinForm.ext_basis (coordBasis p hp) fun σ ν => ?_
      have := hc σ ν
      simp only [hB, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
      show cov.ricciAt p _ _ - (cov.scalarCurvatureAt g p / 2 - Λ) * g.g p _ _ - κ * T p _ _ = 0
      linarith
    have := congrArg (fun B' => B' v w) hB0
    simp only [hB, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at this
    show cov.ricciAt p v w - cov.scalarCurvatureAt g p / 2 * g.g p v w + Λ * g.g p v w = κ * T p v w
    have h2 : (RicB cov p hp) v w = cov.ricciAt p v w := rfl
    have h3 : ((g.g p).toBilinForm) v w = g.g p v w := rfl
    have h4 : ((T p).toBilinForm) v w = T p v w := rfl
    rw [h2, h3, h4] at this
    linarith
end Lightlike
