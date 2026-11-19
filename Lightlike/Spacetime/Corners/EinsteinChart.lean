import Lightlike.Spacetime.ChartAgreement
import Lightlike.Spacetime.Corners.ChartAgreement
import Lightlike.Spacetime.EinsteinEquations
import Lightlike.Spacetime.Corners.EinsteinEquations
import Lightlike.Spacetime.Corners.ChartConnection
import Lightlike.Spacetime.Corners.ChartCovariant
import Lightlike.Spacetime.Corners.Coordinates
import Lightlike.Spacetime.Corners.Curvature
import Lightlike.Spacetime.Corners.CurvatureSymmetries
/-!
# The Einstein equations with a source are the coordinate equations in every chart

`einsteinEq_iff_chartW`: for the Levi-Civita connection of a Lorentzian metric `g` and a source given by a field `T` of continuous
bilinear forms, the equations `G + Λ g = κ T` of `EinsteinEquations.lean` hold iff they hold for the coordinate components
(`einsteinTensor` of the chart metric, the components of `T` on the coordinate fields) at every point of every chart. This is
`satisfiesEinstein_iff_chart_proved` (`ChartAgreement.lean`) with a source and a coupling.

**Limits.** The setting of `ChartAgreement.lean` (`C²` manifolds with corners modelled on `Fin n → ℝ` (derivatives within `range I`), a locally smooth connection); the source is a
field of bilinear forms (no regularity is required of it).
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology
noncomputable section
namespace Lightlike
variable {n : ℕ} {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 2 M]
variable (cov : Connection I M) [LocallySmoothConnectionW cov]
  (g : LorentzianMetric I M n)

/-- **The Einstein equations with a source are the coordinate equations in every chart**: for the Levi-Civita connection of `g` and a
source given by a field of continuous bilinear forms `T`, `G + Λ g = κ T` holds iff it holds for the coordinate components in the
chart at every point. -/
theorem einsteinEq_iff_chartW (h : cov.IsLeviCivita g) (Λ κ : ℝ)
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    g.EinsteinEqW cov Λ κ (fun x v w => T x v w) ↔
      ∀ x₀ : M, ∀ y ∈ (extChartAt I x₀).target, ∀ μ ν : Fin n,
        einsteinTensorW (range I) (g.coordMetricW x₀) μ ν y + Λ * g.coordMetricW x₀ y μ ν =
          κ * T ((extChartAt I x₀).symm y) (coordFieldW (I := I) x₀ μ ((extChartAt I x₀).symm y))
            (coordFieldW (I := I) x₀ ν ((extChartAt I x₀).symm y)) := by
  constructor
  · rintro ⟨-, hE⟩ x₀ y hy μ ν
    have hp := symm_mem_chartTriv_baseSetW x₀ hy
    have e := hE _ (coordFieldW (I := I) x₀ μ ((extChartAt I x₀).symm y))
      (coordFieldW (I := I) x₀ ν ((extChartAt I x₀).symm y))
    have hs : cov.ricciAt ((extChartAt I x₀).symm y)
        (coordFieldW (I := I) x₀ μ ((extChartAt I x₀).symm y))
        (coordFieldW (I := I) x₀ ν ((extChartAt I x₀).symm y)) = ricciW (range I) (g.coordMetricW x₀) μ ν y := by
      rw [ricciAt_symm_provedW cov g h.1 h.2 _ _ _]
      exact ricciAt_coordW cov x₀ g h hy ν μ
    have hg : g.g ((extChartAt I x₀).symm y)
        (coordFieldW (I := I) x₀ μ ((extChartAt I x₀).symm y))
        (coordFieldW (I := I) x₀ ν ((extChartAt I x₀).symm y)) = g.coordMetricW x₀ y μ ν := by
      rw [coordField_applyW x₀ μ hy, coordField_applyW x₀ ν hy, g.coordMetric_eqW x₀ hy]
    unfold Connection.einsteinField at e
    rw [hs, scalarCurvatureAt_coordW cov x₀ g h hy, hg] at e
    unfold einsteinTensorW
    linarith
  · intro hvac
    refine ⟨h, fun p v w => ?_⟩
    set φ := extChartAt I p with hφ
    have hzs : p ∈ φ.source := mem_extChartAt_source p
    have hy : φ p ∈ φ.target := φ.map_source hzs
    have hp : p ∈ (tTrivW (I := I) (E := Fin n → ℝ) p).baseSet := by
      simpa [tTrivW, TangentBundle.trivializationAt_baseSet] using (mem_chart_source H p)
    have hvac' := hvac p (φ p) hy
    have hc : ∀ σ ν : Fin n, cov.ricciAt p (coordBasisW p hp σ) (coordBasisW p hp ν) -
        (cov.scalarCurvatureAt g p / 2 - Λ) * g.g p (coordBasisW p hp σ) (coordBasisW p hp ν) -
        κ * T p (coordBasisW p hp σ) (coordBasisW p hp ν) = 0 := by
      intro σ ν
      have e := hvac' σ ν
      have hr := ricciAt_coordW cov p g h hy σ ν
      have hs := scalarCurvatureAt_coordW cov p g h hy
      have hg := g_coordFieldW g p σ ν hy
      rw [hφ, (extChartAt I p).left_inv hzs] at hr hs hg e
      have hr' := ricciAt_coordW cov p g h hy ν σ
      rw [hφ, (extChartAt I p).left_inv hzs] at hr'
      have e1 : ∀ k, coordBasisW p hp k = coordFieldW (I := I) p k p := fun k =>
        (coordBasis_applyW p hp k).trans (symmL_eq_coordFieldW p hp k)
      rw [e1 σ, e1 ν]
      have hsym := ricciAt_symm_provedW cov g h.1 h.2 p (coordFieldW (I := I) p σ p) (coordFieldW (I := I) p ν p)
      rw [hr, hs, hg]
      have hrs : ricciW (range I) (g.coordMetricW p) ν σ (extChartAt I p p) =
          ricciW (range I) (g.coordMetricW p) σ ν (extChartAt I p p) := by
        rw [← hr, hsym, hr']
      unfold einsteinTensorW at e
      linarith
    set B : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
      RicBW cov p hp - (cov.scalarCurvatureAt g p / 2 - Λ) • (g.g p).toBilinForm - κ • (T p).toBilinForm with hB
    have hB0 : B = 0 := by
      refine LinearMap.BilinForm.ext_basis (coordBasisW p hp) fun σ ν => ?_
      have := hc σ ν
      simp only [hB, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
      show cov.ricciAt p _ _ - (cov.scalarCurvatureAt g p / 2 - Λ) * g.g p _ _ - κ * T p _ _ = 0
      linarith
    have := congrArg (fun B' => B' v w) hB0
    simp only [hB, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at this
    show cov.ricciAt p v w - cov.scalarCurvatureAt g p / 2 * g.g p v w + Λ * g.g p v w = κ * T p v w
    have h2 : (RicBW cov p hp) v w = cov.ricciAt p v w := rfl
    have h3 : ((g.g p).toBilinForm) v w = g.g p v w := rfl
    have h4 : ((T p).toBilinForm) v w = T p v w := rfl
    rw [h2, h3, h4] at this
    linarith
end Lightlike
