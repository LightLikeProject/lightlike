import Mathlib
import Lightlike.Spacetime.Corners.RicciTransport

/-!
# The curvature in a chart for a model transported to `Fin n → ℝ`

For `e : E ≃L[ℝ] (Fin n → ℝ)` (a choice of coordinates on the finite-dimensional model space `E`), the charts `e ∘ extChartAt I x₀` are the charts of the
model `I.transContinuousLinearEquiv e`. The intrinsic Ricci tensor, scalar curvature and Einstein equations of `cov` and `g` agree in these
charts with the coordinate ones (`ricciAt_coord_trans`, `scalarCurvatureAt_coord_trans`, `satisfiesEinstein_iff_chart_trans`), by the theorems of
`ChartAgreement.lean` for the transported connection and metric.
-/

open Bundle Manifold Set VectorField Filter
open scoped Manifold ContDiff Topology
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

section
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 2 M]
  (e : E ≃L[ℝ] (Fin n → ℝ)) (cov : Connection I M) [LocallySmoothConnectionW cov]

/-- **The Einstein equations are the same for the transported connection and metric.** -/
theorem satisfiesEinstein_trans_iff (g : NondegMetric I M) (h : cov.IsLeviCivita g) (Λ : ℝ) :
    g.SatisfiesEinstein cov Λ ↔ (transMetric e g).SatisfiesEinstein (transCov e cov) Λ := by
  have := locallySmoothConnectionW_transCov e cov
  constructor
  · rintro ⟨hLC, hE⟩
    refine ⟨isLeviCivita_trans e cov g hLC, fun x v w => ?_⟩
    have h1 := hE x (e.symm v) (e.symm w)
    have hr := ricciAt_trans e cov x (e.symm v) (e.symm w)
    erw [e.apply_symm_apply, e.apply_symm_apply] at hr
    rw [hr, scalarCurvatureAt_trans e cov g x]
    exact h1
  · rintro ⟨-, hE'⟩
    refine ⟨h, fun x v w => ?_⟩
    have h1 := hE' x (e v) (e w)
    have hr := ricciAt_trans e cov x v w
    have hg : ((transMetric e g).g x) (e v) (e w) = g.g x v w := by
      show (g.g x (e.symm (e v))) (e.symm (e w)) = _
      erw [e.symm_apply_apply, e.symm_apply_apply]
    rw [hr, scalarCurvatureAt_trans e cov g x, hg] at h1
    exact h1

/-- **The Einstein equations on a manifold with corners modelled on any finite-dimensional space are the coordinate vacuum equations in every
chart `e ∘ extChartAt I x₀`.** -/
theorem satisfiesEinstein_iff_chart_trans (g : NondegMetric I M) (h : cov.IsLeviCivita g) (Λ : ℝ) :
    g.SatisfiesEinstein cov Λ ↔
      ∀ x₀ : M, IsVacuumSolutionW (range (I.transContinuousLinearEquiv e)) Λ
        ((transMetric e g).coordMetricW x₀) (extChartAt (I.transContinuousLinearEquiv e) x₀).target := by
  have := locallySmoothConnectionW_transCov e cov
  exact (satisfiesEinstein_trans_iff e cov g h Λ).trans
    (satisfiesEinstein_iff_chart_provedW (transCov e cov) (transMetric e g) (isLeviCivita_trans e cov g h) Λ)

/-- **The scalar curvature in a chart is the coordinate scalar curvature**, for any finite-dimensional model space. -/
theorem scalarCurvatureAt_coord_trans (g : NondegMetric I M) (h : cov.IsLeviCivita g) (x₀ : M)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt (I.transContinuousLinearEquiv e) x₀).target) :
    cov.scalarCurvatureAt g ((extChartAt (I.transContinuousLinearEquiv e) x₀).symm y) =
      scalarCurvatureW (range (I.transContinuousLinearEquiv e)) ((transMetric e g).coordMetricW x₀) y := by
  have := locallySmoothConnectionW_transCov e cov
  rw [← scalarCurvatureAt_trans e cov g]
  exact scalarCurvatureAt_coordW (transCov e cov) x₀ (transMetric e g) (isLeviCivita_trans e cov g h) hy

/-- **The Ricci tensor in a chart is the coordinate Ricci tensor**, for any finite-dimensional model space: the coordinate vectors are
the vectors `e⁻¹ ∂_ν` of the model space. -/
theorem ricciAt_coord_trans (g : NondegMetric I M) (h : cov.IsLeviCivita g) (x₀ : M)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt (I.transContinuousLinearEquiv e) x₀).target) (ν ζ : Fin n) :
    cov.ricciAt ((extChartAt (I.transContinuousLinearEquiv e) x₀).symm y)
      (e.symm (coordFieldW (I := I.transContinuousLinearEquiv e) x₀ ν
        ((extChartAt (I.transContinuousLinearEquiv e) x₀).symm y)))
      (e.symm (coordFieldW (I := I.transContinuousLinearEquiv e) x₀ ζ
        ((extChartAt (I.transContinuousLinearEquiv e) x₀).symm y))) =
      ricciW (range (I.transContinuousLinearEquiv e)) ((transMetric e g).coordMetricW x₀) ζ ν y := by
  have := locallySmoothConnectionW_transCov e cov
  have h1 := ricciAt_coordW (transCov e cov) x₀ (transMetric e g) (isLeviCivita_trans e cov g h) hy ν ζ
  have h2 := ricciAt_trans e cov ((extChartAt (I.transContinuousLinearEquiv e) x₀).symm y)
    (e.symm (coordFieldW (I := I.transContinuousLinearEquiv e) x₀ ν
        ((extChartAt (I.transContinuousLinearEquiv e) x₀).symm y)))
    (e.symm (coordFieldW (I := I.transContinuousLinearEquiv e) x₀ ζ
        ((extChartAt (I.transContinuousLinearEquiv e) x₀).symm y)))
  erw [e.apply_symm_apply, e.apply_symm_apply] at h2
  exact h2.symm.trans h1

/-- **The curvature in a chart is the coordinate Riemann tensor**, for any finite-dimensional model space. -/
theorem riemann_coord_trans (g : NondegMetric I M) (h : cov.IsLeviCivita g) (x₀ : M)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt (I.transContinuousLinearEquiv e) x₀).target) (μ ν σ ρ : Fin n) :
    (hvW (I := I.transContinuousLinearEquiv e) x₀ ((extChartAt (I.transContinuousLinearEquiv e) x₀).symm y)
      (e (cov.curvatureAt ((extChartAt (I.transContinuousLinearEquiv e) x₀).symm y)
        (e.symm (coordFieldW (I := I.transContinuousLinearEquiv e) x₀ μ
          ((extChartAt (I.transContinuousLinearEquiv e) x₀).symm y)))
        (e.symm (coordFieldW (I := I.transContinuousLinearEquiv e) x₀ ν
          ((extChartAt (I.transContinuousLinearEquiv e) x₀).symm y)))
        (e.symm (coordFieldW (I := I.transContinuousLinearEquiv e) x₀ σ
          ((extChartAt (I.transContinuousLinearEquiv e) x₀).symm y)))))) ρ =
      riemannW (range (I.transContinuousLinearEquiv e)) ((transMetric e g).coordMetricW x₀) ρ σ μ ν y := by
  have := locallySmoothConnectionW_transCov e cov
  have h1 := riemann_coord_compW (transCov e cov) x₀ (transMetric e g) (isLeviCivita_trans e cov g h) hy μ ν σ ρ
  have h2 := curvatureAt_trans e cov ((extChartAt (I.transContinuousLinearEquiv e) x₀).symm y)
    (e.symm (coordFieldW (I := I.transContinuousLinearEquiv e) x₀ μ
        ((extChartAt (I.transContinuousLinearEquiv e) x₀).symm y)))
    (e.symm (coordFieldW (I := I.transContinuousLinearEquiv e) x₀ ν
        ((extChartAt (I.transContinuousLinearEquiv e) x₀).symm y)))
    (e.symm (coordFieldW (I := I.transContinuousLinearEquiv e) x₀ σ
        ((extChartAt (I.transContinuousLinearEquiv e) x₀).symm y)))
  erw [e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply] at h2
  rw [← h2]
  exact h1

end

end Lightlike
