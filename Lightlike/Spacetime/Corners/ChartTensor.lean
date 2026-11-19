import Lightlike.Spacetime.BianchiSecond
import Lightlike.Spacetime.ChartAgreement
import Lightlike.Spacetime.Corners.ChartAgreement
import Lightlike.Spacetime.RiemannSymmetry
import Lightlike.Spacetime.RiemannSymmetryWithin
import Lightlike.Spacetime.CurvatureWithin
import Lightlike.GR.Einstein
import Lightlike.Spacetime.Corners.ChartCovariant
/-!
# Tensoriality of covariant derivatives of bilinear fields, in a chart (step 1 of the divergence-free Einstein tensor)

For a bilinear form field with components `B̂ : M → E →L E →L ℝ` in the tangent trivialization at `x₀`, the
covariant derivative `(∇_X B)(v, w)` is given by the components formula
`D B̂ (X) (v, w) - B̂ (Γ̂(v, X), w) - B̂ (v, Γ̂(w, X))` (`covDerivBilinAt_bilOf`). It is therefore independent of the
extensions of `v, w` and trilinear. Applied to the coordinate components of the Einstein tensor of a Levi-Civita
connection (`covDerivBilinAt_einstein`). Also: smoothness of the coordinate Riemann, Ricci, scalar curvature and Einstein
tensors on the domain of a coordinate metric.

**Limits.** Manifold with corners (any `ModelWithCorners`); the coordinate Einstein tensor is differentiated within `range I`; locally smooth connection and `C²` structure. No statement
about the divergence yet; this is a supporting layer for `T-GE1-P8`, which stays open.

This is the Corners layer of the CO30 branch: the versions for any model with corners of the declarations of
`Lightlike/Spacetime/ChartTensor.lean` that the CO30 and GE11 files use, with a `W` suffix where the boundaryless file owns the name.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology
noncomputable section
namespace Lightlike
section Coord
variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The Riemann tensor within `S` is smooth on the domain of a coordinate metric. -/
theorem IsCoordMetricW.contDiffOn_riemannW {S : Set (Fin n → ℝ)} (hg : IsCoordMetricW S g U) (ρ σ μ ν : Fin n) :
    ContDiffOn ℝ ∞ (riemannW S g ρ σ μ ν) U := by
  have hΓ := hg.contDiffOn_christoffel
  unfold riemannW
  refine ContDiffOn.add (ContDiffOn.sub (hg.contDiffOn_pdW (hΓ _ _ _) _) (hg.contDiffOn_pdW (hΓ _ _ _) _)) ?_
  exact ContDiffOn.sum fun l _ => ((hΓ _ _ _).mul (hΓ _ _ _)).sub ((hΓ _ _ _).mul (hΓ _ _ _))

/-- The Ricci tensor within `S` is smooth on the domain of a coordinate metric. -/
theorem IsCoordMetricW.contDiffOn_ricciW {S : Set (Fin n → ℝ)} (hg : IsCoordMetricW S g U) (σ ν : Fin n) :
    ContDiffOn ℝ ∞ (ricciW S g σ ν) U := by
  unfold ricciW
  exact ContDiffOn.sum fun ρ _ => hg.contDiffOn_riemannW ρ σ ρ ν

/-- The scalar curvature within `S` is smooth on the domain of a coordinate metric. -/
theorem IsCoordMetricW.contDiffOn_scalarCurvatureW {S : Set (Fin n → ℝ)} (hg : IsCoordMetricW S g U) :
    ContDiffOn ℝ ∞ (scalarCurvatureW S g) U := by
  unfold scalarCurvatureW
  exact ContDiffOn.sum fun σ _ => ContDiffOn.sum fun ν _ =>
    (hg.contDiffOn_inv σ ν).mul (hg.contDiffOn_ricciW σ ν)

end Coord
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 2 M] [CompleteSpace E]
variable (cov : Connection I M) [LocallySmoothConnectionW cov] (x₀ : M)

section Einstein
set_option synthInstance.maxHeartbeats 400000
variable {n : ℕ} {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 2 M]
  (g : NondegMetric I M)

variable (cov : Connection I M) [LocallySmoothConnectionW cov]

end Einstein
end Lightlike
