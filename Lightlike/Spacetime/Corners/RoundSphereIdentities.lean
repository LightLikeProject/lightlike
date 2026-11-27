import Mathlib
import Lightlike.Spacetime.RoundSphereTwoCurvature
import Lightlike.Spacetime.Corners.CurvatureSymmetries
import Lightlike.Spacetime.Corners.BianchiSecond
import Lightlike.Spacetime.Corners.DivergenceFree

/-!
# The identities of the Corners layer on the round 2-sphere

The round 2-sphere `S²` of radius `r` (Mathlib's unit sphere with the metric `r² h`, modelled on `Fin 2 → ℝ`, see
`RoundSphereTwo.lean`) is a Riemannian example for the curvature identities proved for any non-degenerate metric on a
manifold with corners: at every point, for every locally smooth Levi-Civita connection of `roundMetric2I r hr`, the first and
second Bianchi identities, the pair symmetry of the lowered curvature, the symmetry of the Ricci tensor and the vanishing
divergence of the Einstein tensor (`roundSphere2_identities`), together with the scalar curvature `2 / r²` of
`roundSphere2_scalarCurvatureAt`.

The identities themselves are the theorems of `CurvatureSymmetries.lean`, `BianchiSecond.lean` and `DivergenceFree.lean`,
applied to this metric; the example shows that the hypotheses are met by a compact Riemannian manifold, where all the
quantities are nonzero (the scalar curvature is `2 / r² ≠ 0`).

**Differences from the cited statement** (comparison with Lee, *Introduction to Riemannian Manifolds*, ch. 7, pending):
the sphere of radius `r` is the unit sphere of Mathlib with the metric `r² h` (isometric to it), `r ≠ 0`.
-/

open Manifold Bundle
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

section Identities

variable (r : ℝ) (hr : r ≠ 0) (cov : Connection I2 S2) [LocallySmoothConnectionW cov]

/-- **The identities of the Corners layer on the round 2-sphere**: at every point, for a locally smooth Levi-Civita connection
of `roundMetric2I r hr`, the first and second Bianchi identities, the pair symmetry, the symmetry of the Ricci tensor and
the vanishing divergence of the Einstein tensor. -/
theorem roundSphere2_identities (h : cov.IsLeviCivita (roundMetric2I r hr)) (x : S2) :
    (∀ X Y Z : TangentSpace I2 x,
      cov.curvatureAt x X Y Z + cov.curvatureAt x Y Z X + cov.curvatureAt x Z X Y = 0) ∧
    (∀ X Y Z W : TangentSpace I2 x,
      cov.riemannLowerAt (roundMetric2I r hr) x X Y Z W = cov.riemannLowerAt (roundMetric2I r hr) x Z W X Y) ∧
    (∀ Y Z : TangentSpace I2 x, cov.ricciAt x Y Z = cov.ricciAt x Z Y) ∧
    (∀ X Y Z W : TangentSpace I2 x,
      cov.covDerivCurvatureAt x X Y Z W + cov.covDerivCurvatureAt x Y Z X W +
        cov.covDerivCurvatureAt x Z X Y W = 0) ∧
    (∀ w : TangentSpace I2 x,
      cov.divBilinAt (roundMetric2I r hr) (cov.einsteinField (roundMetric2I r hr)) x w = 0) :=
  ⟨fun X Y Z => bianchi_first_provedW cov h.1 x X Y Z,
    fun X Y Z W => riemannLowerAt_pair_symmW cov (roundMetric2I r hr) h.1 h.2 x X Y Z W,
    fun Y Z => ricciAt_symm_provedW cov (roundMetric2I r hr) h.1 h.2 x Y Z,
    fun X Y Z W => bianchi_second_provedW cov h.1 x X Y Z W,
    fun w => einstein_divergence_free_provedW (roundMetric2I r hr) cov x h w⟩

end Identities

end Lightlike
