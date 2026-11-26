import Lightlike.Spacetime.Corners.ChartAgreement
import Lightlike.Spacetime.LieMetric
import Lightlike.Spacetime.LeviCivita

/-!
# Constant curvature and maximal symmetry of a pseudo-Riemannian manifold

For a smooth symmetric nondegenerate metric `g` (`NondegMetric`, any signature) on a manifold `M` modelled on
`Fin n → ℝ` (any model with corners):

* `HasConstantCurvature g K`: for every locally smooth Levi-Civita connection, the curvature is
  `R(X, Y) Z = K (g(Y, Z) X - g(X, Z) Y)` at every point (the curvature of a maximally symmetric space,
  Carroll, *Lecture Notes on General Relativity*, eq. (3.191), with the sign convention of `curvatureAt`);
* `IsMaximallySymmetric g K`: constant curvature `K` and `n (n + 1) / 2` smooth Killing fields of the Levi-Civita
  connection that are linearly independent (at most that many exist on a connected manifold:
  `finrank_killingFieldSpace_le` for the model `𝓘(ℝ, Fin n → ℝ)`).
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 2 M]

/-- **Constant curvature `K`**: every locally smooth Levi-Civita connection of `g` has
`R(X, Y) Z = K (g(Y, Z) X - g(X, Z) Y)` at every point. -/
def HasConstantCurvature (g : NondegMetric I M) (K : ℝ) : Prop :=
  ∀ (cov : Connection I M) [LocallySmoothConnectionW cov], cov.IsLeviCivita g →
    ∀ (x : M) (X Y Z : TangentSpace I x),
      cov.curvatureAt x X Y Z = K • (g.g x Y Z • X - g.g x X Z • Y)

/-- **Maximally symmetric with curvature `K`**: constant curvature `K`, and `n (n + 1) / 2` smooth vector fields
that are Killing for the Levi-Civita connection `leviCivita g` and linearly independent. -/
def IsMaximallySymmetric (g : NondegMetric I M) (K : ℝ) : Prop :=
  HasConstantCurvature g K ∧
    ∃ Y : Fin (n * (n + 1) / 2) → Π p : M, TangentSpace I p,
      (∀ i, ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
          (fun q : M => (⟨q, Y i q⟩ : TangentBundle I M)) ∧
        ∀ p, IsKillingAt (leviCivita g) g (Y i) p) ∧
      LinearIndependent ℝ Y

end Lightlike
