import Lightlike.Canonical.FoliationSmooth
import Lightlike.Spacetime.LieMetric

/-!
# The extrinsic curvature is minus half the Lie derivative of the metric along the normal

For a time function `τ` and the Levi-Civita connection, on vectors tangent to the leaves,
`K(V, W) = −½ (ℒ_n g)(V, W)` (`extrinsicCurvature_eq_neg_half_lieDeriv`), with the Lie derivative
`Lightlike.lieDerivMetric` of `Lightlike/Spacetime/LieMetric.lean`. This is Gourgoulhon's
`K = −½ ℒ_n γ` (arXiv:gr-qc/0703035, Sec. 3.3.5, eq. (3.27), p. 45) evaluated on tangent vectors: there
`ℒ_n γ = ℒ_n g`, because `γ = g + n♭ ⊗ n♭` and `n♭` vanishes on tangent vectors.
-/

open Bundle Manifold Set Filter VectorField
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike.Canonical

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [T2Space M]

variable {g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M} {τ : M → ℝ}

/-- **`K = −½ ℒ_n g` on tangent vectors** (Gourgoulhon (3.27), `K = −½ ℒ_n γ`): for vector fields `V, W`
differentiable at `x` and tangent to the leaf there, `K(V, W) = −½ (ℒ_n g)(V, W)` at `x`. -/
theorem extrinsicCurvature_eq_neg_half_lieDeriv (h : IsTimeFunction g τ)
    {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} (hc : cov.IsLeviCivita g) {x : M}
    {V W : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y}
    (hV : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun y : M => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) x)
    (hW : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun y : M => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) x)
    (hVt : dTime τ x (V x) = 0) (hWt : dTime τ x (W x) = 0) :
    extrinsicCurvature g τ cov x (V x) (W x) = -(1 / 2) * Lightlike.lieDerivMetric g (unitNormal g τ) V W x := by
  have hn : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun y : M => (⟨y, unitNormal g τ y⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) x :=
    (contMDiffAt_unitNormal h x).mdifferentiableAt (by simp)
  rw [Lightlike.lieDerivMetric_eq_of_isLeviCivita hc hn hV hW]
  have hs := extrinsicCurvature_symm_of_timeFunction h hc x (V x) (W x)
  simp only [extrinsicCurvature, spatialProj_of_tangent h hVt, spatialProj_of_tangent h hWt,
    Hypersurface.secondFF] at hs ⊢
  rw [g.symm x (V x) (cov (unitNormal g τ) x (W x))]
  linarith

end Lightlike.Canonical
