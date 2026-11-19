import Lightlike.Spacetime.EHManifold.IntrinsicIntegrand
import Lightlike.Spacetime.EHManifold.PerturbationAlgebra

/-!
# The integrand `⟨G + Λ g, h⟩_g` is linear over functions in `h`

`ehIntegrand_smulFun`: `⟨G + Λ g, χ h⟩_g = χ ⟨G + Λ g, h⟩_g` for a smooth function `χ`.

Supporting lemma for cutting a perturbation into pieces with a partition of unity; no catalogue entry.
-/

open Bundle Manifold Set Matrix
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

/-- The contraction is homogeneous in its last argument. -/
lemma formContract_smul_right {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Module.Basis (Fin n) ℝ V) (g A B : LinearMap.BilinForm ℝ V) (r : ℝ) :
    formContract b g A (r • B) = r * formContract b g A B := by
  unfold formContract
  rw [map_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]

/-- **The integrand is linear over functions in the perturbation.** -/
theorem ehIntegrand_smulFun (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ χ) (Λ : ℝ) (p : M) :
    ehIntegrand g (h.smulFun χ hχ) Λ p = χ p * ehIntegrand g h Λ p := by
  have hB : ((h.smulFun χ hχ).h p).toBilinForm = χ p • (h.h p).toBilinForm :=
    LinearMap.ext₂ fun u v => rfl
  unfold ehIntegrand
  rw [hB, formContract_smul_right]

end Lightlike
