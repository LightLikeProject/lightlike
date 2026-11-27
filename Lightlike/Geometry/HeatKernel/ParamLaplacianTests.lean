import Mathlib
import Lightlike.Geometry.HeatKernel.ParamLaplacian
import Lightlike.Spacetime.LaplaceBeltrami.Tests

/-!
# Tests: the Laplacian with a parameter

For `F(p, y) = p₀ · y₀` on `ℝ × ℝ` (parameter `p`, line `y`), the partial derivative in `y` is `p₀`
(`pdY_example`, through `pd_eq_pdY`; the partial derivative in `p`, `y₀`, would be the wrong slot), and
`(p, y) ↦ Δ_y (p₀ · y₀²)` is jointly smooth (non-vacuity of `IsCoordMetric.contDiffOn_coordLaplacian_param`).
-/

open Set
open scoped ContDiff
noncomputable section
namespace Lightlike.ParamLaplacianTests

open Lightlike.LaplaceBeltramiTests

/-- `∂_y (p₀ y₀) = p₀`. -/
theorem pdY_example (q : (Fin 1 → ℝ) × (Fin 1 → ℝ)) :
    pdY 0 (fun r : (Fin 1 → ℝ) × (Fin 1 → ℝ) => r.1 0 * r.2 0) q = q.1 0 := by
  rw [← pd_eq_pdY isOpen_univ (by fun_prop) (mem_univ q)]
  rw [pd_const_mul _ ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 1 => ℝ) 0 q.2).differentiableAt), pd_coord]
  ring

/-- Non-vacuity: `(p, y) ↦ Δ_y(p₀ y₀²)` is smooth. -/
example : ContDiffOn ℝ ∞ (fun q : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
    coordLaplacian gLine (fun y => q.1 0 * (y 0 * y 0)) q.2) univ :=
  isCoordMetric_gLine.contDiffOn_coordLaplacian_param isOpen_univ (fun _ _ => mem_univ _)
    (F := fun r : (Fin 1 → ℝ) × (Fin 1 → ℝ) => r.1 0 * (r.2 0 * r.2 0)) (by fun_prop)

end Lightlike.ParamLaplacianTests
