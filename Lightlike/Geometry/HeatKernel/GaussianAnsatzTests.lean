import Mathlib
import Lightlike.Geometry.HeatKernel.GaussianAnsatz
import Lightlike.Spacetime.LaplaceBeltrami.Tests

/-!
# Tests: the Gaussian ansatz on the line

On the line with its flat metric, `σ(y) = y²` satisfies the eikonal equation `g⁻¹(dσ, dσ) = (2y)² = 4σ`, so
`Lightlike.heatOperator_gaussian_ansatz` applies (non-vacuity). For `u ≡ 1` the `1/t` coefficient
`g⁻¹(dσ, du)/2 - (Δσ/4 + n/2) u` is `0 - (-2/4 + 1/2) = 0`: the free heat kernel `(4πt)^{-1/2} e^{-y²/4t}` solves the
heat equation, with `u₀ = 1`. With the opposite sign convention for the Laplacian (`Δσ = +2`) the coefficient would be
`-1 ≠ 0`: caught.
-/

open Set
open scoped ContDiff
noncomputable section
namespace Lightlike.GaussianAnsatzTests

open Lightlike.LaplaceBeltramiTests

/-- The squared coordinate of the line. -/
def σLine : (Fin 1 → ℝ) → ℝ := fun w => w 0 * w 0

theorem pd_σLine (z : Fin 1 → ℝ) : pd 0 σLine z = 2 * z 0 := by
  have h := pd_mul (f₁ := fun w : Fin 1 → ℝ => w 0) (f₂ := fun w : Fin 1 → ℝ => w 0)
    ((hasFDerivAt_apply (𝕜 := ℝ) 0 z).differentiableAt) ((hasFDerivAt_apply (𝕜 := ℝ) 0 z).differentiableAt) 0
  rw [show σLine = fun w : Fin 1 → ℝ => w 0 * w 0 from rfl, h, pd_coord]
  ring

/-- **The eikonal equation for `y²` on the line.** -/
theorem eikonal_σLine : coordGradPair gLine σLine σLine = fun y => 4 * σLine y := by
  funext y
  simp [coordGradPair, gLine, pd_σLine, σLine]
  ring

/-- **The transport coefficient of the free heat kernel vanishes** (`u ≡ 1`, `n = 1`). -/
theorem transport_free (y : Fin 1 → ℝ) :
    coordGradPair gLine σLine (fun _ => 1) y / 2 - (coordLaplacian gLine σLine y / 4 + (1 : ℕ) / 2) * 1 = 0 := by
  rw [show σLine = fun w : Fin 1 → ℝ => w 0 * w 0 from rfl, coordLaplacian_gLine_sq]
  simp [coordGradPair, pd_const]
  norm_num

/-- The opposite sign convention (`Δσ = +2`) would leave `-1 ≠ 0`: caught. -/
example : (0 : ℝ) / 2 - ((2 : ℝ) / 4 + (1 : ℕ) / 2) * 1 ≠ 0 := by norm_num

/-- Non-vacuity of `heatOperator_gaussian_ansatz`: its hypotheses hold on the line for `σ = y²`, `u ≡ 1`. -/
example (t : ℝ) (ht : 0 < t) (y : Fin 1 → ℝ) :
    ∃ D, HasDerivAt (fun s => heatGaussian 1 (σLine y) s * (fun _ _ => (1 : ℝ)) s y) D t ∧
      D + (4 * Real.pi * t) ^ (-((1 : ℕ) : ℝ) / 2) *
          coordLaplacian gLine (fun z => gaussFactor t (σLine z) * (fun _ _ => (1 : ℝ)) t z) y =
        heatGaussian 1 (σLine y) t * (0 + coordLaplacian gLine ((fun _ _ => (1 : ℝ)) t) y +
          (coordGradPair gLine σLine ((fun _ _ => (1 : ℝ)) t) y / 2 -
            (coordLaplacian gLine σLine y / 4 + (1 : ℕ) / 2) * (fun _ _ => (1 : ℝ)) t y) / t) :=
  heatOperator_gaussian_ansatz isCoordMetric_gLine
    ((contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).mul (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0)).contDiffOn
    (fun _ => contDiffOn_const) eikonal_σLine ht (mem_univ y) (hasDerivAt_const t 1)

end Lightlike.GaussianAnsatzTests
