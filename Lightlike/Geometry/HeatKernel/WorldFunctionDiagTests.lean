import Mathlib
import Lightlike.Geometry.HeatKernel.WorldFunctionDiag
import Lightlike.Spacetime.LaplaceBeltrami.Tests

/-!
# Tests: the Laplacian of the world function on the diagonal

On the line with its flat metric and `V = id` (the velocity of the geodesic from `p` to `y` is `y − p`; at `p = 0` it
is `y`), `IsCoordMetric.coordLaplacian_pairing_diag` gives `Δ(y²)(0) = −2`, and the direct computation
`LaplaceBeltramiTests.coordLaplacian_gLine_sq` (product rule, `Δy = 0`, `|dy|² = 1`) gives the same value: two
independent routes agree. A velocity with derivative `2·id` would give `σ = 4y²` and `Δσ = −8 ≠ −2`: the hypothesis
`DV(p) = id` is needed.
-/

open Set
open scoped ContDiff
noncomputable section
namespace Lightlike.WorldFunctionDiagTests

open Lightlike.LaplaceBeltramiTests

theorem diag_line : coordLaplacian gLine (fun y => ∑ a, ∑ b, y a * (gLine 0 a b * y b)) 0 = -2 := by
  have h := isCoordMetric_gLine.coordLaplacian_pairing_diag (p := 0) (mem_univ 0) (V := id)
    (fun a => (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) a).contDiffOn) rfl (hasFDerivAt_id 0)
  simpa using h

/-- The two routes agree: the same function is `y ↦ y₀ · y₀`. -/
example : coordLaplacian gLine (fun y => ∑ a, ∑ b, y a * (gLine 0 a b * y b)) 0 =
    coordLaplacian gLine (fun w => w 0 * w 0) 0 := by
  rw [diag_line, coordLaplacian_gLine_sq]

/-- `DV = 2·id` would give `Δσ = 4 · (−2) = −8`, not `−2n = −2`. -/
example : (4 : ℝ) * -2 ≠ -2 * (1 : ℕ) := by norm_num

end Lightlike.WorldFunctionDiagTests
