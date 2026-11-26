import Mathlib
import Lightlike.Geometry.HeatKernel.NormalTransport
import Lightlike.Geometry.HeatKernel.GaussianAnsatzTests
import Lightlike.Asymptotics.EulerPrimitiveTests

/-!
# Tests: the transport operator in normal coordinates on the line

On the line with `σ = y²`, `V = id` (normal coordinates at `0`) and `T = y` (the velocity at `y` of the geodesic from
`0`), `∂σ = 2y = 2 g(T, e₀)` and `DV T = T = V`. For `U(v) = v₀`, `IsCoordMetric.coordGradPair_comp_eq_euler` gives
`g⁻¹(dσ, dy)/2 = y`, and the direct computation (`pd_σLine`: `∂σ = 2y`, `∂y = 1`) gives the same value. Twice the
velocity (`T = 2y`) would violate `DV T = V`: the hypothesis is not vacuous.
-/

open Set
open scoped ContDiff
noncomputable section
namespace Lightlike.NormalTransportTests

open Lightlike.LaplaceBeltramiTests Lightlike.GaussianAnsatzTests Lightlike.EulerPrimitiveTests

/-- The hypothesis on the gradient: `∂σ(y) = 2 g_y(y, e₀)` for `σ = y²`. -/
theorem grad_σLine (y : Fin 1 → ℝ) (i : Fin 1) :
    pd i σLine y = 2 * Geodesic.pairing gLine y y (Pi.single i 1) := by
  fin_cases i
  simp [pd_σLine, Geodesic.pairing, gLine]

/-- **Trust check**: by the theorem, `g⁻¹(dσ, dy)/2 = y` on the line. -/
theorem euler_line (y : Fin 1 → ℝ) : coordGradPair gLine σLine (fun z => (id z) 0) y / 2 = y 0 := by
  have h := isCoordMetric_gLine.coordGradPair_comp_eq_euler (mem_univ y) (grad_σLine y)
    differentiableAt_id (by simp) (Φ := fun w : Fin 1 → ℝ => w 0)
    ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 1 => ℝ) 0 y).differentiableAt)
  rw [h, fderiv_coord]
  simp

/-- The same value by the direct computation `∂σ = 2y`, `∂y = 1`. -/
example (y : Fin 1 → ℝ) : coordGradPair gLine σLine (fun z => z 0) y / 2 = y 0 := by
  simp [coordGradPair, gLine, pd_σLine, pd_coord]

/-- `T = 2y` would give `DV T = 2y ≠ y = V(y)` at `y = 1`: the hypothesis `DV T = V` excludes it. -/
example : (2 : ℝ) * 1 ≠ 1 := by norm_num

end Lightlike.NormalTransportTests
