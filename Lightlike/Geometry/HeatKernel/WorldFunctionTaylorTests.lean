import Mathlib
import Lightlike.Geometry.HeatKernel.WorldFunctionTaylor
import Lightlike.Geometry.HeatKernel.WorldFunctionBoundsTests

/-!
# Tests: the world function to third order

Non-vacuity on the flat line with `V(p, y) = y − p` (for which `V − (y − p) = 0` exactly, so the second-order bound
holds with room): `exists_norm_V_sub_le` and `exists_abs_pairing_sub_le` apply.
-/

open Set
open scoped ContDiff
noncomputable section
namespace Lightlike.WorldFunctionTaylorTests

open Lightlike.LaplaceBeltramiTests Lightlike.WorldFunctionBoundsTests

/-- Non-vacuity of the second-order bound for normal coordinates. -/
example : ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ p y : Fin 1 → ℝ, ‖p - 0‖ < r → ‖y - 0‖ < r →
    ‖Vline (p, y) - (y - p)‖ ≤ C * ‖y - p‖ ^ 2 :=
  exists_norm_V_sub_le isOpen_univ (by unfold Vline; fun_prop) (mem_univ _) (fun p _ => by simp [Vline])
    (fun p _ => hasFDerivAt_Vline p)

/-- Non-vacuity of the third-order bound for the world function. -/
example : ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ p y : Fin 1 → ℝ, ‖p - 0‖ < r → ‖y - 0‖ < r →
    |Geodesic.pairing gLine p (Vline (p, y)) (Vline (p, y)) - Geodesic.pairing gLine p (y - p) (y - p)| ≤
      C * ‖y - p‖ ^ 3 :=
  exists_abs_pairing_sub_le isCoordMetric_gLine isOpen_univ (by unfold Vline; fun_prop) (mem_univ _) (mem_univ _)
    (fun p _ => by simp [Vline]) (fun p _ => hasFDerivAt_Vline p)

/-- For `V = y − p` the error is exactly `0`. -/
example (p y : Fin 1 → ℝ) : ‖Vline (p, y) - (y - p)‖ = 0 := by simp [Vline]

end Lightlike.WorldFunctionTaylorTests
