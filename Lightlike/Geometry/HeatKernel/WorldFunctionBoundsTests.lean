import Mathlib
import Lightlike.Geometry.HeatKernel.WorldFunctionBounds
import Lightlike.Spacetime.LaplaceBeltrami.Tests

/-!
# Tests: bounds for normal coordinates and the world function

On the flat line, `V(p, y) = y − p` has `V(p, p) = 0` and derivative the identity in `y`, so the hypotheses of
`exists_norm_sub_le_two_mul_norm` and `exists_pairing_lower` hold (non-vacuity); for this `V` the bi-Lipschitz bound
`‖y − p‖ ≤ 2‖V(p, y)‖` holds with room (`‖V‖ = ‖y − p‖`).
-/

open Set
open scoped ContDiff
noncomputable section
namespace Lightlike.WorldFunctionBoundsTests

open Lightlike.LaplaceBeltramiTests

/-- The velocity map of the flat line. -/
def Vline : (Fin 1 → ℝ) × (Fin 1 → ℝ) → (Fin 1 → ℝ) := fun q => q.2 - q.1

theorem hasFDerivAt_Vline (p : Fin 1 → ℝ) :
    HasFDerivAt (fun y => Vline (p, y)) (ContinuousLinearMap.id ℝ (Fin 1 → ℝ)) p := by
  simpa [Vline] using (hasFDerivAt_id (𝕜 := ℝ) p).sub_const p

/-- Non-vacuity of the bi-Lipschitz bound. -/
example : ∃ r > 0, ∀ p y : Fin 1 → ℝ, ‖p - 0‖ < r → ‖y - 0‖ < r →
    (p, y) ∈ (univ : Set ((Fin 1 → ℝ) × (Fin 1 → ℝ))) ∧ ‖y - p‖ ≤ 2 * ‖Vline (p, y)‖ :=
  exists_norm_sub_le_two_mul_norm isOpen_univ (by unfold Vline; fun_prop) (mem_univ _)
    (fun p _ => by simp [Vline]) (fun p _ => hasFDerivAt_Vline p)

/-- Non-vacuity of the Gaussian lower bound, for the flat (Riemannian) metric of the line. -/
example : ∃ r c : ℝ, 0 < r ∧ 0 < c ∧ ∀ p y : Fin 1 → ℝ, ‖p - 0‖ < r → ‖y - 0‖ < r →
    c * ‖y - p‖ ^ 2 ≤ Geodesic.pairing gLine p (Vline (p, y)) (Vline (p, y)) :=
  exists_pairing_lower (U := univ)
    ⟨⟨isOpen_univ, isCoordMetric_gLine.symm, isCoordMetric_gLine.isUnit_det, isCoordMetric_gLine.smooth⟩,
      fun _ _ => Matrix.PosDef.one⟩ isOpen_univ
    (by unfold Vline; fun_prop) (mem_univ _) (mem_univ _) (fun p _ => by simp [Vline])
    (fun p _ => hasFDerivAt_Vline p)

end Lightlike.WorldFunctionBoundsTests
