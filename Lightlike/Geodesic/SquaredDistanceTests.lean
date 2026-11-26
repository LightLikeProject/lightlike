import Mathlib
import Lightlike.Geodesic.SquaredDistance
import Lightlike.Spacetime.Curvature

/-!
# Tests: the world function and the eikonal equation

Non-vacuity: the hypotheses of `Lightlike.Geodesic.exists_sqDist_eikonal` are met by Minkowski space (a Lorentzian
coordinate metric on all of `ℝⁿ`), so the theorem is not restricted to Riemannian metrics. Trust check of the algebraic
step (`dotProduct_inv_mulVec_of_lower`): for the identity metric of `ℝ²` and `T = (1, 2)`, the gradient `c = 2T` has
`c · c = 20 = 4 |T|²`; the constant `2` in place of `4` (the eikonal equation of `σ/2` read as if it were `σ`) gives
`10 ≠ 20` and is caught.
-/

open Set Matrix
noncomputable section
namespace Lightlike.Geodesic.SquaredDistanceTests

/-- Non-vacuity: the hypotheses hold for Minkowski space, so a world function near `(0, 0)` with the eikonal equation
exists; its neighbourhood of the diagonal is open and contains `(0, 0)`. -/
example (n : ℕ) : ∃ W : Set ((Fin n → ℝ) × (Fin n → ℝ)), IsOpen W ∧ ((0 : Fin n → ℝ), (0 : Fin n → ℝ)) ∈ W := by
  obtain ⟨W, V, hW, h0, -⟩ := exists_sqDist_eikonal (minkowski_isCoordMetric (n := n) 0) (mem_univ 0)
  exact ⟨W, hW, h0⟩

/-- The identity metric of `ℝ²`. -/
def g1 : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun _ => 1

theorem isCoordMetric_g1 : Lightlike.IsCoordMetric g1 univ :=
  isCoordMetric_const (Matrix.transpose_one) (by show IsUnit (Matrix.det (1 : Matrix (Fin 2) (Fin 2) ℝ)); simp)

/-- Trust check: `c = 2T` with `T = (1, 2)` for the identity metric gives `c · g⁻¹ c = 20 = 4 g(T, T)`. -/
example : (![2, 4] : Fin 2 → ℝ) ⬝ᵥ ((g1 0)⁻¹ *ᵥ ![2, 4]) = 20 := by
  rw [dotProduct_inv_mulVec_of_lower isCoordMetric_g1 (mem_univ 0) ![1, 2] ![2, 4] (fun i => by
    fin_cases i <;> simp [pairing, g1, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num)]
  simp [pairing, g1, Fin.sum_univ_two, Matrix.one_apply]; norm_num

/-- The constant `2` in place of `4` is caught: `2 g(T, T) = 10 ≠ 20`. -/
example : 2 * pairing g1 0 ![1, 2] ![1, 2] ≠ 20 := by
  simp [pairing, g1, Fin.sum_univ_two, Matrix.one_apply]; norm_num

end Lightlike.Geodesic.SquaredDistanceTests
