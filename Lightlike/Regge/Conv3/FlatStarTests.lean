import Lightlike.Regge.Conv3.FlatStarJet

/-!
# Trust checks for the star identity at a point with vanishing metric gradient

* The hypotheses of `jetStarCore_of_flat` are met by the Euclidean metric, so the theorem is not
  vacuous (`euclid_flat_core`).
* For the second derivatives of a round 3-sphere in a chart with vanishing gradient at the centre
  (`g_ii = 1 - ½ Σ_{k ≠ i} x_k²` to second order, scalar curvature `6`), the sum over the 36 incidences
  is `3 = det R / 2`, not `0` and not `6` (`sphere_sum`, `sphere_sum_ne_double`). So the identity
  is not `0 = 0`, and a wrong factor in the curvature side is detected.
-/

open Real Matrix Lightlike
namespace Lightlike.Regge.Conv3
open Lightlike.Geodesic

/-- Non-vacuity: the Euclidean metric has vanishing first derivatives everywhere, so
`jetStarCore_of_flat` applies to it. -/
theorem euclid_flat_core (m : Fin 3 → ℝ) : JetStarCore (euclid : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) m :=
  jetStarCore_of_flat (isRiemMetric_euclid isOpen_univ) (Set.mem_univ m)
    (fun k i j => by simp [euclid, pd])

/-- The second derivatives `∂_l ∂_k g_ij` of a metric of constant positive curvature in a chart with
vanishing gradient at the origin: `-1` when `k = l ≠ i = j`. -/
def sphereDD : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun k l i j => if k = l ∧ i = j ∧ k ≠ i then -1 else 0

/-- The Euclidean Gram matrix. -/
def idG : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then 1 else 0

theorem sphere_Rnum : Rnum idG sphereDD = 3 := by
  simp [Rnum, idG, sphereDD, Matrix.adjugate_fin_three, Fin.sum_univ_three]
  norm_num

/-- **The identity is not `0 = 0`:** for the sphere-like second derivatives the sum over the 36
incidences is `3`. -/
theorem sphere_sum : ∑ σ : Fin 6, ∑ h : Fin 6, Einc (lenQ idG σ h) (lenR sphereDD σ h) = 3 := by
  have hdet : (Matrix.of idG).det = 1 := by
    simp [idG, Matrix.det_fin_three]
  have := flat_star_identity idG sphereDD
    (fun i j => by fin_cases i <;> fin_cases j <;> simp [idG])
    (fun k l i j => by
      fin_cases k <;> fin_cases l <;> fin_cases i <;> fin_cases j <;> simp [sphereDD])
    (fun k l i j => by
      fin_cases k <;> fin_cases l <;> fin_cases i <;> fin_cases j <;> simp [sphereDD])
    (by norm_num [idG]) (by norm_num [idG]) (by norm_num [idG]) (by norm_num [idG])
    (by norm_num [idG]) (by norm_num [idG]) (by rw [hdet]; norm_num)
  rw [this, hdet, sphere_Rnum]; norm_num

/-- **Wrong-model control:** the sum is not twice `det R / 2`. -/
theorem sphere_sum_ne_double :
    ∑ σ : Fin 6, ∑ h : Fin 6, Einc (lenQ idG σ h) (lenR sphereDD σ h) ≠ 6 := by
  rw [sphere_sum]; norm_num

end Lightlike.Regge.Conv3
