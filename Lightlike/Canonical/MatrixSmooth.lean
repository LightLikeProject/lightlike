import Mathlib

/-!
# Smoothness of the determinant and of the inverse of a matrix-valued function

The `C^∞` versions of `Lightlike.Gauge.differentiableAt_det` and `differentiableAt_inv_entry` (Cramer's rule): a
matrix-valued function with smooth entries has a smooth determinant, and a smooth inverse where the determinant
does not vanish.
-/

open Matrix
open scoped ContDiff

namespace Lightlike.Canonical

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- The determinant of a matrix-valued function with smooth entries is smooth. -/
theorem contDiffAt_det (M : E → Matrix (Fin n) (Fin n) ℝ) {x : E}
    (hM : ∀ i j, ContDiffAt ℝ ∞ (fun y => M y i j) x) :
    ContDiffAt ℝ ∞ (fun y => (M y).det) x := by
  simp only [Matrix.det_apply']
  refine ContDiffAt.sum fun σ _ => ?_
  have h := fun i : Fin n => hM (σ i) i
  refine contDiffAt_const.mul ?_
  fun_prop

/-- The entries of the inverse of a matrix-valued function with smooth entries and nonzero determinant are smooth
(Cramer's rule). -/
theorem contDiffAt_inv_entry (M : E → Matrix (Fin n) (Fin n) ℝ) {x : E}
    (hM : ∀ i j, ContDiffAt ℝ ∞ (fun y => M y i j) x) (hdet : (M x).det ≠ 0) (a b : Fin n) :
    ContDiffAt ℝ ∞ (fun y => (M y)⁻¹ a b) x := by
  have hadj : ∀ i j, ContDiffAt ℝ ∞ (fun y => (M y).adjugate i j) x := by
    intro i j
    simp only [Matrix.adjugate_apply]
    refine contDiffAt_det (fun y => (M y).updateRow j (Pi.single i 1)) ?_
    intro k l
    simp only [Matrix.updateRow_apply]
    by_cases h : k = j
    · simp [h]; exact contDiffAt_const
    · simpa [h] using hM k l
  have hd := contDiffAt_det M hM
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  exact (hd.inv hdet).mul (hadj a b)

end Lightlike.Canonical
