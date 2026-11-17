import Mathlib
import Lightlike.Canonical.MatrixDeriv
import Lightlike.Canonical.ADM

/-!
# The `π`-gradient of the Hamiltonian constraint

The derivative of the kinetic term in the direction `(0, p)` is the pairing of `p` with
`hamiltonianPiGradient`: `N · dkinJ c H P 0 p = Σ_ij (δH[N]/δπ)_ij p_ij` (pointwise).
-/

open Matrix

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

lemma sum_transpose_mul (M p : Matrix (Fin d) (Fin d) ℝ) :
    ∑ i, ∑ j, Mᵀ i j * p i j = (M * p).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- **The `π`-derivative of the kinetic density is the pairing with `hamiltonianPiGradient`.** -/
theorem hamiltonianPiGradient_pairing (N : (Fin d → ℝ) → ℝ) (h π : TensorField d) (x : Fin d → ℝ)
    (hH : 0 < (h x).det) (p : Matrix (Fin d) (Fin d) ℝ) :
    N x * dkinJ (1 / ((d : ℝ) - 1)) (h x) (π x) 0 p =
      ∑ i, ∑ j, hamiltonianPiGradient N h π x i j * p i j := by
  have hs0 : Real.sqrt (h x).det ≠ 0 := (Real.sqrt_pos.mpr hH).ne'
  set M : Matrix (Fin d) (Fin d) ℝ := 2 • (h x * π x * h x) - (2 / ((d : ℝ) - 1) * (h x * π x).trace) • h x with hM
  have hG : hamiltonianPiGradient N h π x = (N x / Real.sqrt (h x).det) • Mᵀ := by
    unfold hamiltonianPiGradient
    rw [Matrix.transpose_smul]
  have e : ∑ i, ∑ j, hamiltonianPiGradient N h π x i j * p i j =
      (N x / Real.sqrt (h x).det) * (M * p).trace := by
    rw [hG, ← sum_transpose_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.smul_apply]
    ring
  rw [e]
  unfold dkinJ
  simp only [zero_add, Matrix.trace_zero, mul_zero, sub_zero, zero_mul, zero_div]
  have hMp : (M * p).trace = 2 * (h x * π x * h x * p).trace -
      (2 / ((d : ℝ) - 1) * (h x * π x).trace) * (h x * p).trace := by
    rw [hM, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul]
    simp [two_smul]
    ring
  rw [hMp]
  have hsq : Real.sqrt (h x).det ^ 2 = (h x).det := Real.sq_sqrt hH.le
  have hr : (h x * π x * (h x * p)).trace = (h x * π x * h x * p).trace := by simp only [Matrix.mul_assoc]
  rw [hr]
  field_simp

end Lightlike.Canonical

end
