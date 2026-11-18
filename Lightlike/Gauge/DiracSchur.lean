import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Real.Basic

/-!
# Left null vectors of a block matrix from its Schur complement

Third attempt at the nonlinear Dirac algorithm (Henneaux and Teitelboim 1992, Chapter One, "Constrained Hamiltonian
Systems"): the consistency conditions `{φ_b, H} + ∑ u_a {φ_b, φ_a} ≈ 0` are a linear system `Cmat u = -h` with the
bracket matrix `Cmat`, and the secondary constraints are the compatibility conditions `ν · h = 0` for the left null
vectors `ν` of `Cmat`. Where an `r × r` block `B` of `Cmat = [[B, C], [D, E]]` is invertible and the Schur complement
`E - D B⁻¹ C` vanishes (the rank of `Cmat` equals `r`), the rows of `[-D B⁻¹, 1]` are explicit left null vectors, built
from the entries of `B⁻¹`, `D`, so smooth where `B`, `D` are (no choice of a null-vector bundle). This is local: `B` is
invertible only near a point.

* `leftNull_mul`: `[[1, 0], [-D B⁻¹, 1]] · [[B, C], [D, E]] = [[B, C], [0, E - D B⁻¹ C]]`.
* `leftNull_row_zero`: if the Schur complement vanishes, the lower rows of that product are zero.
-/

namespace Lightlike.Gauge

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **The left null vectors**: multiplying a block matrix by `[[1, 0], [-D B⁻¹, 1]]` on the left gives the Schur
complement in the lower right corner and zero in the lower left. -/
theorem leftNull_mul (B : Matrix m m ℝ) (C : Matrix m n ℝ) (D : Matrix n m ℝ) (E : Matrix n n ℝ)
    (hB : IsUnit B.det) :
    fromBlocks (1 : Matrix m m ℝ) 0 (-(D * B⁻¹)) (1 : Matrix n n ℝ) * fromBlocks B C D E =
      fromBlocks B C 0 (E - D * B⁻¹ * C) := by
  rw [fromBlocks_multiply]
  have h0 : D * B⁻¹ * B = D := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul B hB, Matrix.mul_one]
  have e1 : (-(D * B⁻¹)) * B + (1 : Matrix n n ℝ) * D = 0 := by
    rw [Matrix.neg_mul, h0, Matrix.one_mul, neg_add_cancel]
  have e2 : (-(D * B⁻¹)) * C + (1 : Matrix n n ℝ) * E = E - D * B⁻¹ * C := by
    rw [Matrix.neg_mul, Matrix.one_mul, sub_eq_add_neg, add_comm]
  rw [e1, e2]
  simp

/-- **Rows of the lower block are null when the Schur complement vanishes**: for `x : m → ℝ`-free statement, the
vector `ν = (-D B⁻¹ i, e_i)` satisfies `ν · [[B, C], [D, E]] = 0` when `E = D B⁻¹ C`. -/
theorem leftNull_row_zero (B : Matrix m m ℝ) (C : Matrix m n ℝ) (D : Matrix n m ℝ) (E : Matrix n n ℝ)
    (hB : IsUnit B.det) (hS : E = D * B⁻¹ * C) :
    fromBlocks (1 : Matrix m m ℝ) 0 (-(D * B⁻¹)) (1 : Matrix n n ℝ) * fromBlocks B C D E =
      fromBlocks B C 0 0 := by
  rw [leftNull_mul B C D E hB, hS, sub_self]

end Lightlike.Gauge
