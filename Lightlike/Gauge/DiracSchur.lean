import Mathlib.LinearAlgebra.Matrix.Rank
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

variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] [DecidableEq m] [DecidableEq n] [DecidableEq l]

/-- **The left null vectors**: multiplying a block matrix by `[[1, 0], [-D B⁻¹, 1]]` on the left gives the Schur
complement in the lower right corner and zero in the lower left. -/
theorem leftNull_mul (B : Matrix m m ℝ) (C : Matrix m l ℝ) (D : Matrix n m ℝ) (E : Matrix n l ℝ)
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
theorem leftNull_row_zero (B : Matrix m m ℝ) (C : Matrix m l ℝ) (D : Matrix n m ℝ) (E : Matrix n l ℝ)
    (hB : IsUnit B.det) (hS : E = D * B⁻¹ * C) :
    fromBlocks (1 : Matrix m m ℝ) 0 (-(D * B⁻¹)) (1 : Matrix n n ℝ) * fromBlocks B C D E =
      fromBlocks B C 0 0 := by
  rw [leftNull_mul B C D E hB, hS, sub_self]

/-- **A vanishing Schur complement from the rank**: if an invertible `r × r` block `B` and a block `S` form the
block-diagonal matrix `[[B, 0], [0, S]]` of rank at most `r`, then `S = 0`. (A nonzero entry `S i j` would give an
invertible `(r + 1) × (r + 1)` submatrix.) -/
theorem schur_eq_zero_of_rank_le (B : Matrix m m ℝ) (S : Matrix n l ℝ) (hB : IsUnit B.det)
    (h : (fromBlocks B 0 0 S).rank ≤ Fintype.card m) : S = 0 := by
  by_contra hS
  obtain ⟨i, j, hij⟩ : ∃ i j, S i j ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hS (Matrix.ext hne)
  let r : m ⊕ Unit → m ⊕ n := Sum.map id fun _ => i
  let c : m ⊕ Unit → m ⊕ l := Sum.map id fun _ => j
  have hsub : (fromBlocks B 0 0 S).submatrix r c = fromBlocks B 0 0 (Matrix.of fun _ _ => S i j) := by
    ext x y
    rcases x with x | x <;> rcases y with y | y <;> simp [r, c]
  have hdet : ((fromBlocks B 0 0 S).submatrix r c).det ≠ 0 := by
    rw [hsub, det_fromBlocks_zero₂₁]
    simp only [det_unique, Matrix.of_apply]
    exact mul_ne_zero (hB.ne_zero) hij
  have hrank : ((fromBlocks B 0 0 S).submatrix r c).rank = Fintype.card m + 1 := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))]
    simp
  have := Matrix.rank_submatrix_le (fromBlocks B 0 0 S) r c
  omega

/-- **Constant rank gives the Schur complement zero**: if `B` is invertible and the block matrix
`[[B, C], [D, E]]` has rank at most `r = card m`, then `E = D B⁻¹ C`; so the rows of `[-D B⁻¹, 1]` are left null
vectors (`leftNull_row_zero`). -/
theorem schur_eq_zero_of_rank_le_block (B : Matrix m m ℝ) (C : Matrix m l ℝ) (D : Matrix n m ℝ)
    (E : Matrix n l ℝ) (hB : IsUnit B.det) (h : (fromBlocks B C D E).rank ≤ Fintype.card m) :
    E = D * B⁻¹ * C := by
  have hL : IsUnit (fromBlocks (1 : Matrix m m ℝ) 0 (-(D * B⁻¹)) (1 : Matrix n n ℝ)).det := by
    rw [det_fromBlocks_zero₁₂]; simp
  have hR : IsUnit (fromBlocks (1 : Matrix m m ℝ) (-(B⁻¹ * C)) 0 (1 : Matrix l l ℝ)).det := by
    rw [det_fromBlocks_zero₂₁]; simp
  have h1 : fromBlocks (1 : Matrix m m ℝ) 0 (-(D * B⁻¹)) (1 : Matrix n n ℝ) * fromBlocks B C D E =
      fromBlocks B C 0 (E - D * B⁻¹ * C) := leftNull_mul B C D E hB
  have h2 : fromBlocks B C 0 (E - D * B⁻¹ * C) *
      fromBlocks (1 : Matrix m m ℝ) (-(B⁻¹ * C)) 0 (1 : Matrix l l ℝ) =
      fromBlocks B 0 0 (E - D * B⁻¹ * C) := by
    rw [fromBlocks_multiply]
    have e : B * -(B⁻¹ * C) + C * (1 : Matrix l l ℝ) = 0 := by
      rw [Matrix.mul_neg, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv B hB, Matrix.one_mul,
        neg_add_cancel]
    have e' : -(B * (B⁻¹ * C)) + C = 0 := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv B hB, Matrix.one_mul, neg_add_cancel]
    simp [e']
  have hrank : (fromBlocks B 0 0 (E - D * B⁻¹ * C)).rank = (fromBlocks B C D E).rank := by
    rw [← h2, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hR, ← h1,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hL]
  have hz := schur_eq_zero_of_rank_le B (E - D * B⁻¹ * C) hB (hrank ▸ h)
  exact sub_eq_zero.mp hz

/-- **The consistency system and its secondary constraint**: with `B` invertible and the Schur complement zero
(`E = D B⁻¹ C`, i.e. constant rank), the system `B u₁ + C u₂ + h₁ = 0`, `D u₁ + E u₂ + h₂ = 0` for the multipliers
`(u₁, u₂)` is solvable exactly when `h₂ - D B⁻¹ h₁ = 0`. These are the secondary constraints, the entries of
`ν · h` for the left null vectors `ν` of `leftNull_row_zero`. -/
theorem consistency_iff (B : Matrix m m ℝ) (C : Matrix m l ℝ) (D : Matrix n m ℝ)
    (E : Matrix n l ℝ) (hB : IsUnit B.det) (hS : E = D * B⁻¹ * C) (h₁ : m → ℝ) (h₂ : n → ℝ) :
    (∃ (u₁ : m → ℝ) (u₂ : l → ℝ), B *ᵥ u₁ + C *ᵥ u₂ + h₁ = 0 ∧ D *ᵥ u₁ + E *ᵥ u₂ + h₂ = 0) ↔
      h₂ - D *ᵥ (B⁻¹ *ᵥ h₁) = 0 := by
  constructor
  · rintro ⟨u₁, u₂, e1, e2⟩
    have k1 : (D * B⁻¹) *ᵥ (B *ᵥ u₁) = D *ᵥ u₁ := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul B hB, Matrix.mul_one]
    have k2 : (D * B⁻¹) *ᵥ (C *ᵥ u₂) = E *ᵥ u₂ := by rw [Matrix.mulVec_mulVec, ← hS]
    have k3 : (D * B⁻¹) *ᵥ h₁ = D *ᵥ (B⁻¹ *ᵥ h₁) := by rw [← Matrix.mulVec_mulVec]
    have e3 := congrArg (fun v => (D * B⁻¹) *ᵥ v) e1
    simp only [Matrix.mulVec_add, k1, k2, k3, Matrix.mulVec_zero] at e3
    calc h₂ - D *ᵥ (B⁻¹ *ᵥ h₁)
        = (D *ᵥ u₁ + E *ᵥ u₂ + h₂) - (D *ᵥ u₁ + E *ᵥ u₂ + D *ᵥ (B⁻¹ *ᵥ h₁)) := by abel
      _ = 0 := by rw [e2, e3, sub_zero]
  · intro h
    refine ⟨-(B⁻¹ *ᵥ h₁), 0, ?_, ?_⟩
    · rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hB, Matrix.one_mulVec,
        Matrix.mulVec_zero]
      abel
    · rw [Matrix.mulVec_neg, Matrix.mulVec_zero, add_zero, sub_eq_zero.mp h]
      abel

end Lightlike.Gauge
