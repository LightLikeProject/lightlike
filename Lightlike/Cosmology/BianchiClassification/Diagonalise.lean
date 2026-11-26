import Lightlike.Cosmology.BianchiClassification.Transform

/-!
# Orthogonal diagonalisation of the matrix `n`

By the spectral theorem a real symmetric `n` is `U D Uᵀ` with `U` orthogonal.  Changing basis by
`P = Uᵀ` (which has `det P = ±1`) turns `n` into a diagonal matrix and `a` into `Uᵀ a`.

## Main results

* `Lightlike.Cosmology.BianchiClassification.exists_orthogonal_diagonal`: spectral theorem in the form needed here.
* `Lightlike.Cosmology.BianchiClassification.exists_diagonalisation`: every Bianchi bracket is isomorphic to one with
  diagonal `n`, preserving `n a = 0` and `a = 0`.

## References

* heinzle-uggla-2009a (Section 3)
-/

namespace Lightlike.Cosmology.BianchiClassification

open Matrix

/-- Spectral theorem: a real symmetric `3 × 3` matrix is diagonalised by an orthogonal matrix. -/
theorem exists_orthogonal_diagonal (n : Matrix (Fin 3) (Fin 3) ℝ) (hn : n.IsSymm) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ), Uᵀ * U = 1 ∧ Uᵀ * n * U = diagonal d := by
  have hA : n.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hn
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℝ), hA.eigenvalues, ?_, ?_⟩
  · have := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  · have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa [Matrix.star_eq_conjTranspose] using h

/-- Every Bianchi bracket is isomorphic to one with diagonal `n`; the isomorphism preserves the
conditions `n a = 0` and `a = 0`. -/
theorem exists_diagonalisation (n : Matrix (Fin 3) (Fin 3) ℝ) (hn : n.IsSymm) (a : V3) :
    ∃ (d : Fin 3 → ℝ) (a' : V3), BracketIso n a (diagonal d) a' ∧
      (n.mulVec a = 0 → (diagonal d).mulVec a' = 0) ∧ (a = 0 → a' = 0) := by
  obtain ⟨U, d, hU, hd⟩ := exists_orthogonal_diagonal n hn
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hdet : Uᵀ.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hU
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hP := bracketIso_transform n a Uᵀ hdet
  rw [Matrix.transpose_transpose, hd, Matrix.inv_eq_right_inv hU, ← Matrix.diagonal_smul] at hP
  have hUa : U.mulVec (Uᵀ.mulVec a) = a := by
    rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  refine ⟨(Uᵀ.det)⁻¹ • d, Uᵀ.mulVec a, ?_, ?_, ?_⟩
  · exact hP
  · intro h0
    rw [Matrix.diagonal_smul, Matrix.smul_mulVec, ← hd, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hUa, h0, Matrix.mulVec_zero, smul_zero]
  · intro h0
    rw [h0, Matrix.mulVec_zero]

end Lightlike.Cosmology.BianchiClassification

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.exists_diagonalisation := _root_.Lightlike.Cosmology.BianchiClassification.exists_diagonalisation
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.exists_orthogonal_diagonal := _root_.Lightlike.Cosmology.BianchiClassification.exists_orthogonal_diagonal
