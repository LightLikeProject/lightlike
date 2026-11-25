import Lightlike.Cosmology.BianchiClassification.ClassB2

/-!
# Class B, part 3: the case `n = 0` (Bianchi type V)

For `l = 0` every nonzero `a` can be moved to `(0, 0, 1)` by a change of basis whose third row
is `a`; this gives the class B normal form of type V.

## Main results

* `Lightlike.Cosmology.BianchiClassification.bnormalisable_zero`: `BNormalisable ![0, 0, 0] a` for `a ≠ 0`.

## References

* heinzle-uggla-2009a (Section 3)
-/

namespace Lightlike.Cosmology.BianchiClassification

open Matrix

/-- For `a ≠ 0` there is an invertible matrix whose third row is `a`. -/
theorem exists_matrix_third_row (a : V3) (ha : a ≠ 0) :
    ∃ P : Matrix (Fin 3) (Fin 3) ℝ, P.det ≠ 0 ∧ ∀ j, P 2 j = a j := by
  by_cases h2 : a 2 ≠ 0
  · refine ⟨!![1, 0, 0; 0, 1, 0; a 0, a 1, a 2], ?_, fun j => ?_⟩
    · simpa [Matrix.det_fin_three] using h2
    · fin_cases j <;> simp
  by_cases h1 : a 1 ≠ 0
  · refine ⟨!![1, 0, 0; 0, 0, 1; a 0, a 1, a 2], ?_, fun j => ?_⟩
    · simpa [Matrix.det_fin_three] using h1
    · fin_cases j <;> simp
  have h0 : a 0 ≠ 0 := by
    intro h
    apply ha
    ext i
    fin_cases i
    · simpa using h
    · simpa using h1
    · simpa using h2
  refine ⟨!![0, 1, 0; 0, 0, 1; a 0, a 1, a 2], ?_, fun j => ?_⟩
  · simpa [Matrix.det_fin_three] using h0
  · fin_cases j <;> simp

/-- Type V: `(diag 0, a)` with `a ≠ 0` is isomorphic to `(0, (0, 0, 1))`. -/
theorem bnormalisable_zero (a : V3) (ha : a ≠ 0) : BNormalisable ![0, 0, 0] a := by
  obtain ⟨P, hP, hrow⟩ := exists_matrix_third_row a ha
  have hz : (![0, 0, 0] : Fin 3 → ℝ) = 0 := by
    ext i; fin_cases i <;> rfl
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP)
  have hat : Pᵀ.mulVec ![0, 0, 1] = a := by
    ext j
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply, hrow j]
  have ha' : (P⁻¹)ᵀ.mulVec a = ![0, 0, 1] := by
    rw [← hat, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hPi, Matrix.transpose_one,
      Matrix.one_mulVec]
  have h := bracketIso_transform (diagonal (![0, 0, 0] : Fin 3 → ℝ)) a P hP
  rw [ha', hz] at h
  have hd : diagonal (0 : Fin 3 → ℝ) = 0 := by
    ext i j; simp [diagonal_apply]
  simp only [hd, Matrix.mul_zero, Matrix.zero_mul, smul_zero] at h
  refine ⟨![0, 0, 0], 1, Or.inl ⟨rfl, rfl⟩, ?_⟩
  rw [hz, hd]
  exact h

end Lightlike.Cosmology.BianchiClassification

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bnormalisable_zero := _root_.Lightlike.Cosmology.BianchiClassification.bnormalisable_zero
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.exists_matrix_third_row := _root_.Lightlike.Cosmology.BianchiClassification.exists_matrix_third_row
