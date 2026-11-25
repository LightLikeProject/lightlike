import Mathlib

/-!
# Expansion of the volume factor `det (1 + ε h)` in four dimensions

Row G3-255 (graviton vertices from the Einstein–Hilbert expansion).  The Einstein–Hilbert density is
`√(-g) R` with `g = η + κ h`; its expansion in `h` starts from the expansion of the volume factor
`√(-det g) = √(det (1 + κ η⁻¹ h))`.  This file gives the exact polynomial in `ε` for `det (1 + ε A)` on
`4 × 4` matrices, in terms of the traces `tr A`, `tr A²`, `tr A³` and `det A`.

* `det_one_add_smul_fin4`: `det (1 + ε A) = 1 + ε t₁ + ε² (t₁² - t₂)/2 + ε³ (t₁³ - 3 t₁ t₂ + 2 t₃)/6 + ε⁴ det A`.
-/

open Matrix

namespace Lightlike.GR.EinsteinHilbertExpansion

/-- The Laplace expansion of a `4 × 4` determinant, with every entry written out. -/
theorem det_fin_four (B : Matrix (Fin 4) (Fin 4) ℝ) :
    B.det =
      B 0 0 * (B 1 1 * B 2 2 * B 3 3 - B 1 1 * B 2 3 * B 3 2 - B 1 2 * B 2 1 * B 3 3
          + B 1 2 * B 2 3 * B 3 1 + B 1 3 * B 2 1 * B 3 2 - B 1 3 * B 2 2 * B 3 1)
      - B 0 1 * (B 1 0 * B 2 2 * B 3 3 - B 1 0 * B 2 3 * B 3 2 - B 1 2 * B 2 0 * B 3 3
          + B 1 2 * B 2 3 * B 3 0 + B 1 3 * B 2 0 * B 3 2 - B 1 3 * B 2 2 * B 3 0)
      + B 0 2 * (B 1 0 * B 2 1 * B 3 3 - B 1 0 * B 2 3 * B 3 1 - B 1 1 * B 2 0 * B 3 3
          + B 1 1 * B 2 3 * B 3 0 + B 1 3 * B 2 0 * B 3 1 - B 1 3 * B 2 1 * B 3 0)
      - B 0 3 * (B 1 0 * B 2 1 * B 3 2 - B 1 0 * B 2 2 * B 3 1 - B 1 1 * B 2 0 * B 3 2
          + B 1 1 * B 2 2 * B 3 0 + B 1 2 * B 2 0 * B 3 1 - B 1 2 * B 2 1 * B 3 0) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove_zero, Fin.succ_zero_eq_one, Fin.val_zero, Fin.val_succ]
  simp [Fin.succAbove]
  ring

/-- **Exact expansion of the `4 × 4` determinant `det (1 + ε A)`** in the power traces of `A`. -/
theorem det_one_add_smul_fin4 (ε : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    (1 + ε • A).det =
      1 + ε * A.trace + ε ^ 2 * ((A.trace ^ 2 - (A * A).trace) / 2)
        + ε ^ 3 * ((A.trace ^ 3 - 3 * A.trace * (A * A).trace + 2 * (A * A * A).trace) / 6)
        + ε ^ 4 * A.det := by
  rw [det_fin_four (1 + ε • A), det_fin_four A]
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

end Lightlike.GR.EinsteinHilbertExpansion

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_255.det_fin_four := _root_.Lightlike.GR.EinsteinHilbertExpansion.det_fin_four
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_255.det_one_add_smul_fin4 := _root_.Lightlike.GR.EinsteinHilbertExpansion.det_one_add_smul_fin4
