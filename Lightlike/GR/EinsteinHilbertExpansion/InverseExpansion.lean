import Mathlib

/-!
# Expansion of the inverse metric `(1 + ε A)⁻¹`

Row G3-255.  With `g = η + κ h` one has `g⁻¹ = (1 + κ η⁻¹ h)⁻¹ η⁻¹`, so the inverse metric entering the
Einstein–Hilbert density is the truncated geometric series below, with an exact remainder.

* `one_add_smul_mul_geom`: `(1 + ε A) (1 - ε A + ε² A² - ε³ A³) = 1 - ε⁴ A⁴`.
* `inv_one_add_smul`: if `1 + ε A` is invertible,
  `(1 + ε A)⁻¹ = 1 - ε A + ε² A² - ε³ A³ + ε⁴ (1 + ε A)⁻¹ A⁴`.
-/

open Matrix

namespace Lightlike.GR.EinsteinHilbertExpansion

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- The truncated geometric series `1 - εA + ε²A² - ε³A³`, the inverse of `1 + εA` up to `O(ε⁴)`. -/
def invSeries (ε : R) (A : Matrix n n R) : Matrix n n R :=
  1 - ε • A + ε ^ 2 • (A * A) - ε ^ 3 • (A * A * A)

/-- `(1 + εA) (1 - εA + ε²A² - ε³A³) = 1 - ε⁴A⁴`. -/
theorem one_add_smul_mul_geom (ε : R) (A : Matrix n n R) :
    (1 + ε • A) * invSeries ε A = 1 - ε ^ 4 • (A * A * A * A) := by
  unfold invSeries
  simp only [mul_sub, mul_add, add_mul, one_mul, mul_one, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
  have h0 : ε * ε = ε ^ 2 := by ring
  have h1 : ε ^ 2 * ε = ε ^ 3 := by ring
  have h2 : ε ^ 3 * ε = ε ^ 4 := by ring
  rw [h0, h1, h2]
  abel

/-- **Inverse of `1 + εA` to third order with exact remainder.** -/
theorem inv_one_add_smul (ε : R) (A : Matrix n n R) (h : IsUnit (1 + ε • A).det) :
    (1 + ε • A)⁻¹ =
      invSeries ε A + ε ^ 4 • ((1 + ε • A)⁻¹ * (A * A * A * A)) := by
  have hB : (1 + ε • A)⁻¹ * (1 + ε • A) = 1 := Matrix.nonsing_inv_mul _ h
  have key : invSeries ε A = (1 + ε • A)⁻¹ * (1 + ε • A) * invSeries ε A := by rw [hB, one_mul]
  rw [Matrix.mul_assoc, one_add_smul_mul_geom, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_smul] at key
  rw [key]
  abel

end Lightlike.GR.EinsteinHilbertExpansion

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_255.invSeries := _root_.Lightlike.GR.EinsteinHilbertExpansion.invSeries
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_255.inv_one_add_smul := _root_.Lightlike.GR.EinsteinHilbertExpansion.inv_one_add_smul
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_255.one_add_smul_mul_geom := _root_.Lightlike.GR.EinsteinHilbertExpansion.one_add_smul_mul_geom
