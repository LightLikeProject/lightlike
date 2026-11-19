import Lightlike.NCG.Uniqueness
import Lightlike.NCG.TestsClassification

/-!
# Tests for the uniqueness of the real structure

* `isComplexLinear_krajewski`: the model `krajewskiTriple` is complex-linear, so the uniqueness theorem applies to it;
* `twoPoint_unique`: the real structure of the two-point model is unitarily equivalent to the model of its own
  multiplicity matrix.
-/

namespace Lightlike.NCG.TestsUniqueness

open TestsClassification

/-- **The model is complex-linear**: `π(c a) = c π(a)` for complex `c`. -/
theorem isComplexLinear_krajewski {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} [∀ i, NeZero (n i)]
    {r : ι → ι → ℕ} (hpos : ∀ i, ∃ j, 0 < r i j) : IsComplexLinear (krajewskiTriple (n := n) (r := r) hpos) := by
  intro c a
  show Matrix.toEuclideanCLM (n := KIdx n r) (𝕜 := ℂ) (blockHom (c • a)) =
    c • Matrix.toEuclideanCLM (n := KIdx n r) (𝕜 := ℂ) (blockHom a)
  rw [← map_smul]
  congr 1
  show Matrix.blockDiagonal' (blk (c • a)) = c • Matrix.blockDiagonal' (blk a)
  rw [← Matrix.blockDiagonal'_smul]
  congr 1
  funext p
  simp only [blk, Pi.smul_apply, Matrix.smul_kronecker, Matrix.kronecker_smul]

/-- **Uniqueness on the two-point model**: its real structure is unitarily equivalent to the model of its
multiplicity matrix. -/
theorem twoPoint_unique :
    ∃ U : HK (fun _ : Fin 2 => 1) twoPointR ≃ₗᵢ[ℂ]
        HK (fun _ : Fin 2 => 1)
          (fun i j => multiplicity (krajewskiReal (n := fun _ : Fin 2 => 1) twoPointR_symm twoPointR_pos) i j),
      (∀ a x, U (piK a x) = piK a (U x)) ∧
        ∀ x, U (JK twoPointR_symm x) =
          JK (multiplicity_symm (krajewskiReal (n := fun _ : Fin 2 => 1) twoPointR_symm twoPointR_pos)) (U x) :=
  exists_unitary_krajewski _ (isComplexLinear_krajewski twoPointR_pos)

end Lightlike.NCG.TestsUniqueness
