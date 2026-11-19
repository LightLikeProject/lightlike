import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# The quaternions as `2 × 2` complex matrices

`q = a + b i + c j + d k ↦ [[a + b i, c + d i], [-c + d i, a - b i]]` is an injective real `*`-algebra homomorphism
`ℍ → M₂(ℂ)` whose complex span is `M₂(ℂ)`: `ℍ ⊗_ℝ ℂ ≅ M₂(ℂ)`, the step at which the complexification of a real finite
spectral triple with a quaternionic summand stopped (T. Krajewski, arXiv:hep-th/9701081, Section 2, p. 2: `A = ⊕ Mₙᵢ(K)`,
`K = ℝ, ℂ, ℍ`).

* `quatToMat`, `quatToMat_injective`;
* `single_eq_quat`: the matrix units are complex combinations of the images of `1, i, j, k`.
-/

open Matrix
open scoped Quaternion

namespace Lightlike.NCG

/-- **The quaternions as complex `2 × 2` matrices**, a real `*`-algebra homomorphism. -/
noncomputable def quatToMat : ℍ[ℝ] →⋆ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun q := !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩; ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff, Matrix.one_apply]
  map_mul' p q := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff, Quaternion.re_mul, Quaternion.imI_mul,
        Quaternion.imJ_mul, Quaternion.imK_mul] <;> constructor <;> ring
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff]
  map_add' p q := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff] <;> ring
  commutes' c := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff, Algebra.algebraMap_eq_smul_one, Matrix.one_apply]
  map_star' q := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff, Matrix.star_eq_conjTranspose]

/-- The matrix of `a + b i + c j + d k`. -/
lemma quatToMat_apply (q : ℍ[ℝ]) :
    quatToMat q = !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩; ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩] := rfl

/-- **`quatToMat` is injective.** -/
theorem quatToMat_injective : Function.Injective quatToMat := by
  intro p q h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp only [quatToMat_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Complex.mk.injEq] at h00 h01
  obtain ⟨h1, h2⟩ := h00
  obtain ⟨h3, h4⟩ := h01
  ext <;> assumption

/-- The quaternion units `i`, `j`, `k`. -/
def qI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
/-- The quaternion unit `j`. -/
def qJ : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
/-- The quaternion unit `k`. -/
def qK : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

/-- **The matrix units are complex combinations of `1, i, j, k`**: `ℍ ⊗_ℝ ℂ → M₂(ℂ)` is onto. -/
theorem single_eq_quat :
    Matrix.single 0 0 (1 : ℂ) = (1 / 2 : ℂ) • (quatToMat 1 - Complex.I • quatToMat qI) ∧
    Matrix.single 1 1 (1 : ℂ) = (1 / 2 : ℂ) • (quatToMat 1 + Complex.I • quatToMat qI) ∧
    Matrix.single 0 1 (1 : ℂ) = (1 / 2 : ℂ) • (quatToMat qJ - Complex.I • quatToMat qK) ∧
    Matrix.single 1 0 (1 : ℂ) = (1 / 2 : ℂ) • (-quatToMat qJ - Complex.I • quatToMat qK) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [quatToMat_apply, qI, qJ, qK, Complex.ext_iff] <;> norm_num

end Lightlike.NCG
