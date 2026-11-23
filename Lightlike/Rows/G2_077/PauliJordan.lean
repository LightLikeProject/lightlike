import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# The Pauli–Jordan matrix and its positive part

Sorkin–Johnston construction on a finite set (Johnston 2009, `johnston-2009`; Afshordi–Aslanbeigi–Sorkin 2012,
`aas-2012`, Section 3).  For a real antisymmetric matrix `Δ` (the Pauli–Jordan matrix) the matrix `iΔ` is Hermitian;
`sjPos Δ = (iΔ)⁺` is its positive part and `sjNeg Δ = (iΔ)⁻` its negative part, `iΔ = (iΔ)⁺ - (iΔ)⁻`.
-/

open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Lightlike.Rows.G2_077

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Hermitian matrix `iΔ` of a real matrix `Δ`. -/
noncomputable def iMat (Δ : Matrix ι ι ℝ) : Matrix ι ι ℂ := Complex.I • Δ.map (↑)

omit [Fintype ι] [DecidableEq ι] in
lemma iMat_isHermitian {Δ : Matrix ι ι ℝ} (h : Δ.transpose = -Δ) : (iMat Δ).IsHermitian := by
  ext i j
  have := congrFun (congrFun h j) i
  simp only [iMat, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal, Matrix.transpose_apply, Matrix.neg_apply] at this ⊢
  rw [this]
  simp

/-- The positive part of `iΔ`: the Wightman two-point function of the Sorkin–Johnston state. -/
noncomputable def sjPos (Δ : Matrix ι ι ℝ) : Matrix ι ι ℂ := (iMat Δ)⁺

/-- The negative part of `iΔ`. -/
noncomputable def sjNeg (Δ : Matrix ι ι ℝ) : Matrix ι ι ℂ := (iMat Δ)⁻

lemma sjPos_sub_sjNeg {Δ : Matrix ι ι ℝ} (h : Δ.transpose = -Δ) : sjPos Δ - sjNeg Δ = iMat Δ :=
  CFC.posPart_sub_negPart _ (iMat_isHermitian h).isSelfAdjoint

lemma sjPos_nonneg (Δ : Matrix ι ι ℝ) : 0 ≤ sjPos Δ := CFC.posPart_nonneg _

lemma sjNeg_nonneg (Δ : Matrix ι ι ℝ) : 0 ≤ sjNeg Δ := CFC.negPart_nonneg _

lemma sjPos_mul_sjNeg (Δ : Matrix ι ι ℝ) : sjPos Δ * sjNeg Δ = 0 := CFC.posPart_mul_negPart _

lemma sjNeg_mul_sjPos (Δ : Matrix ι ι ℝ) : sjNeg Δ * sjPos Δ = 0 := by
  have h1 : (sjPos Δ * sjNeg Δ).conjTranspose = 0 := by rw [sjPos_mul_sjNeg]; simp
  rw [Matrix.conjTranspose_mul] at h1
  have hp : (sjPos Δ).conjTranspose = sjPos Δ := (Matrix.nonneg_iff_posSemidef.mp (sjPos_nonneg Δ)).isHermitian
  have hn : (sjNeg Δ).conjTranspose = sjNeg Δ := (Matrix.nonneg_iff_posSemidef.mp (sjNeg_nonneg Δ)).isHermitian
  rwa [hp, hn] at h1

/-- Complex conjugation of the entries of a matrix. -/
def cmat (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := A.map (starRingEnd ℂ)

lemma cmat_nonneg {A : Matrix ι ι ℂ} (hA : 0 ≤ A) : 0 ≤ cmat A := by
  rw [Matrix.nonneg_iff_posSemidef] at hA ⊢
  have : cmat A = A.transpose := by
    ext i j
    have := congrFun (congrFun hA.isHermitian j) i
    simpa [cmat, Matrix.conjTranspose_apply] using this
  rw [this]; exact hA.transpose

lemma cmat_mul {A B : Matrix ι ι ℂ} : cmat (A * B) = cmat A * cmat B := by
  simp [cmat, Matrix.map_mul]

lemma cmat_iMat (Δ : Matrix ι ι ℝ) : cmat (iMat Δ) = -iMat Δ := by
  ext i j; simp [cmat, iMat]

/-- **The conjugate of the positive part is the negative part**: `conj (iΔ)⁺ = (iΔ)⁻`, since `iΔ` is purely
imaginary. -/
lemma cmat_sjPos {Δ : Matrix ι ι ℝ} (h : Δ.transpose = -Δ) : cmat (sjPos Δ) = sjNeg Δ := by
  have e1 : iMat Δ = cmat (sjNeg Δ) - cmat (sjPos Δ) := by
    have := congrArg cmat (sjPos_sub_sjNeg h)
    rw [cmat_iMat] at this
    have h2 : cmat (sjPos Δ - sjNeg Δ) = cmat (sjPos Δ) - cmat (sjNeg Δ) := by ext i j; simp [cmat]
    rw [h2] at this
    rw [← neg_neg (iMat Δ), ← this]; abel
  have e2 : cmat (sjNeg Δ) * cmat (sjPos Δ) = 0 := by
    rw [← cmat_mul, sjNeg_mul_sjPos]; ext i j; simp [cmat]
  have := CFC.posPart_negPart_unique e1 e2 (cmat_nonneg (sjNeg_nonneg Δ)) (cmat_nonneg (sjPos_nonneg Δ))
  exact this.2.symm

end Lightlike.Rows.G2_077
