import Mathlib

/-!
# The positive part of `iΔ` for a real antisymmetric matrix `Δ`

Let `Δ` be a real antisymmetric matrix (the Pauli–Jordan matrix of a finite causal set is of this
form, Johnston 2009, eq. (10)). Then `iΔ` is Hermitian, and its positive part `Pos(iΔ)` is the
Wightman two-point function of the Sorkin–Johnston state (Afshordi–Aslanbeigi–Sorkin 2012, Section 3).

* `cx`, `iMat Δ`: the complexification of a real matrix and the Hermitian matrix `iΔ`;
* `absRe Δ`: the real symmetric matrix `|Δ| = √(ΔᵀΔ)`;
* `pjPos Δ = (iΔ)⁺` (continuous functional calculus of the C⋆-algebra of complex matrices);
* `pjPos_eq`: `(iΔ)⁺ = (|Δ| + iΔ) / 2`, with `|Δ|` real;
* `pjPos_nonneg`: `(iΔ)⁺` is positive semidefinite.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace Lightlike.OperatorAlgebras.PauliJordanQuasiFree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complexification of a real matrix. -/
noncomputable def cx (A : Matrix ι ι ℝ) : Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix A

@[simp] lemma cx_apply (A : Matrix ι ι ℝ) (i j : ι) : cx A i j = (A i j : ℂ) := rfl

lemma cx_mul (A B : Matrix ι ι ℝ) : cx (A * B) = cx A * cx B := map_mul _ _ _

lemma cx_add (A B : Matrix ι ι ℝ) : cx (A + B) = cx A + cx B := map_add _ _ _

lemma star_cx (A : Matrix ι ι ℝ) : star (cx A) = cx (star A) := by
  ext i j; simp [Matrix.star_apply]

/-- The Hermitian matrix `iΔ`. -/
noncomputable def iMat (Δ : Matrix ι ι ℝ) : Matrix ι ι ℂ := Complex.I • cx Δ

/-- The real symmetric matrix `|Δ| = √(ΔᵀΔ)`. -/
noncomputable def absRe (Δ : Matrix ι ι ℝ) : Matrix ι ι ℝ := CFC.sqrt (Δᵀ * Δ)

/-- **The positive part `(iΔ)⁺`** of the Hermitian matrix `iΔ`. -/
noncomputable def pjPos (Δ : Matrix ι ι ℝ) : Matrix ι ι ℂ := (iMat Δ)⁺

variable {Δ : Matrix ι ι ℝ}

lemma star_iMat : star (iMat Δ) = (-Complex.I) • cx Δᵀ := by
  ext i j; simp [iMat, Matrix.star_apply]

lemma isSelfAdjoint_iMat (hΔ : Δᵀ = -Δ) : IsSelfAdjoint (iMat Δ) := by
  show star (iMat Δ) = iMat Δ
  rw [star_iMat, hΔ]
  ext i j; simp [iMat]

lemma star_iMat_mul_iMat (Δ : Matrix ι ι ℝ) : star (iMat Δ) * iMat Δ = cx (Δᵀ * Δ) := by
  rw [star_iMat, cx_mul]
  simp only [iMat, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp

lemma absRe_nonneg (Δ : Matrix ι ι ℝ) : 0 ≤ absRe Δ := CFC.sqrt_nonneg _

lemma absRe_mul_self (Δ : Matrix ι ι ℝ) : absRe Δ * absRe Δ = Δᵀ * Δ :=
  CFC.sqrt_mul_sqrt_self _ (by simpa using Matrix.posSemidef_conjTranspose_mul_self Δ |>.nonneg)

lemma isSelfAdjoint_absRe (Δ : Matrix ι ι ℝ) : IsSelfAdjoint (absRe Δ) :=
  .of_nonneg (absRe_nonneg Δ)

lemma cx_absRe_nonneg (Δ : Matrix ι ι ℝ) : 0 ≤ cx (absRe Δ) := by
  have h1 : absRe Δ = star (CFC.sqrt (absRe Δ)) * CFC.sqrt (absRe Δ) := by
    rw [(isSelfAdjoint_absRe Δ |> fun _ => (.of_nonneg (CFC.sqrt_nonneg (absRe Δ)) :
      IsSelfAdjoint (CFC.sqrt (absRe Δ)))).star_eq]
    exact (CFC.sqrt_mul_sqrt_self _ (absRe_nonneg Δ)).symm
  rw [h1, cx_mul, ← star_cx]
  exact star_mul_self_nonneg _

lemma abs_iMat (Δ : Matrix ι ι ℝ) : CFC.abs (iMat Δ) = cx (absRe Δ) := by
  unfold CFC.abs
  rw [star_iMat_mul_iMat, CFC.sqrt_eq_iff _ _ (by rw [← star_iMat_mul_iMat]; exact star_mul_self_nonneg _)
    (cx_absRe_nonneg Δ), ← cx_mul, absRe_mul_self]

/-- `(iΔ)⁺ = (|Δ| + iΔ) / 2`, with `|Δ|` the real matrix `√(ΔᵀΔ)`. -/
theorem pjPos_eq (hΔ : Δᵀ = -Δ) :
    pjPos Δ = (1 / 2 : ℂ) • (cx (absRe Δ) + iMat Δ) := by
  have h := isSelfAdjoint_iMat hΔ
  have h1 := CFC.posPart_add_negPart (iMat Δ) h
  have h2 := CFC.posPart_sub_negPart (iMat Δ) h
  rw [abs_iMat] at h1
  unfold pjPos
  rw [← h1]
  generalize (iMat Δ)⁺ = p at h2 ⊢
  generalize (iMat Δ)⁻ = n at h2 ⊢
  rw [← h2]
  module

/-- `(iΔ)⁺` is positive semidefinite. -/
theorem pjPos_nonneg (Δ : Matrix ι ι ℝ) : 0 ≤ pjPos Δ := CFC.posPart_nonneg _

end Lightlike.OperatorAlgebras.PauliJordanQuasiFree

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.absRe := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.absRe
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.absRe_mul_self := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.absRe_mul_self
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.absRe_nonneg := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.absRe_nonneg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.abs_iMat := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.abs_iMat
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.cx := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.cx
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.cx_absRe_nonneg := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.cx_absRe_nonneg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.cx_add := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.cx_add
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.cx_apply := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.cx_apply
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.cx_mul := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.cx_mul
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.iMat := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.iMat
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.isSelfAdjoint_absRe := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.isSelfAdjoint_absRe
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.isSelfAdjoint_iMat := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.isSelfAdjoint_iMat
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.pjPos := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.pjPos
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.pjPos_eq := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.pjPos_eq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.pjPos_nonneg := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.pjPos_nonneg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.star_cx := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.star_cx
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.star_iMat := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.star_iMat
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.star_iMat_mul_iMat := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.star_iMat_mul_iMat
