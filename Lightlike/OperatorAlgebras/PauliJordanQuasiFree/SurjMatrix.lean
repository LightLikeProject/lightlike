import Lightlike.OperatorAlgebras.PauliJordanQuasiFree.PositivePart
import Lightlike.OperatorAlgebras.PauliJordanQuasiFree.Surj

/-!
# G2-077: matrix form of the solvability lemma

For real antisymmetric `Δ` and `S = absRe Δ = √(ΔᵀΔ)`: `S` commutes with `Δ`, `S² = -Δ²`, and
for every `b` there is a real `y` with `S y = -Δ b`, `Δ y = S b`.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace Lightlike.Rows.G2_077

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Δ : Matrix ι ι ℝ}

/-- `√(ΔᵀΔ)` commutes with `Δ` (since `Δ` commutes with `ΔᵀΔ = -Δ²`). -/
lemma absRe_comm (hΔ : Δᵀ = -Δ) : absRe Δ * Δ = Δ * absRe Δ := by
  have h : Commute (Δᵀ * Δ) Δ := by
    rw [hΔ]; unfold Commute SemiconjBy; simp [Matrix.mul_assoc]
  exact (Commute.cfcₙ_nnreal h NNReal.sqrt : Commute _ Δ)

lemma absRe_sq (hΔ : Δᵀ = -Δ) : absRe Δ * absRe Δ = -(Δ * Δ) := by
  rw [absRe_mul_self, hΔ, Matrix.neg_mul]

lemma absRe_transpose (Δ : Matrix ι ι ℝ) : (absRe Δ)ᵀ = absRe Δ := by
  have := isSelfAdjoint_absRe Δ
  simpa [IsSelfAdjoint, Matrix.star_eq_conjTranspose] using this

lemma inner_toEuclideanLin (A : Matrix ι ι ℝ) (x y : EuclideanSpace ℝ ι) :
    inner ℝ (Matrix.toEuclideanLin A x) y = inner ℝ x (Matrix.toEuclideanLin Aᵀ y) := by
  rw [← LinearMap.adjoint_inner_right (Matrix.toEuclideanLin A) x y,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.conjTranspose_eq_transpose_of_trivial]

/-- **Real solvability.** For antisymmetric `Δ`, every `b` admits a real `y` with
`|Δ| y = -Δ b` and `Δ y = |Δ| b`. -/
theorem exists_real_solve (hΔ : Δᵀ = -Δ) (b : ι → ℝ) :
    ∃ y : ι → ℝ, absRe Δ *ᵥ y = -(Δ *ᵥ b) ∧ Δ *ᵥ y = absRe Δ *ᵥ b := by
  set S := absRe Δ with hS
  have hSt : Sᵀ = S := absRe_transpose Δ
  obtain ⟨y, h1, h2⟩ := exists_solve (Matrix.toEuclideanLin Δ) (Matrix.toEuclideanLin S)
    (by intro x y; rw [inner_toEuclideanLin, hΔ, map_neg]; simp)
    (by intro x y; rw [inner_toEuclideanLin, hSt]; simp)
    (by
      intro x
      have := congrArg (fun M => Matrix.toEuclideanLin M x) (absRe_comm hΔ)
      simpa using this)
    (by
      intro x
      have := congrArg (fun M => Matrix.toEuclideanLin M x) (absRe_sq hΔ)
      simpa using this)
    (WithLp.toLp 2 b)
  refine ⟨y.ofLp, ?_, ?_⟩
  · simpa using congrArg WithLp.ofLp h1
  · simpa using congrArg WithLp.ofLp h2

/-- Real vector viewed as a complex vector. -/
abbrev ofR (u : ι → ℝ) : ι → ℂ := fun i => (u i : ℂ)

lemma cx_mulVec_ofR (A : Matrix ι ι ℝ) (u : ι → ℝ) : cx A *ᵥ ofR u = ofR (A *ᵥ u) := by
  ext i
  simp [cx, Matrix.mulVec, dotProduct, ofR]

/-- **Key surjectivity lemma.** Every complex vector `v` differs from a *real* vector `x` by an
element of the kernel of `pjPos Δ`; hence `pjPos Δ v = pjPos Δ x`. -/
theorem exists_real_pjPos_eq (hΔ : Δᵀ = -Δ) (v : ι → ℂ) :
    ∃ x : ι → ℝ, pjPos Δ *ᵥ v = pjPos Δ *ᵥ ofR x := by
  obtain ⟨y, h1, h2⟩ := exists_real_solve hΔ (fun i => (v i).im)
  refine ⟨fun i => (v i).re + y i, ?_⟩
  have hv : v = ofR (fun i => (v i).re) + Complex.I • ofR (fun i => (v i).im) := by
    ext i
    simp only [ofR, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]; exact (Complex.re_add_im _).symm
  have hx : ofR (fun i => (v i).re + y i) = ofR (fun i => (v i).re) + ofR y := by
    ext i; simp [ofR]
  rw [pjPos_eq hΔ, hx]
  conv_lhs => rw [hv]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, iMat,
    cx_mulVec_ofR, Matrix.smul_mulVec]
  rw [h1, h2]
  ext i
  simp only [ofR, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Complex.ofReal_neg]
  linear_combination (1 / 2 : ℂ) * (↑((Δ *ᵥ fun i => (v i).im) i)) * Complex.I_sq

end Lightlike.Rows.G2_077
