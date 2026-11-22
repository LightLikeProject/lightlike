import Lightlike.Rows.G2_077.PauliJordan
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The one-particle structure of the Sorkin–Johnston state

For a real antisymmetric `Δ` let `Q = √((iΔ)⁺)`.  The real-linear map `K f = √2 · Q f` sends `ℝ^ι` into the
complex Hilbert space `EuclideanSpace ℂ ι` and satisfies `⟪K f, K g⟫ = 2 fᵀ P g` for `P = (iΔ)⁺`, whence
`Im ⟪K f, K g⟫ = fᵀ Δ g` (the commutator form) and `‖K f‖² = 2 fᵀ P f`.
-/

open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder InnerProductSpace

namespace Lightlike.Rows.G2_077

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The square root `Q` of the positive part `P = (iΔ)⁺`. -/
noncomputable def sqP (Δ : Matrix ι ι ℝ) : Matrix ι ι ℂ := CFC.sqrt (sjPos Δ)

lemma sqP_nonneg (Δ : Matrix ι ι ℝ) : 0 ≤ sqP Δ := CFC.sqrt_nonneg _

lemma sqP_mul_self (Δ : Matrix ι ι ℝ) : sqP Δ * sqP Δ = sjPos Δ :=
  CFC.sqrt_mul_sqrt_self _ (sjPos_nonneg Δ)

lemma sqP_conjTranspose (Δ : Matrix ι ι ℝ) : (sqP Δ).conjTranspose = sqP Δ :=
  (Matrix.nonneg_iff_posSemidef.mp (sqP_nonneg Δ)).isHermitian

lemma sjPos_conjTranspose (Δ : Matrix ι ι ℝ) : (sjPos Δ).conjTranspose = sjPos Δ :=
  (Matrix.nonneg_iff_posSemidef.mp (sjPos_nonneg Δ)).isHermitian

/-- A real vector viewed as a complex one. -/
def rv (f : ι → ℝ) : ι → ℂ := fun i => (f i : ℂ)

/-- The one-particle vector `K f = √2 · Q f`. -/
noncomputable def kv (Δ : Matrix ι ι ℝ) (f : ι → ℝ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (((Real.sqrt 2 : ℝ) : ℂ) • (sqP Δ).mulVec (rv f))

lemma inner_kv (Δ : Matrix ι ι ℝ) (f g : ι → ℝ) :
    ⟪kv Δ f, kv Δ g⟫_ℂ = 2 * (rv f ⬝ᵥ (sjPos Δ).mulVec (rv g)) := by
  have hs : (((Real.sqrt 2 : ℝ) : ℂ)) * starRingEnd ℂ ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; simp
  have hrv : star (rv f) = rv f := by ext i; simp [rv]
  simp only [kv, EuclideanSpace.inner_toLp_toLp]
  rw [dotProduct_comm, star_smul, Matrix.star_mulVec, hrv]
  rw [sqP_conjTranspose, smul_dotProduct, dotProduct_smul, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, sqP_mul_self, smul_eq_mul, Complex.star_def]
  linear_combination (rv f ⬝ᵥ (sjPos Δ).mulVec (rv g)) * hs

/-- The quadratic form `f ↦ Re (fᵀ P f)` of the Sorkin–Johnston two-point function (`P = (iΔ)⁺`). -/
noncomputable def qform (Δ : Matrix ι ι ℝ) (f : ι → ℝ) : ℝ := (rv f ⬝ᵥ (sjPos Δ).mulVec (rv f)).re

/-- `‖K f‖² = 2 fᵀ P f`. -/
lemma norm_kv_sq (Δ : Matrix ι ι ℝ) (f : ι → ℝ) : ‖kv Δ f‖ ^ 2 = 2 * qform Δ f := by
  have h1 := congrArg Complex.re (inner_kv Δ f f)
  rw [inner_self_eq_norm_sq_to_K] at h1
  simpa [qform, ← Complex.ofReal_pow] using h1

lemma rv_add (f g : ι → ℝ) : rv (f + g) = rv f + rv g := by ext i; simp [rv]

lemma rv_smul (s : ℝ) (f : ι → ℝ) : rv (s • f) = (s : ℂ) • rv f := by ext i; simp [rv]

lemma kv_add (Δ : Matrix ι ι ℝ) (f g : ι → ℝ) : kv Δ (f + g) = kv Δ f + kv Δ g := by
  simp [kv, rv_add, Matrix.mulVec_add, smul_add]

lemma kv_smul (Δ : Matrix ι ι ℝ) (s : ℝ) (f : ι → ℝ) : kv Δ (s • f) = s • kv Δ f := by
  ext i
  simp [kv, rv_smul, Matrix.mulVec_smul]
  ring

/-- The real-linear one-particle map `K : ℝ^ι → EuclideanSpace ℂ ι`. -/
noncomputable def kmap (Δ : Matrix ι ι ℝ) : (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℂ ι where
  toFun := kv Δ
  map_add' := kv_add Δ
  map_smul' := kv_smul Δ

/-- The imaginary part of the positive part of `iΔ` is `Δ / 2`. -/
lemma sjPos_im {Δ : Matrix ι ι ℝ} (h : Δ.transpose = -Δ) (i j : ι) : (sjPos Δ i j).im = Δ i j / 2 := by
  have e := congrFun (congrFun (sjPos_sub_sjNeg h) i) j
  rw [← cmat_sjPos h] at e
  have e2 := congrArg Complex.im e
  simp [cmat, iMat] at e2
  linarith

/-- **The commutator form**: `Im ⟪K f, K g⟫ = fᵀ Δ g`. -/
lemma inner_kv_im {Δ : Matrix ι ι ℝ} (h : Δ.transpose = -Δ) (f g : ι → ℝ) :
    (⟪kv Δ f, kv Δ g⟫_ℂ).im = f ⬝ᵥ Δ.mulVec g := by
  rw [inner_kv]
  simp only [dotProduct, Matrix.mulVec, rv, Complex.mul_im, Complex.im_sum]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, zero_mul, Complex.re_ofNat,
    Complex.im_ofNat, sjPos_im h]
  simp only [zero_add, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Lightlike.Rows.G2_077
