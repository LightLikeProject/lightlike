import Lightlike.Rows.G2_077.Fock

/-!
# The one-particle map `K` of the Sorkin–Johnston state is onto the one-particle space

Let `h = range Q ⊆ ℂ^ι` with `Q = √((iΔ)⁺)`.  The real-linear map `K f = √2 Q f` takes values in `h`
(`kv_mem_range`), and every vector of `h` is of the form `K f` (`exists_kv_eq`).  The key is
`Q * conj Q = 0`, which follows from `P * N = 0` (`P = (iΔ)⁺`, `N = (iΔ)⁻ = conj P`).
-/

open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder InnerProductSpace Matrix

namespace Lightlike.Rows.G2_077

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The one-particle space `h = range Q`. -/
noncomputable def oneParticle (Δ : Matrix ι ι ℝ) : Submodule ℂ (EuclideanSpace ℂ ι) :=
  LinearMap.range (Matrix.toEuclideanLin (sqP Δ))

lemma kv_mem_range (Δ : Matrix ι ι ℝ) (f : ι → ℝ) : kv Δ f ∈ oneParticle Δ := by
  refine ⟨WithLp.toLp 2 (((Real.sqrt 2 : ℝ) : ℂ) • rv f), ?_⟩
  change WithLp.toLp 2 ((sqP Δ) *ᵥ (((Real.sqrt 2 : ℝ) : ℂ) • rv f)) = _
  simp [kv, Matrix.mulVec_smul]

/-- Complex conjugation of the entries commutes with the matrix-vector product. -/
lemma cmat_mulVec (A : Matrix ι ι ℂ) (z : ι → ℂ) : cmat A *ᵥ star z = star (A *ᵥ z) := by
  ext i
  simp [Matrix.mulVec, dotProduct, cmat]

lemma cmat_sqP_hermitian (Δ : Matrix ι ι ℝ) : (cmat (sqP Δ)).conjTranspose = cmat (sqP Δ) :=
  (Matrix.nonneg_iff_posSemidef.mp (cmat_nonneg (sqP_nonneg Δ))).isHermitian

/-- `Q * conj Q = 0`. -/
lemma sqP_mul_cmat {Δ : Matrix ι ι ℝ} (h : Δ.transpose = -Δ) : sqP Δ * cmat (sqP Δ) = 0 := by
  have hCC : cmat (sqP Δ) * cmat (sqP Δ) = sjNeg Δ := by
    rw [← cmat_mul, sqP_mul_self, cmat_sjPos h]
  have h1 : cmat (sqP Δ) * sjPos Δ = 0 := by
    rw [← Matrix.conjTranspose_mul_self_eq_zero]
    have : (cmat (sqP Δ) * sjPos Δ)ᴴ * (cmat (sqP Δ) * sjPos Δ)
        = sjPos Δ * (cmat (sqP Δ) * cmat (sqP Δ)) * sjPos Δ := by
      rw [Matrix.conjTranspose_mul, cmat_sqP_hermitian, sjPos_conjTranspose]
      simp only [Matrix.mul_assoc]
    rw [this, hCC, sjPos_mul_sjNeg, Matrix.zero_mul]
  rw [← Matrix.conjTranspose_mul_self_eq_zero]
  have : (sqP Δ * cmat (sqP Δ))ᴴ * (sqP Δ * cmat (sqP Δ))
      = cmat (sqP Δ) * sjPos Δ * cmat (sqP Δ) := by
    rw [Matrix.conjTranspose_mul, cmat_sqP_hermitian, sqP_conjTranspose, ← sqP_mul_self]
    simp only [Matrix.mul_assoc]
  rw [this, h1, Matrix.zero_mul]

/-- Every vector of the one-particle space is of the form `K f` with `f` real. -/
lemma exists_kv_eq {Δ : Matrix ι ι ℝ} (h : Δ.transpose = -Δ) {w : EuclideanSpace ℂ ι}
    (hw : w ∈ oneParticle Δ) : ∃ f : ι → ℝ, kv Δ f = w := by
  obtain ⟨y, rfl⟩ := hw
  set L := Matrix.toEuclideanLin (sqP Δ) with hL
  have hsym : L.IsSymmetric := by
    rw [hL, Matrix.isSymmetric_toEuclideanLin_iff]
    exact sqP_conjTranspose Δ
  set U := LinearMap.range L with hU
  have hmem : U.starProjection y ∈ U := Submodule.starProjection_apply_mem U y
  have hker : y - U.starProjection y ∈ LinearMap.ker L := by
    rw [← hsym.orthogonal_range]
    exact Submodule.sub_starProjection_mem_orthogonal y
  have hLy : L y = L (U.starProjection y) := by
    have := LinearMap.mem_ker.mp hker
    rw [map_sub, sub_eq_zero] at this
    exact this
  obtain ⟨z, hz⟩ := hmem
  set y₁ := U.starProjection y
  set v : ι → ℂ := WithLp.ofLp y₁ with hv
  have hvz : v = sqP Δ *ᵥ WithLp.ofLp z := by
    rw [hv, ← hz]; rfl
  refine ⟨fun i => Real.sqrt 2 * (v i).re, ?_⟩
  rw [hLy]
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; simp
  have hvec : ((Real.sqrt 2 : ℝ) : ℂ) • rv (fun i => Real.sqrt 2 * (v i).re) = v + star v := by
    ext i
    have hre : v i + starRingEnd ℂ (v i) = 2 * ((v i).re : ℂ) := by
      simp [Complex.add_conj]
    simp only [rv, Pi.smul_apply, Pi.add_apply, Pi.star_apply, smul_eq_mul]
    rw [Complex.star_def, hre, Complex.ofReal_mul, ← mul_assoc, hsq]
  have hstar : sqP Δ *ᵥ star v = 0 := by
    rw [hvz, show star (sqP Δ *ᵥ WithLp.ofLp z) = cmat (sqP Δ) *ᵥ star (WithLp.ofLp z) from
      (cmat_mulVec _ _).symm, Matrix.mulVec_mulVec, sqP_mul_cmat h, Matrix.zero_mulVec]
  change _ = WithLp.toLp 2 (sqP Δ *ᵥ WithLp.ofLp y₁)
  simp only [kv]
  congr 1
  rw [← hv, ← Matrix.mulVec_smul, hvec, Matrix.mulVec_add, hstar, add_zero]

end Lightlike.Rows.G2_077
