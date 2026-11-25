import Lightlike.OperatorAlgebras.PauliJordanQuasiFree.SurjMatrix

/-!
# G2-077: the one-particle map `T f = √2 · √P f`

For real antisymmetric `Δ` let `P = pjPos Δ = (iΔ)⁺` and `Q = √P`.  The real-linear map
`T : (ι → ℝ) → EuclideanSpace ℂ ι`, `T f = √2 • Q f`, satisfies
`⟪T f, T g⟫ = f·|Δ| g + i f·Δ g`, so that `Im ⟪T f, T g⟫ = fᵀΔg` and `‖T f‖² = fᵀ|Δ|f`;
its range is the real span of the complex subspace `range Q`, i.e. `T` is real-surjective onto
`range Q` (`exists_T_eq`).
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace Lightlike.Rows.G2_077

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Δ : Matrix ι ι ℝ}

/-- `√P`, the positive square root of the positive part `P = pjPos Δ` of the Pauli–Jordan matrix. -/
noncomputable def sqrtP (Δ : Matrix ι ι ℝ) : Matrix ι ι ℂ := CFC.sqrt (pjPos Δ)

lemma sqrtP_mul_self (Δ : Matrix ι ι ℝ) : sqrtP Δ * sqrtP Δ = pjPos Δ :=
  CFC.sqrt_mul_sqrt_self _ (pjPos_nonneg Δ)

lemma isSelfAdjoint_sqrtP (Δ : Matrix ι ι ℝ) : IsSelfAdjoint (sqrtP Δ) :=
  (CFC.sqrt_nonneg _).isSelfAdjoint

/-- The one-particle space: the (complex) range of `√P` in `ℂ^ι`. -/
noncomputable def oneParticle (Δ : Matrix ι ι ℝ) : Submodule ℂ (EuclideanSpace ℂ ι) :=
  LinearMap.range (Matrix.toEuclideanLin (sqrtP Δ))

/-- The embedding of a real vector in `ℂ^ι`. -/
noncomputable def embR (f : ι → ℝ) : EuclideanSpace ℂ ι := WithLp.toLp 2 (ofR f)

/-- The one-particle map `T f = √2 • √P f` (real-linear). -/
noncomputable def Tvec (Δ : Matrix ι ι ℝ) (f : ι → ℝ) : EuclideanSpace ℂ ι :=
  ((Real.sqrt 2 : ℝ) : ℂ) • Matrix.toEuclideanLin (sqrtP Δ) (embR f)

lemma Tvec_mem (Δ : Matrix ι ι ℝ) (f : ι → ℝ) : Tvec Δ f ∈ oneParticle Δ :=
  Submodule.smul_mem _ _ ⟨embR f, rfl⟩

lemma inner_sqrtP (x y : EuclideanSpace ℂ ι) :
    inner ℂ (Matrix.toEuclideanLin (sqrtP Δ) x) (Matrix.toEuclideanLin (sqrtP Δ) y) =
      inner ℂ x (Matrix.toEuclideanLin (pjPos Δ) y) := by
  rw [← LinearMap.adjoint_inner_right (Matrix.toEuclideanLin (sqrtP Δ)) x _,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have h : (sqrtP Δ)ᴴ = sqrtP Δ := (isSelfAdjoint_sqrtP Δ)
  have h2 := congrArg (fun M => Matrix.toEuclideanLin M y) (sqrtP_mul_self Δ)
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply] at h2 ⊢
  rw [h, h2]

lemma inner_embR_pjPos (hΔ : Δᵀ = -Δ) (f g : ι → ℝ) :
    inner ℂ (embR f) (Matrix.toEuclideanLin (pjPos Δ) (embR g)) =
      (1 / 2 : ℂ) * (((f ⬝ᵥ absRe Δ *ᵥ g : ℝ) : ℂ) + Complex.I * ((f ⬝ᵥ Δ *ᵥ g : ℝ) : ℂ)) := by
  have h : Matrix.toEuclideanLin (pjPos Δ) (embR g) =
      WithLp.toLp 2 ((1 / 2 : ℂ) • (ofR (absRe Δ *ᵥ g) + Complex.I • ofR (Δ *ᵥ g))) := by
    simp only [Matrix.toEuclideanLin, embR, Matrix.toLpLin_toLp, Matrix.toLin'_apply]
    rw [pjPos_eq hΔ]
    simp only [Matrix.smul_mulVec, Matrix.add_mulVec, iMat, cx_mulVec_ofR]
  rw [h]
  simp only [embR, PiLp.inner_apply, ofR, dotProduct,
    Finset.mul_sum, ← Finset.sum_add_distrib, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [RCLike.inner_apply, Complex.conj_ofReal, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    ofR, Complex.ofReal_mul]
  ring

/-- `⟪T f, T g⟫ = f·|Δ|g + i f·Δg`. -/
theorem inner_Tvec (hΔ : Δᵀ = -Δ) (f g : ι → ℝ) :
    inner ℂ (Tvec Δ f) (Tvec Δ g) =
      ((f ⬝ᵥ absRe Δ *ᵥ g : ℝ) : ℂ) + Complex.I * ((f ⬝ᵥ Δ *ᵥ g : ℝ) : ℂ) := by
  unfold Tvec
  rw [inner_smul_left, inner_smul_right, inner_sqrtP, inner_embR_pjPos hΔ, Complex.conj_ofReal]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; simp
  linear_combination (((f ⬝ᵥ absRe Δ *ᵥ g : ℝ) : ℂ) + Complex.I * ((f ⬝ᵥ Δ *ᵥ g : ℝ) : ℂ)) / 2 * h2

/-- The symplectic form of the one-particle vectors is `Im ⟪T f, T g⟫ = fᵀΔg`. -/
theorem im_inner_Tvec (hΔ : Δᵀ = -Δ) (f g : ι → ℝ) :
    (inner ℂ (Tvec Δ f) (Tvec Δ g)).im = f ⬝ᵥ Δ *ᵥ g := by
  rw [inner_Tvec hΔ]; simp

/-- `‖T f‖² = fᵀ|Δ|f`. -/
theorem norm_sq_Tvec (hΔ : Δᵀ = -Δ) (f : ι → ℝ) :
    ‖Tvec Δ f‖ ^ 2 = f ⬝ᵥ absRe Δ *ᵥ f := by
  have h := inner_Tvec hΔ f f
  rw [inner_self_eq_norm_sq_to_K] at h
  have h' : (((‖Tvec Δ f‖ ^ 2 : ℝ)) : ℂ) = ((f ⬝ᵥ absRe Δ *ᵥ f : ℝ) : ℂ) +
      Complex.I * ((f ⬝ᵥ Δ *ᵥ f : ℝ) : ℂ) := by
    push_cast; exact h
  have := congrArg Complex.re h'
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im] at this
  linarith

omit [Fintype ι] [DecidableEq ι] in
lemma embR_smul (c : ℝ) (x : ι → ℝ) : embR (c • x) = (c : ℂ) • embR x := by
  ext i; simp [embR, ofR]

/-- `Q v = Q x` when `P v = P x`. -/
lemma sqrtP_eq_of_pjPos_eq {v w : EuclideanSpace ℂ ι}
    (h : Matrix.toEuclideanLin (pjPos Δ) v = Matrix.toEuclideanLin (pjPos Δ) w) :
    Matrix.toEuclideanLin (sqrtP Δ) v = Matrix.toEuclideanLin (sqrtP Δ) w := by
  have h0 : Matrix.toEuclideanLin (pjPos Δ) (v - w) = 0 := by rw [map_sub, h, sub_self]
  have h1 := inner_sqrtP (Δ := Δ) (v - w) (v - w)
  rw [h0, inner_zero_right, inner_self_eq_zero, map_sub, sub_eq_zero] at h1
  exact h1

/-- **Real surjectivity.** Every vector of `range √P` is `T f` for a real `f`. -/
theorem exists_T_eq (hΔ : Δᵀ = -Δ) {w : EuclideanSpace ℂ ι} (hw : w ∈ oneParticle Δ) :
    ∃ f : ι → ℝ, Tvec Δ f = w := by
  obtain ⟨v, rfl⟩ := hw
  obtain ⟨x, hx⟩ := exists_real_pjPos_eq hΔ v.ofLp
  have hx' : Matrix.toEuclideanLin (pjPos Δ) v = Matrix.toEuclideanLin (pjPos Δ) (embR x) := by
    simp only [Matrix.toEuclideanLin, embR, Matrix.toLpLin_apply]
    rw [hx]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by simp
  refine ⟨(Real.sqrt 2)⁻¹ • x, ?_⟩
  rw [sqrtP_eq_of_pjPos_eq hx', Tvec, embR_smul, map_smul, smul_smul]
  have : ((Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (by simp)]; simp
  rw [this, one_smul]

end Lightlike.Rows.G2_077
