import Lightlike.GR.ComplexMinkowski
import Physlib.Relativity.SL2C.Basic

/-!
# SU(2, 2) on twistor space, and the Poincaré group as the stabilizer of the infinity twistor

Twistors are written in blocks `Z = (μ, λ)`, `Z : Fin 2 ⊕ Fin 2 → ℂ`, and the incidence relation of
a `2 × 2` matrix `X` is `μ = Xᵀ λ` (`twistorInc`, the `incidence` of `ComplexMinkowski.lean`
through `finSumFinEquiv`, `incidence_comp_finSumFinEquiv`).

* The Hermitian form `Σ(Z) = i(λ̄ · μ - μ̄ · λ)` (`twistorNorm`, the matrix `twistorHerm` of
  signature `(2, 2)`) vanishes on the whole twistor line of `X` iff `X` is Hermitian, i.e. the
  point is in the real slice (`twistorNorm_inc_eq_zero_iff`, `twistorLine_null_iff`).
* `IsSU22 T`: `T` preserves the form and has determinant one.
* The infinity form `I(Z, W) = λ_Z 0 λ_W 1 - λ_Z 1 λ_W 0` (`infinityForm`): on the twistor line of
  any `X` it is `⟨λ λ'⟩` (`infinityForm_inc`).
* **The stabilizer of `I` in SU(2, 2)** consists exactly of the matrices
  `T(L, a) = [[L̄, aᵀ (Lᵀ)⁻¹], [0, (Lᵀ)⁻¹]]` with `L ∈ SL(2, ℂ)` and `a` Hermitian
  (`isSU22_and_fixesInfinity_iff`), and `T(L, a)` maps the twistor line of `X` to that of
  `L X L† + a` (`poincareTwistor_inc`): the Lorentz transformation of `L` (Physlib's
  `Lorentz.SL2C.toSelfAdjointMap` on the real slice) followed by the translation by `a`, i.e. the
  (double cover of the restricted) Poincaré group.

## References

* T. Adamo, *Lectures on twistor theory*, arXiv:1712.02196: the Lorentzian incidence relation with a
  factor `i` (2.2), p. 13; the inner product (2.5), "an SU(2, 2)-invariant" of signature `(+2, -2)`,
  and `Z · Z̄ = i (x - x†) λ λ̄` (2.6), lines of real points in `PN` (2.7), p. 14; the infinity twistor
  (2.29) with `I_AB X^AB = ⟨λ₁ λ₂⟩`, and "the ingredient required to break conformal invariance",
  pp. 20–21.
* M. Atiyah, M. Dunajski, L. Mason, *Twistor theory at fifty*, arXiv:1704.07464, §2.1, p. 7: the
  `(+ + - -)` Hermitian form `Σ` and "the orientation-preserving endomorphisms of the twistor space
  which preserve Σ form a group SU(2, 2)".
* A. Bette, *Twistors, special relativity, conformal symmetry and minimal coupling — a review*,
  arXiv:hep-th/0402150: the Lorentz group block diagonal (3.1), p. 11; the form (3.7) and the
  translations (3.10), p. 14; the Poincaré subgroup as the matrices of (3.5) with `C = 0`, `d = 1`,
  p. 16.

Differences: the incidence relation is Adamo's (1.23) `μ = Xᵀ λ`, without the factor `i` of (2.2),
so the form carries the `i`: `Σ` here is Adamo's `Z · Z̄` for the twistor `(i μ, λ)`, up to the
spinor contractions written in components. The theorem "the stabilizer of `I` in SU(2, 2) is the
Poincaré group" is proved here in matrix form; Adamo says that `I` breaks conformal invariance, and
Bette defines the Poincaré subgroup by the block form; neither states the equality as a theorem.
-/

open Matrix Complex

noncomputable section

namespace Lightlike

/-- The twistor `(μ, λ)` of the incidence relation `μ = Xᵀ λ`. -/
def twistorInc (X : Matrix (Fin 2) (Fin 2) ℂ) (l : Fin 2 → ℂ) : Fin 2 ⊕ Fin 2 → ℂ :=
  Sum.elim (Xᵀ *ᵥ l) l

/-- The library's `incidence` (twistors as `Fin 4 → ℂ`) in blocks. -/
lemma incidence_comp_finSumFinEquiv (x : Fin 4 → ℂ) (l : Fin 2 → ℂ) :
    incidence x l ∘ finSumFinEquiv = twistorInc (spinorMat x) l := by
  funext s
  rcases s with i | i <;> fin_cases i <;>
    simp only [Function.comp_apply, incidence_apply, twistorInc, Sum.elim_inl, Sum.elim_inr, mulVec,
      dotProduct, Fin.sum_univ_two, transpose_apply] <;> rfl

/-! ## The Hermitian form and the real slice -/

/-- The Hermitian matrix `[[0, -i], [i, 0]]` of the twistor form. -/
def twistorHerm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  fromBlocks 0 (-(I • (1 : Matrix (Fin 2) (Fin 2) ℂ))) (I • 1) 0

lemma twistorHerm_isHermitian : twistorHerm.IsHermitian := by
  simp [IsHermitian, twistorHerm, fromBlocks_conjTranspose, conjTranspose_smul]

/-- The twistor form `Σ(Z) = Z† H Z`. -/
def twistorNorm (Z : Fin 2 ⊕ Fin 2 → ℂ) : ℂ := star Z ⬝ᵥ (twistorHerm *ᵥ Z)

lemma twistorNorm_sumElim (m l : Fin 2 → ℂ) :
    twistorNorm (Sum.elim m l) =
      I * (star (l 0) * m 0 + star (l 1) * m 1 - star (m 0) * l 0 - star (m 1) * l 1) := by
  simp only [twistorNorm, twistorHerm, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr, Pi.star_apply, zero_mulVec,
    smul_mulVec, one_mulVec, neg_mulVec, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, zero_add,
    add_zero, Function.comp_apply]
  ring

/-- `Σ` on the twistor line of `X`: `i Σ_{ij} λ_i λ̄_j (X_ij - X̄_ji)` (Adamo (2.6)). -/
lemma twistorNorm_inc (X : Matrix (Fin 2) (Fin 2) ℂ) (l : Fin 2 → ℂ) :
    twistorNorm (twistorInc X l) = I * (l 0 * star (l 0) * (X 0 0 - star (X 0 0)) +
      l 0 * star (l 1) * (X 0 1 - star (X 1 0)) + l 1 * star (l 0) * (X 1 0 - star (X 0 1)) +
      l 1 * star (l 1) * (X 1 1 - star (X 1 1))) := by
  rw [twistorInc, twistorNorm_sumElim]
  simp only [mulVec, dotProduct, Fin.sum_univ_two, transpose_apply, star_add, star_mul]
  ring

/-- **The twistor line of `X` lies in `PN` iff `X` is Hermitian** (Adamo (2.6)–(2.7), p. 14,
states "⇐"). -/
theorem twistorNorm_inc_eq_zero_iff (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (∀ l, twistorNorm (twistorInc X l) = 0) ↔ X.IsHermitian := by
  constructor
  · intro h
    have key : ∀ l : Fin 2 → ℂ, l 0 * star (l 0) * (X 0 0 - star (X 0 0)) +
        l 0 * star (l 1) * (X 0 1 - star (X 1 0)) + l 1 * star (l 0) * (X 1 0 - star (X 0 1)) +
        l 1 * star (l 1) * (X 1 1 - star (X 1 1)) = 0 := by
      intro l
      have := h l
      rw [twistorNorm_inc] at this
      exact (mul_eq_zero.1 this).resolve_left I_ne_zero
    have hI : star I = -I := by simp
    have e1 := key ![1, 0]
    have e2 := key ![0, 1]
    have e3 := key ![1, 1]
    have e4 := key ![1, I]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, star_one, star_zero,
      one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add, hI] at e1 e2 e3 e4
    have h3 : (X 0 1 - star (X 1 0)) + (X 1 0 - star (X 0 1)) = 0 := by
      linear_combination e3 - e1 - e2
    have h4 : -I * (X 0 1 - star (X 1 0)) + I * (X 1 0 - star (X 0 1)) = 0 := by
      linear_combination e4 - e1 - (I * -I) * e2
    have h01 : X 0 1 - star (X 1 0) = 0 := by
      have : 2 * I * (X 0 1 - star (X 1 0)) = 0 := by linear_combination I * h3 - h4
      simpa [I_ne_zero] using this
    have h10 : X 1 0 - star (X 0 1) = 0 := by linear_combination h3 - h01
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [conjTranspose_apply] <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
    · linear_combination -e1
    · linear_combination -h01
    · linear_combination -h10
    · linear_combination -e2
  · intro hX l
    have h00 : star (X 0 0) = X 0 0 := hX.apply 0 0
    have h01 : star (X 0 1) = X 1 0 := hX.apply 1 0
    have h10 : star (X 1 0) = X 0 1 := hX.apply 0 1
    have h11 : star (X 1 1) = X 1 1 := hX.apply 1 1
    rw [twistorNorm_inc, h00, h01, h10, h11]
    ring

/-- **The twistor line of `x` lies in the null twistors iff `x` is a real point**. -/
theorem twistorLine_null_iff (x : Fin 4 → ℂ) :
    (∀ Z ∈ twistorLine x, twistorNorm (Z ∘ finSumFinEquiv) = 0) ↔ ∀ i, (x i).im = 0 := by
  rw [← isHermitian_spinorMat_iff, ← twistorNorm_inc_eq_zero_iff]
  constructor
  · intro h l
    rw [← incidence_comp_finSumFinEquiv]
    exact h _ ⟨l, rfl⟩
  · rintro h Z ⟨l, rfl⟩
    rw [incidence_comp_finSumFinEquiv]
    exact h l

/-! ## SU(2, 2) and the infinity twistor -/

/-- `T` lies in **SU(2, 2)**: it preserves the twistor form and has determinant one. -/
def IsSU22 (T : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ) : Prop :=
  Tᴴ * twistorHerm * T = twistorHerm ∧ T.det = 1

lemma IsSU22.twistorNorm_mulVec {T : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ} (hT : IsSU22 T)
    (Z : Fin 2 ⊕ Fin 2 → ℂ) : twistorNorm (T *ᵥ Z) = twistorNorm Z := by
  unfold twistorNorm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hT.1]

/-- The **infinity form** `I(Z, W) = ⟨λ_Z λ_W⟩` (Adamo (2.29)): `I_AB Z^A W^B`. -/
def infinityForm (Z W : Fin 2 ⊕ Fin 2 → ℂ) : ℂ :=
  Z (Sum.inr 0) * W (Sum.inr 1) - Z (Sum.inr 1) * W (Sum.inr 0)

/-- On the twistor line of `X`, `I_AB X^AB = ⟨λ λ'⟩` (Adamo, p. 21). -/
lemma infinityForm_inc (X : Matrix (Fin 2) (Fin 2) ℂ) (l l' : Fin 2 → ℂ) :
    infinityForm (twistorInc X l) (twistorInc X l') = l 0 * l' 1 - l 1 * l' 0 := by
  simp [infinityForm, twistorInc]

/-- `T` fixes the infinity twistor. -/
def FixesInfinity (T : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ) : Prop :=
  ∀ Z W, infinityForm (T *ᵥ Z) (T *ᵥ W) = infinityForm Z W

/-! ## The Poincaré transformations of twistor space -/

/-- The twistor transformation of the Poincaré transformation `X ↦ L X L† + a`:
`T(L, a) = [[L̄, aᵀ (Lᵀ)⁻¹], [0, (Lᵀ)⁻¹]]`. -/
def poincareTwistor (L : Matrix.SpecialLinearGroup (Fin 2) ℂ) (a : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  fromBlocks ((L : Matrix (Fin 2) (Fin 2) ℂ).map star) (aᵀ * ((L : Matrix (Fin 2) (Fin 2) ℂ)ᵀ)⁻¹) 0
    ((L : Matrix (Fin 2) (Fin 2) ℂ)ᵀ)⁻¹

lemma isUnit_det_transpose (L : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    IsUnit ((L : Matrix (Fin 2) (Fin 2) ℂ)ᵀ).det := by
  rw [det_transpose, L.2]; exact isUnit_one

/-- **`T(L, a)` maps the twistor line of `X` to the twistor line of `L X L† + a`**. -/
theorem poincareTwistor_inc (L : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (a X : Matrix (Fin 2) (Fin 2) ℂ) (l : Fin 2 → ℂ) :
    poincareTwistor L a *ᵥ twistorInc X l =
      twistorInc ((L : Matrix (Fin 2) (Fin 2) ℂ) * X * (L : Matrix (Fin 2) (Fin 2) ℂ)ᴴ + a)
        (((L : Matrix (Fin 2) (Fin 2) ℂ)ᵀ)⁻¹ *ᵥ l) := by
  set M : Matrix (Fin 2) (Fin 2) ℂ := (L : Matrix (Fin 2) (Fin 2) ℂ) with hM
  have hinv : Mᵀ * (Mᵀ)⁻¹ = 1 := mul_nonsing_inv _ (isUnit_det_transpose L)
  have hct : (Mᴴ)ᵀ = M.map star := by
    ext i j; simp [conjTranspose_apply]
  have e1 : (M.map star * (Xᵀ * Mᵀ)) *ᵥ ((Mᵀ)⁻¹ *ᵥ l) = M.map star *ᵥ (Xᵀ *ᵥ l) := by
    rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hinv, Matrix.mul_one, ← mulVec_mulVec]
  have e2 : (aᵀ * (Mᵀ)⁻¹) *ᵥ l = aᵀ *ᵥ ((Mᵀ)⁻¹ *ᵥ l) := (mulVec_mulVec _ _ _).symm
  simp only [poincareTwistor, twistorInc, fromBlocks_mulVec, zero_mulVec, zero_add, Sum.elim_comp_inl,
    Sum.elim_comp_inr]
  refine congrArg₂ Sum.elim ?_ rfl
  rw [transpose_add, transpose_mul, transpose_mul]
  show M.map star *ᵥ (Xᵀ *ᵥ l) + (aᵀ * (Mᵀ)⁻¹) *ᵥ l = ((Mᴴ)ᵀ * (Xᵀ * Mᵀ) + aᵀ) *ᵥ ((Mᵀ)⁻¹ *ᵥ l)
  rw [hct, add_mulVec, e1, e2]

/-- The real slice is preserved: for Hermitian `X` and `a`, `L X L† + a` is Hermitian; on the real
slice the Lorentz part is Physlib's `Lorentz.SL2C.toSelfAdjointMap`. -/
lemma poincare_isHermitian (L : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    {a X : Matrix (Fin 2) (Fin 2) ℂ} (ha : a.IsHermitian) (hX : X.IsHermitian) :
    ((L : Matrix (Fin 2) (Fin 2) ℂ) * X * (L : Matrix (Fin 2) (Fin 2) ℂ)ᴴ + a).IsHermitian := by
  have h1 : ((L : Matrix (Fin 2) (Fin 2) ℂ) * X * (L : Matrix (Fin 2) (Fin 2) ℂ)ᴴ).IsHermitian :=
    (Lorentz.SL2C.toSelfAdjointMap L ⟨X, hX⟩).2
  exact h1.add ha

/-! ## The stabilizer of the infinity twistor in SU(2, 2) -/

/-- The block equations of `T†HT` for an upper triangular `T`. -/
lemma conjTranspose_herm_mul (P Q S : Matrix (Fin 2) (Fin 2) ℂ) :
    (fromBlocks P Q 0 S)ᴴ * twistorHerm * fromBlocks P Q 0 S =
      fromBlocks 0 (-(I • (Pᴴ * S))) (I • (Sᴴ * P)) (I • (Sᴴ * Q) - I • (Qᴴ * S)) := by
  rw [twistorHerm, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, sub_eq_add_neg,
    smul_zero]

/-- **The infinity form on the image of `T`** depends only on the lower blocks. -/
lemma infinityForm_fromBlocks (P Q R S : Matrix (Fin 2) (Fin 2) ℂ) (m l m' l' : Fin 2 → ℂ) :
    infinityForm (fromBlocks P Q R S *ᵥ Sum.elim m l) (fromBlocks P Q R S *ᵥ Sum.elim m' l') =
      (R *ᵥ m + S *ᵥ l) 0 * (R *ᵥ m' + S *ᵥ l') 1 - (R *ᵥ m + S *ᵥ l) 1 * (R *ᵥ m' + S *ᵥ l') 0 := by
  simp [infinityForm, fromBlocks_mulVec]

/-- **`T(L, a)` is in SU(2, 2) and fixes the infinity twistor**, for `L ∈ SL(2, ℂ)` and `a`
Hermitian. -/
theorem poincareTwistor_isSU22 (L : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    {a : Matrix (Fin 2) (Fin 2) ℂ} (ha : a.IsHermitian) :
    IsSU22 (poincareTwistor L a) ∧ FixesInfinity (poincareTwistor L a) := by
  set M : Matrix (Fin 2) (Fin 2) ℂ := (L : Matrix (Fin 2) (Fin 2) ℂ) with hM
  have hdet : M.det = 1 := L.2
  set S : Matrix (Fin 2) (Fin 2) ℂ := (Mᵀ)⁻¹ with hS
  have hinv : Mᵀ * S = 1 := mul_nonsing_inv _ (isUnit_det_transpose L)
  have hPS : (M.map star)ᴴ * S = 1 := by
    have : (M.map star)ᴴ = Mᵀ := by ext i j; simp [conjTranspose_apply]
    rw [this, hinv]
  have hSP : Sᴴ * M.map star = 1 := by
    have := congrArg conjTranspose hPS
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one] at this
  have haT : (aᵀ)ᴴ = aᵀ := ha.transpose
  have hdetS : S.det = 1 := by
    rw [hS, det_nonsing_inv, det_transpose, hdet, Ring.inverse_one]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [poincareTwistor, conjTranspose_herm_mul, hPS, hSP]
    have hQ : Sᴴ * (aᵀ * S) = (aᵀ * S)ᴴ * S := by
      rw [conjTranspose_mul, haT, Matrix.mul_assoc]
    rw [hQ, sub_self, twistorHerm]
  · rw [poincareTwistor, det_fromBlocks_zero₂₁, hdetS, mul_one]
    have : (M.map star).det = star M.det := by
      have := (starRingEnd ℂ).map_det M
      simpa using this.symm
    rw [this, hdet, star_one]
  · intro Z W
    rw [← Sum.elim_comp_inl_inr Z, ← Sum.elim_comp_inl_inr W, poincareTwistor,
      infinityForm_fromBlocks]
    have hd : S 0 0 * S 1 1 - S 0 1 * S 1 0 = 1 := by rw [← det_fin_two]; exact hdetS
    simp only [zero_mulVec, zero_add, infinityForm, Sum.elim_inr, mulVec, dotProduct,
      Fin.sum_univ_two, Function.comp_apply]
    linear_combination (Z (Sum.inr 0) * W (Sum.inr 1) - Z (Sum.inr 1) * W (Sum.inr 0)) * hd

/-- **Every element of SU(2, 2) fixing the infinity twistor is a `T(L, a)`**, with `L ∈ SL(2, ℂ)`
and `a` Hermitian. -/
theorem eq_poincareTwistor_of {T : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ} (hT : IsSU22 T)
    (hI : FixesInfinity T) :
    ∃ (L : Matrix.SpecialLinearGroup (Fin 2) ℂ) (a : Matrix (Fin 2) (Fin 2) ℂ),
      a.IsHermitian ∧ T = poincareTwistor L a := by
  set P := T.toBlocks₁₁
  set Q := T.toBlocks₁₂
  set R := T.toBlocks₂₁
  set S := T.toBlocks₂₂
  have hT' : T = fromBlocks P Q R S := (fromBlocks_toBlocks T).symm
  have hIb : ∀ m l m' l' : Fin 2 → ℂ,
      (R *ᵥ m + S *ᵥ l) 0 * (R *ᵥ m' + S *ᵥ l') 1 - (R *ᵥ m + S *ᵥ l) 1 * (R *ᵥ m' + S *ᵥ l') 0 =
        l 0 * l' 1 - l 1 * l' 0 := by
    intro m l m' l'
    have := hI (Sum.elim m l) (Sum.elim m' l')
    rw [hT', infinityForm_fromBlocks] at this
    simpa [infinityForm] using this
  have hd : S 0 0 * S 1 1 - S 0 1 * S 1 0 = 1 := by
    have := hIb 0 ![1, 0] 0 ![0, 1]
    simp at this
    linear_combination this
  have hcol : ∀ i : Fin 2, R 0 i = 0 ∧ R 1 i = 0 := by
    intro i
    have e0 := hIb (Pi.single i 1) 0 0 ![1, 0]
    have e1 := hIb (Pi.single i 1) 0 0 ![0, 1]
    simp at e0 e1
    constructor
    · linear_combination (-R 0 i) * hd + S 0 0 * e1 - S 0 1 * e0
    · linear_combination (-R 1 i) * hd - S 1 1 * e0 + S 1 0 * e1
  have hR : R = 0 := by
    ext j i
    fin_cases j
    · exact (hcol i).1
    · exact (hcol i).2
  have hdetS : S.det = 1 := by rw [det_fin_two]; exact hd
  have hSu : IsUnit S.det := by rw [hdetS]; exact isUnit_one
  have hSU : IsUnit S := (isUnit_iff_isUnit_det S).2 hSu
  -- the block equations of SU(2, 2)
  have h1 := hT.1
  rw [hT', hR, conjTranspose_herm_mul, twistorHerm] at h1
  obtain ⟨-, h12, -, h22⟩ := fromBlocks_inj.1 h1
  have hPS : Pᴴ * S = 1 := by
    have := neg_injective h12
    exact smul_right_injective _ I_ne_zero this
  have hSQ : Sᴴ * Q = Qᴴ * S := by
    have : I • (Sᴴ * Q - Qᴴ * S) = 0 := by rw [smul_sub]; exact h22
    exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_left I_ne_zero)
  -- `L = (Sᵀ)⁻¹`, `a = (Q S⁻¹)ᵀ`
  have hLdet : ((Sᵀ)⁻¹).det = 1 := by
    rw [det_nonsing_inv, det_transpose, hdetS, Ring.inverse_one]
  let L : Matrix.SpecialLinearGroup (Fin 2) ℂ := ⟨(Sᵀ)⁻¹, hLdet⟩
  have hLT : ((L : Matrix (Fin 2) (Fin 2) ℂ)ᵀ)⁻¹ = S := by
    show (((Sᵀ)⁻¹)ᵀ)⁻¹ = S
    rw [transpose_nonsing_inv, transpose_transpose, nonsing_inv_nonsing_inv _ hSu]
  have hSinv : S⁻¹ = Pᴴ := inv_eq_left_inv hPS
  refine ⟨L, (Q * S⁻¹)ᵀ, ?_, ?_⟩
  · -- `a` is Hermitian
    have hQa : Q = (Q * S⁻¹) * S := by rw [Matrix.mul_assoc, nonsing_inv_mul _ hSu, Matrix.mul_one]
    have h3 : Sᴴ * (Q * S⁻¹) * S = Sᴴ * (Q * S⁻¹)ᴴ * S := by
      have := hSQ
      rw [hQa, conjTranspose_mul (Q * S⁻¹) S] at this
      simpa [Matrix.mul_assoc] using this
    have hSHU : IsUnit Sᴴ := by
      rw [isUnit_iff_isUnit_det, det_conjTranspose]; exact hSu.star
    have h4 : Q * S⁻¹ = (Q * S⁻¹)ᴴ := by
      have := hSU.mul_right_cancel h3
      exact hSHU.mul_left_cancel this
    have : (Q * S⁻¹).IsHermitian := h4.symm
    simpa using this.transpose
  · rw [hT', hR, poincareTwistor, hLT, transpose_transpose, Matrix.mul_assoc, nonsing_inv_mul _ hSu,
      Matrix.mul_one]
    congr 1
    show P = ((Sᵀ)⁻¹).map star
    have : P = (S⁻¹)ᴴ := by rw [hSinv, conjTranspose_conjTranspose]
    rw [this, ← transpose_nonsing_inv]
    ext i j
    simp [conjTranspose_apply]

/-- **The stabilizer of the infinity twistor in SU(2, 2) is the Poincaré group**: `T` lies in
SU(2, 2) and fixes `I` iff `T = T(L, a)` for some `L ∈ SL(2, ℂ)` and Hermitian `a`, the twistor
transformation of `X ↦ L X L† + a` (`poincareTwistor_inc`). -/
theorem isSU22_and_fixesInfinity_iff (T : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ) :
    IsSU22 T ∧ FixesInfinity T ↔
      ∃ (L : Matrix.SpecialLinearGroup (Fin 2) ℂ) (a : Matrix (Fin 2) (Fin 2) ℂ),
        a.IsHermitian ∧ T = poincareTwistor L a := by
  constructor
  · rintro ⟨h1, h2⟩; exact eq_poincareTwistor_of h1 h2
  · rintro ⟨L, a, ha, rfl⟩; exact poincareTwistor_isSU22 L ha

end Lightlike
