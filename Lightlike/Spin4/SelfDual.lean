import Lightlike.Spin4.SO4

/-!
# Self-dual and anti-self-dual 2-forms: which factor of Spin(4) is which

`Spin4 = SU2 × SU2` acts on `ℝ⁴ = ℍ` by `x ↦ p x q⁻¹` (`toSO4`, `toSO4Mat`). This file identifies
the two factors with the two chiralities of 2-forms, for the orientation of `ℝ⁴` given by the
basis `(1, i, j, k)` (the basis `basisH` of `toSO4Mat`) and the Euclidean metric.

A 2-form is a skew matrix `A` (`A_{ab} = -A_{ba}`); its Hodge dual is
`(⋆A)_{ab} = ½ ε_{abcd} A_{cd}` with `ε_{0123} = 1` (`hodge`). The self-dual forms (`⋆A = A`) and
the anti-self-dual forms (`⋆A = -A`) are the two 3-dimensional summands of `Λ²ℝ⁴ = so(4)`.

## Main results

* `leftMat_isSelfDual`, `rightMat_isAntiSelfDual`: the generators `x ↦ u x` (`u` imaginary) of the
  first factor are self-dual, the generators `x ↦ x u` of the second factor anti-self-dual;
  `isSelfDual_iff`, `isAntiSelfDual_iff`: these are all of them.
* `toSO4Mat_fst_conj_antiSelfDual`, `toSO4Mat_snd_conj_selfDual`: the first factor acts trivially
  on the anti-self-dual forms, the second trivially on the self-dual forms (by `A ↦ M A Mᵀ`).
* `toSO4Mat_fst_conj_leftMat`: the first factor rotates the self-dual forms by `u ↦ p u p⁻¹`.

So, with this orientation, the first factor of `Spin4` (labels `j₊`, `n` in `spin4Mat n m`) is the
self-dual one and the second (labels `j₋`) the anti-self-dual one. The opposite orientation of
`ℝ⁴` exchanges the two. The orientations of `Lightlike/FourD/` are combinatorial; a
geometric 4-simplex `(v₀, …, v₄)` in `ℝ⁴ = ℍ` is positively oriented in the present sense when
`det(v₁ - v₀, …, v₄ - v₀) > 0` in the basis `(1, i, j, k)`.

## References

* M. F. Atiyah, N. J. Hitchin, I. M. Singer, *Self-duality in four-dimensional Riemannian
  geometry*, Proc. R. Soc. Lond. A 362 (1978) 425 (`Λ² = Λ²₊ ⊕ Λ²₋` and Spin(4) = SU(2) × SU(2)).
* J. C. Baez, *Spin foam models*, Class. Quantum Grav. 15 (1998) 1827, arXiv:gr-qc/9709052
  (the self-dual and anti-self-dual parts in 4D spin foam models).
-/

open Matrix Quaternion

namespace Lightlike.Spin4

/-- **The Hodge star on 2-forms of `ℝ⁴`**, for the orientation `(1, i, j, k)` and the Euclidean
metric: `(⋆A)_{ab} = ½ ε_{abcd} A_{cd}` for a skew matrix `A`, written out
(`(⋆A)_{01} = A_{23}`, `(⋆A)_{02} = A_{31}`, `(⋆A)_{03} = A_{12}`, and skew). -/
def hodge (A : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, A 2 3, A 3 1, A 1 2;
     -A 2 3, 0, A 0 3, -A 0 2;
     -A 3 1, -A 0 3, 0, A 0 1;
     -A 1 2, A 0 2, -A 0 1, 0]

/-- A self-dual 2-form: skew and `⋆A = A`. -/
def IsSelfDual (A : Matrix (Fin 4) (Fin 4) ℝ) : Prop := Aᵀ = -A ∧ hodge A = A

/-- An anti-self-dual 2-form: skew and `⋆A = -A`. -/
def IsAntiSelfDual (A : Matrix (Fin 4) (Fin 4) ℝ) : Prop := Aᵀ = -A ∧ hodge A = -A

/-- `⋆⋆ = 1` on 2-forms. -/
theorem hodge_hodge {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : Aᵀ = -A) : hodge (hodge A) = A := by
  ext i j
  have h := fun a b => congrFun (congrFun hA a) b
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  fin_cases i <;> fin_cases j <;> simp [hodge] <;> linarith [h 0 0, h 1 1, h 2 2, h 3 3, h 0 1,
    h 0 2, h 0 3, h 1 2, h 1 3, h 2 3]

/-- The matrix of `x ↦ u x` in the basis `(1, i, j, k)`. -/
def leftMat (u : ℍ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![u.re, -u.imI, -u.imJ, -u.imK;
     u.imI, u.re, -u.imK, u.imJ;
     u.imJ, u.imK, u.re, -u.imI;
     u.imK, -u.imJ, u.imI, u.re]

/-- The matrix of `x ↦ x u` in the basis `(1, i, j, k)`. -/
def rightMat (u : ℍ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![u.re, -u.imI, -u.imJ, -u.imK;
     u.imI, u.re, u.imK, -u.imJ;
     u.imJ, -u.imK, u.re, u.imI;
     u.imK, u.imJ, -u.imI, u.re]

lemma toMatrix_mulLeft (u : ℍ) :
    LinearMap.toMatrix basisH basisH (LinearMap.mulLeft ℝ u) = leftMat u := by
  ext i j
  rw [LinearMap.toMatrix_apply, ← Module.Basis.equivFun_apply, basisH_equivFun, basisH_apply]
  fin_cases i <;> fin_cases j <;> simp [leftMat]

lemma toMatrix_mulRight (u : ℍ) :
    LinearMap.toMatrix basisH basisH (LinearMap.mulRight ℝ u) = rightMat u := by
  ext i j
  rw [LinearMap.toMatrix_apply, ← Module.Basis.equivFun_apply, basisH_equivFun, basisH_apply]
  fin_cases i <;> fin_cases j <;> simp [rightMat]

/-- **The generators of the first factor are self-dual**: for imaginary `u`, `x ↦ u x`. -/
theorem leftMat_isSelfDual {u : ℍ} (hu : u.re = 0) : IsSelfDual (leftMat u) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [leftMat, hodge, hu]

/-- **The generators of the second factor are anti-self-dual**: for imaginary `u`, `x ↦ x u`. -/
theorem rightMat_isAntiSelfDual {u : ℍ} (hu : u.re = 0) : IsAntiSelfDual (rightMat u) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [rightMat, hodge, hu]

/-- Every self-dual 2-form is a generator of the first factor. -/
theorem isSelfDual_iff (A : Matrix (Fin 4) (Fin 4) ℝ) :
    IsSelfDual A ↔ ∃ u : ℍ, u.re = 0 ∧ A = leftMat u := by
  refine ⟨fun ⟨hA, hd⟩ => ⟨⟨0, A 1 0, A 2 0, A 3 0⟩, rfl, ?_⟩, ?_⟩
  · have h : ∀ a b, A b a = -A a b := fun a b => by
      simpa using congrFun (congrFun hA a) b
    have d1 : A 2 3 = A 0 1 := by simpa [hodge] using congrFun (congrFun hd 0) 1
    have d2 : A 3 1 = A 0 2 := by simpa [hodge] using congrFun (congrFun hd 0) 2
    have d3 : A 1 2 = A 0 3 := by simpa [hodge] using congrFun (congrFun hd 0) 3
    have := h 0 0; have := h 1 1; have := h 2 2; have := h 3 3; have := h 0 1; have := h 0 2
    have := h 0 3; have := h 1 2; have := h 1 3; have := h 2 3
    ext i j
    fin_cases i <;> fin_cases j <;> simp [leftMat] <;> linarith
  · rintro ⟨u, hu, rfl⟩
    exact leftMat_isSelfDual hu

/-- Every anti-self-dual 2-form is a generator of the second factor. -/
theorem isAntiSelfDual_iff (A : Matrix (Fin 4) (Fin 4) ℝ) :
    IsAntiSelfDual A ↔ ∃ u : ℍ, u.re = 0 ∧ A = rightMat u := by
  refine ⟨fun ⟨hA, hd⟩ => ⟨⟨0, A 1 0, A 2 0, A 3 0⟩, rfl, ?_⟩, ?_⟩
  · have h : ∀ a b, A b a = -A a b := fun a b => by
      simpa using congrFun (congrFun hA a) b
    have d1 : A 2 3 = -A 0 1 := by simpa [hodge] using congrFun (congrFun hd 0) 1
    have d2 : A 3 1 = -A 0 2 := by simpa [hodge] using congrFun (congrFun hd 0) 2
    have d3 : A 1 2 = -A 0 3 := by simpa [hodge] using congrFun (congrFun hd 0) 3
    have := h 0 0; have := h 1 1; have := h 2 2; have := h 3 3; have := h 0 1; have := h 0 2
    have := h 0 3; have := h 1 2; have := h 1 3; have := h 2 3
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rightMat] <;> linarith
  · rintro ⟨u, hu, rfl⟩
    exact rightMat_isAntiSelfDual hu

lemma leftMat_mul (a b : ℍ) : leftMat (a * b) = leftMat a * leftMat b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leftMat, mul_apply, Fin.sum_univ_four] <;> ring

lemma rightMat_mul (a b : ℍ) : rightMat (a * b) = rightMat b * rightMat a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rightMat, mul_apply, Fin.sum_univ_four] <;> ring

/-- Left and right multiplications commute (associativity of `ℍ`). -/
lemma leftMat_mul_rightMat (a b : ℍ) : leftMat a * rightMat b = rightMat b * leftMat a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leftMat, rightMat, mul_apply, Fin.sum_univ_four] <;> ring

lemma leftMat_transpose (a : ℍ) : (leftMat a)ᵀ = leftMat (star a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leftMat]

lemma rightMat_transpose (a : ℍ) : (rightMat a)ᵀ = rightMat (star a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rightMat]

lemma leftMat_one : leftMat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leftMat]

lemma rightMat_one : rightMat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rightMat]

/-- The matrix of `(p, q) ∈ Spin(4)` acting on `ℝ⁴ = ℍ` is `L_p R_{q⁻¹}`. -/
theorem toSO4Mat_eq (g : Spin4) : (toSO4Mat g : Matrix (Fin 4) (Fin 4) ℝ) =
    leftMat (quatEquiv.symm g.1 : ℍ) * rightMat (star (quatEquiv.symm g.2 : ℍ)) := by
  have h : (toSO4 g : ℍ ≃ₗᵢ[ℝ] ℍ).toLinearEquiv.toLinearMap =
      LinearMap.mulLeft ℝ (quatEquiv.symm g.1 : ℍ) ∘ₗ
        LinearMap.mulRight ℝ (star (quatEquiv.symm g.2 : ℍ)) := by
    refine LinearMap.ext fun x => ?_
    change (toSO4 g : ℍ ≃ₗᵢ[ℝ] ℍ) x = _
    rw [toSO4_apply]
    simp [mul_assoc]
  rw [toSO4Mat, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, SO4MatEquiv_apply, h,
    LinearMap.toMatrix_comp basisH basisH basisH, toMatrix_mulLeft, toMatrix_mulRight]

/-- **The first factor fixes the anti-self-dual 2-forms**: for `g = (p, 1)`, `M A Mᵀ = A`. -/
theorem toSO4Mat_fst_conj_antiSelfDual (p : SU2) {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : IsAntiSelfDual A) :
    (toSO4Mat (p, 1) : Matrix (Fin 4) (Fin 4) ℝ) * A * (toSO4Mat (p, 1) : Matrix _ _ ℝ)ᵀ = A := by
  obtain ⟨v, -, rfl⟩ := (isAntiSelfDual_iff A).mp hA
  have h1 : (quatEquiv.symm (1 : SU2) : ℍ) = 1 := by simp
  have hp : (quatEquiv.symm p : ℍ) * star (quatEquiv.symm p : ℍ) = 1 :=
    Unitary.mul_star_self_of_mem (quatEquiv.symm p).2
  rw [toSO4Mat_eq, h1, star_one, rightMat_one, Matrix.mul_one, leftMat_transpose,
    leftMat_mul_rightMat, Matrix.mul_assoc, ← leftMat_mul, hp, leftMat_one, Matrix.mul_one]

/-- **The second factor fixes the self-dual 2-forms**: for `g = (1, q)`, `M A Mᵀ = A`. -/
theorem toSO4Mat_snd_conj_selfDual (q : SU2) {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : IsSelfDual A) :
    (toSO4Mat (1, q) : Matrix (Fin 4) (Fin 4) ℝ) * A * (toSO4Mat (1, q) : Matrix _ _ ℝ)ᵀ = A := by
  obtain ⟨v, -, rfl⟩ := (isSelfDual_iff A).mp hA
  have h1 : (quatEquiv.symm (1 : SU2) : ℍ) = 1 := by simp
  have hq : (quatEquiv.symm q : ℍ) * star (quatEquiv.symm q : ℍ) = 1 :=
    Unitary.mul_star_self_of_mem (quatEquiv.symm q).2
  rw [toSO4Mat_eq]
  dsimp only
  rw [h1, leftMat_one, Matrix.one_mul, rightMat_transpose, star_star,
    ← leftMat_mul_rightMat, Matrix.mul_assoc, ← rightMat_mul, hq, rightMat_one, Matrix.mul_one]

/-- The first factor rotates the self-dual forms: `M L_u Mᵀ = L_{p u p⁻¹}` for `g = (p, 1)`. -/
theorem toSO4Mat_fst_conj_leftMat (p : SU2) (u : ℍ) :
    (toSO4Mat (p, 1) : Matrix (Fin 4) (Fin 4) ℝ) * leftMat u *
      (toSO4Mat (p, 1) : Matrix _ _ ℝ)ᵀ =
      leftMat ((quatEquiv.symm p : ℍ) * u * star (quatEquiv.symm p : ℍ)) := by
  have h1 : (quatEquiv.symm (1 : SU2) : ℍ) = 1 := by simp
  rw [toSO4Mat_eq, h1, star_one, rightMat_one, Matrix.mul_one, leftMat_transpose, leftMat_mul,
    leftMat_mul]

end Lightlike.Spin4
