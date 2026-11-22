import Mathlib

/-!
# The unit quaternions are `SU(2)`

The standard embedding of the Hamilton quaternions `ℍ[ℝ]` in `2 × 2` complex matrices,
`a + bi + cj + dk ↦ [[a + bi, c + di], [-c + di, a - bi]]`, and the resulting isomorphism of groups
`unitary ℍ ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ`.

## Main definitions

* `Quaternion.toMatrix`: the `ℝ`-algebra homomorphism `ℍ[ℝ] →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ`.
* `Quaternion.unitaryEquivSU2`: the unit quaternions are `SU(2)`.

## Main results

* `Quaternion.toMatrix_injective`, `Quaternion.toMatrix_star`, `Quaternion.det_toMatrix`.
-/

open Matrix

namespace Quaternion

/-- The matrix of the quaternion `a + bi + cj + dk`: `[[a + bi, c + di], [-c + di, a - bi]]`. -/
def quatMat (q : ℍ[ℝ]) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩; ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]

/-- The quaternions as complex `2 × 2` matrices, an injective `ℝ`-algebra homomorphism. -/
def toMatrix : ℍ[ℝ] →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := quatMat
  map_one' := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatMat]
  map_mul' p q := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [quatMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  map_zero' := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatMat]
  map_add' p q := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatMat] <;> ring
  commutes' r := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [quatMat, Algebra.algebraMap_eq_smul_one]

lemma toMatrix_apply (q : ℍ[ℝ]) : toMatrix q = quatMat q := rfl

lemma toMatrix_injective : Function.Injective toMatrix := by
  intro p q h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp only [toMatrix_apply, quatMat, of_apply, cons_val', cons_val_zero, empty_val',
    cons_val_fin_one, cons_val_one, Complex.mk.injEq] at h00 h01
  exact Quaternion.ext_iff.mpr ⟨h00.1, h00.2, h01.1, h01.2⟩

/-- Quaternion conjugation is the conjugate transpose. -/
lemma toMatrix_star (q : ℍ[ℝ]) : toMatrix (star q) = (toMatrix q)ᴴ := by
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [toMatrix_apply, quatMat]

/-- The determinant is the squared norm. -/
lemma det_toMatrix (q : ℍ[ℝ]) : (toMatrix q).det = ((normSq q : ℝ) : ℂ) := by
  rw [toMatrix_apply, quatMat, det_fin_two_of, normSq_def']
  apply Complex.ext <;> simp [sq] <;> ring

/-- A unit quaternion has `|q|² = 1`. -/
lemma normSq_eq_one_of_mem_unitary (q : unitary ℍ[ℝ]) : normSq (q : ℍ[ℝ]) = 1 := by
  have h := Quaternion.star_mul_self (q : ℍ[ℝ])
  rw [Unitary.star_mul_self_of_mem q.2, ← Quaternion.coe_one] at h
  exact Quaternion.coe_injective h.symm

/-- A quaternion with `|q|² = 1` is unitary. -/
lemma mem_unitary_of_normSq_eq_one {q : ℍ[ℝ]} (h : normSq q = 1) : q ∈ unitary ℍ[ℝ] := by
  rw [Unitary.mem_iff, Quaternion.star_mul_self, Quaternion.self_mul_star, h, Quaternion.coe_one]
  exact ⟨rfl, rfl⟩

/-- A unit quaternion gives an element of `SU(2)`. -/
lemma toMatrix_mem_specialUnitaryGroup (q : unitary ℍ[ℝ]) :
    toMatrix (q : ℍ[ℝ]) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hn : normSq (q : ℍ[ℝ]) = 1 := normSq_eq_one_of_mem_unitary q
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose,
    ← toMatrix_star, ← map_mul, Unitary.mul_star_self_of_mem q.2, map_one, det_toMatrix, hn,
    Complex.ofReal_one]
  exact ⟨rfl, rfl⟩

/-- Every element of `SU(2)` is the matrix of a unit quaternion. -/
lemma exists_toMatrix_eq (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ q : unitary ℍ[ℝ], toMatrix (q : ℍ[ℝ]) = (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨hU, hdet⟩ := mem_specialUnitaryGroup_iff.mp g.2
  set G : Matrix (Fin 2) (Fin 2) ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ) with hG
  have hstar : star G * G = 1 := mem_unitaryGroup_iff'.mp hU
  have hadj : star G = adjugate G := by
    have h1 : adjugate G * G = 1 := by rw [adjugate_mul, hdet, one_smul]
    calc star G = star G * (G * adjugate G) := by rw [mul_adjugate, hdet, one_smul, mul_one]
      _ = adjugate G := by rw [← Matrix.mul_assoc, hstar, Matrix.one_mul]
  have e00 := congrFun (congrFun hadj 0) 0
  have e10 := congrFun (congrFun hadj 1) 0
  simp only [adjugate_fin_two, star_apply, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one] at e00 e10
  let q : ℍ[ℝ] := ⟨(G 0 0).re, (G 0 0).im, (G 0 1).re, (G 0 1).im⟩
  have hGq : toMatrix q = G := by
    ext i j; fin_cases i <;> fin_cases j
    · simp [toMatrix_apply, quatMat, q]
    · simp [toMatrix_apply, quatMat, q]
    · have := congrArg Complex.re e10; have h2 := congrArg Complex.im e10
      simp at this h2
      apply Complex.ext <;> simp [toMatrix_apply, quatMat, q] <;> linarith
    · have := congrArg Complex.re e00; have h2 := congrArg Complex.im e00
      simp at this h2
      apply Complex.ext <;> simp [toMatrix_apply, quatMat, q] <;> linarith
  have hq : q ∈ unitary ℍ[ℝ] := by
    rw [Unitary.mem_iff]
    constructor
    · apply toMatrix_injective
      rw [map_mul, toMatrix_star, hGq, map_one, ← star_eq_conjTranspose, hstar]
    · apply toMatrix_injective
      rw [map_mul, toMatrix_star, hGq, map_one, ← star_eq_conjTranspose]
      exact mem_unitaryGroup_iff.mp hU
  exact ⟨⟨q, hq⟩, hGq⟩

/-- **The unit quaternions are `SU(2)`.** -/
noncomputable def unitaryEquivSU2 :
    unitary ℍ[ℝ] ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  let f : unitary ℍ[ℝ] →* Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    { toFun := fun q => ⟨toMatrix (q : ℍ[ℝ]), toMatrix_mem_specialUnitaryGroup q⟩
      map_one' := Subtype.ext (map_one toMatrix)
      map_mul' := fun p q => Subtype.ext (map_mul toMatrix (p : ℍ[ℝ]) q) }
  MulEquiv.ofBijective f
    ⟨fun _ _ h => Subtype.ext (toMatrix_injective (congrArg Subtype.val h)),
      fun g => let ⟨q, hq⟩ := exists_toMatrix_eq g; ⟨q, Subtype.ext hq⟩⟩

@[simp]
lemma coe_unitaryEquivSU2 (q : unitary ℍ[ℝ]) :
    (unitaryEquivSU2 q : Matrix (Fin 2) (Fin 2) ℂ) = toMatrix (q : ℍ[ℝ]) := rfl

/-- Trust check: the equivalence sends `i` to `diag(i, -i)` and `j` to `[[0, 1], [-1, 0]]`. -/
example : toMatrix (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) = !![Complex.I, 0; 0, -Complex.I] := by
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [toMatrix_apply, quatMat]

/-- Non-vacuity / wrong-model control: `toMatrix` is not the zero map on `j`. -/
example : toMatrix (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) ≠ toMatrix (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) := by
  intro h
  have := toMatrix_injective h
  simp at this

end Quaternion
