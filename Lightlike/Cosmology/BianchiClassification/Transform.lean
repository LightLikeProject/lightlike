import Lightlike.Cosmology.BianchiClassification.Decomposition

/-!
# Change of basis for the Bianchi bracket

A linear change of basis `P` (with `det P ≠ 0`) transforms the Bianchi data `(n, a)` into
`((det P)⁻¹ • P n Pᵀ, (P⁻¹)ᵀ a)`.  We define the relation `BracketIso` ("`P` is a Lie algebra
isomorphism between the two brackets") and prove that it is reflexive and transitive, and that
`P` always relates `(n, a)` to its transform.

## Main results

* `Lightlike.Cosmology.BianchiClassification.transpose_mulVec_cross`: `Pᵀ (P x × P y) = det P • (x × y)`.
* `Lightlike.Cosmology.BianchiClassification.bracketIso_transform`: the transformation law of `(n, a)`.
* `Lightlike.Cosmology.BianchiClassification.BracketIso.trans`: composition of changes of basis.

## References

* heinzle-uggla-2009a (Section 3)
-/

namespace Lightlike.Cosmology.BianchiClassification

open Matrix

/-- The cofactor identity `Pᵀ (P x × P y) = det P • (x × y)`. -/
theorem transpose_mulVec_cross (P : Matrix (Fin 3) (Fin 3) ℝ) (x y : V3) :
    Pᵀ.mulVec (crossProduct (P.mulVec x) (P.mulVec y)) = P.det • crossProduct x y := by
  ext i
  fin_cases i <;>
  simp [crossProduct, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.det_fin_three,
    Matrix.transpose_apply] <;>
  ring

/-- `BracketIso n a n' a'`: some invertible matrix `P` is a Lie algebra isomorphism from the
bracket of `(n, a)` to the bracket of `(n', a')`. -/
def BracketIso (n : Matrix (Fin 3) (Fin 3) ℝ) (a : V3) (n' : Matrix (Fin 3) (Fin 3) ℝ) (a' : V3) :
    Prop :=
  ∃ P : Matrix (Fin 3) (Fin 3) ℝ, P.det ≠ 0 ∧
    ∀ x y, P.mulVec (bracket n a x y) = bracket n' a' (P.mulVec x) (P.mulVec y)

theorem BracketIso.refl (n : Matrix (Fin 3) (Fin 3) ℝ) (a : V3) : BracketIso n a n a :=
  ⟨1, by simp, by simp⟩

theorem BracketIso.trans {n₁ n₂ n₃ : Matrix (Fin 3) (Fin 3) ℝ} {a₁ a₂ a₃ : V3}
    (h₁ : BracketIso n₁ a₁ n₂ a₂) (h₂ : BracketIso n₂ a₂ n₃ a₃) : BracketIso n₁ a₁ n₃ a₃ := by
  obtain ⟨P, hP, hP'⟩ := h₁
  obtain ⟨Q, hQ, hQ'⟩ := h₂
  refine ⟨Q * P, by rw [Matrix.det_mul]; exact mul_ne_zero hQ hP, fun x y => ?_⟩
  rw [← Matrix.mulVec_mulVec, hP', hQ', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- Transformation law: the change of basis `P` carries `(n, a)` to
`((det P)⁻¹ • P n Pᵀ, (P⁻¹)ᵀ a)`. -/
theorem bracketIso_transform (n : Matrix (Fin 3) (Fin 3) ℝ) (a : V3)
    (P : Matrix (Fin 3) (Fin 3) ℝ) (hP : P.det ≠ 0) :
    BracketIso n a ((P.det)⁻¹ • (P * n * Pᵀ)) ((P⁻¹)ᵀ.mulVec a) := by
  refine ⟨P, hP, fun x y => ?_⟩
  have hPi : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hP)
  have hdot : ∀ z : V3, ((P⁻¹)ᵀ.mulVec a) ⬝ᵥ P.mulVec z = a ⬝ᵥ z := by
    intro z
    rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hPi,
      Matrix.vecMul_one]
  have hcross : ((P.det)⁻¹ • (P * n * Pᵀ)).mulVec (crossProduct (P.mulVec x) (P.mulVec y)) =
      P.mulVec (n.mulVec (crossProduct x y)) := by
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      transpose_mulVec_cross, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hP,
      one_smul]
  unfold bracket
  rw [hcross, hdot, hdot, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul]

end Lightlike.Cosmology.BianchiClassification

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.BracketIso := _root_.Lightlike.Cosmology.BianchiClassification.BracketIso
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.BracketIso.refl := _root_.Lightlike.Cosmology.BianchiClassification.BracketIso.refl
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.BracketIso.trans := _root_.Lightlike.Cosmology.BianchiClassification.BracketIso.trans
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bracketIso_transform := _root_.Lightlike.Cosmology.BianchiClassification.bracketIso_transform
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.transpose_mulVec_cross := _root_.Lightlike.Cosmology.BianchiClassification.transpose_mulVec_cross
