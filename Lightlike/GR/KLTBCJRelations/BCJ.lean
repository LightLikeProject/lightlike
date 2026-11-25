import Lightlike.GR.KLTBCJRelations.Mandelstam

/-!
# The four-point BCJ amplitude relation for Parke-Taylor amplitudes

Row G3-261 (T-PG7). With particles `0,1,2,3` (the particles `1,2,3,4` of the literature) and the
colour-ordered amplitude `A[1234] = parkeTaylor (lt 0) (lt 1) lt`, `A[1243]` the same amplitude with the
spinor list `![lt 0, lt 1, lt 3, lt 2]`, we prove the Bern-Carrasco-Johansson amplitude relation

`s₁₄ A[1234] = s₁₃ A[1243]`   (`bcj_four`),

for nonvanishing brackets and momentum conservation (`Conserved l lt`).  The only kinematic input is
`⟨2 3⟩[3 1] + ⟨2 4⟩[4 1] = 0` (`contract_conserved`).

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson, *New relations for gauge-theory amplitudes* (`bcj-2008`).
* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697, §3.
-/

noncomputable section

namespace Lightlike.GR.KLTBCJRelations

open Lightlike.SpinorHelicity

/-- The colour-ordered four-point amplitude `A[1243]` (particles `0,1,3,2` in this labelling) with
negative-helicity gluons `1, 2`. -/
def pt1243 (lt : Fin 4 → Fin 2 → ℂ) : ℂ :=
  parkeTaylor (lt 0) (lt 1) ![lt 0, lt 1, lt 3, lt 2]

/-- The colour-ordered four-point amplitude `A[1234]` with negative-helicity gluons `1, 2`. -/
def pt1234 (lt : Fin 4 → Fin 2 → ℂ) : ℂ :=
  parkeTaylor (lt 0) (lt 1) lt

/-- The kinematic input of BCJ: `⟨2 3⟩[3 1] + ⟨2 4⟩[4 1] = 0` (1-based labels). -/
theorem angle_square_relation {l lt : Fin 4 → Fin 2 → ℂ} (h : Conserved l lt) :
    angleBr (lt 1) (lt 2) * squareBr (l 2) (l 0) +
      angleBr (lt 1) (lt 3) * squareBr (l 3) (l 0) = 0 := by
  have c := contract_conserved h (lt 1) (l 0)
  simp only [Fin.sum_univ_four] at c
  have a11 : angleBr (lt 1) (lt 1) = 0 := by rw [angleBr_eq]; ring
  have q00 : squareBr (l 0) (l 0) = 0 := by rw [squareBr_eq]; ring
  rw [a11, q00] at c
  linear_combination c

/-- **BCJ amplitude relation at four points** (Bern-Carrasco-Johansson): with momentum conservation and
nonvanishing angle brackets, `s₁₄ A[1234] = s₁₃ A[1243]`. -/
theorem bcj_four {l lt : Fin 4 → Fin 2 → ℂ} (h : Conserved l lt)
    (ha : ∀ a b : Fin 4, a ≠ b → angleBr (lt a) (lt b) ≠ 0) :
    sBr l lt 0 3 * pt1234 lt = sBr l lt 0 2 * pt1243 lt := by
  have c := angle_square_relation h
  have r0 : finRotate 4 0 = 1 := by decide
  have r1 : finRotate 4 1 = 2 := by decide
  have r2 : finRotate 4 2 = 3 := by decide
  have r3 : finRotate 4 3 = 0 := by decide
  have h01 := ha 0 1 (by decide); have h12 := ha 1 2 (by decide)
  have h23 := ha 2 3 (by decide); have h03 := ha 0 3 (by decide)
  have h13 := ha 1 3 (by decide); have h02 := ha 0 2 (by decide)
  have n30 : angleBr (lt 3) (lt 0) = - angleBr (lt 0) (lt 3) := angleBr_antisymm _ _
  have n32 : angleBr (lt 3) (lt 2) = - angleBr (lt 2) (lt 3) := angleBr_antisymm _ _
  have n20 : angleBr (lt 2) (lt 0) = - angleBr (lt 0) (lt 2) := angleBr_antisymm _ _
  simp only [pt1234, pt1243, sBr, parkeTaylor, cycDen, Fin.prod_univ_four, r0, r1, r2, r3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, n30, n32, n20]
  rw [mul_div_assoc', mul_div_assoc', div_eq_div_iff (by simp [h01, h12, h23, h03])
    (by simp [h01, h13, h23, h02])]
  linear_combination (angleBr (lt 0) (lt 3) * angleBr (lt 0) (lt 1) ^ 5 * angleBr (lt 2) (lt 3) *
    angleBr (lt 0) (lt 2)) * c

end Lightlike.GR.KLTBCJRelations

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_261.angle_square_relation := _root_.Lightlike.GR.KLTBCJRelations.angle_square_relation
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_261.bcj_four := _root_.Lightlike.GR.KLTBCJRelations.bcj_four
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_261.pt1234 := _root_.Lightlike.GR.KLTBCJRelations.pt1234
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_261.pt1243 := _root_.Lightlike.GR.KLTBCJRelations.pt1243
