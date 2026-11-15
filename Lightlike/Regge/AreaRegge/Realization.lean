import Mathlib
import Lightlike.Regge.AreaRegge.Basic

/-!
# The equal-area pair is realised by Euclidean 4-simplices

`corner_pair` (in `Basic`) uses the Gram-minor criterion for "valid Euclidean 4-simplex". Here the
two length assignments `sPlus`, `sMinus` are realised by explicit points of `ℝ⁴` (with surd
coordinates), whose ten squared mutual distances are the given squared lengths and which are
affinely independent, so they are genuine simplices with non-zero volume.
-/

open Matrix

namespace Lightlike.AreaRegge

noncomputable section

/-- The vertex pair of each of the ten edges, in the order of `triEdges`. -/
def edgeV : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

/-- The squared Euclidean distance of two points of `ℝ⁴`. -/
def sqDist (x y : Fin 4 → ℝ) : ℝ := ∑ k, (x k - y k) ^ 2

/-- The points `p` realise the squared edge lengths `s`. -/
def Realizes (p : Fin 5 → Fin 4 → ℝ) (s : Fin 10 → ℝ) : Prop :=
  ∀ e, sqDist (p (edgeV e).1) (p (edgeV e).2) = s e

/-- Five points of `ℝ⁴` for `sPlus`: vertex `0` at the origin, the rest the rows of a Cholesky
factor of the Gram matrix. -/
def ptsPlus : Fin 5 → Fin 4 → ℝ :=
  ![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![-1 / 4, 1 / 4, √14 / 4, 0],
    ![1 / 4, -1 / 4, √14 / 28, √42 / 7]]

/-- Five points of `ℝ⁴` for `sMinus` (the third and fourth points reflected in the first two
coordinates). -/
def ptsMinus : Fin 5 → Fin 4 → ℝ :=
  ![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![1 / 4, -1 / 4, √14 / 4, 0],
    ![-1 / 4, 1 / 4, √14 / 28, √42 / 7]]

theorem sq14 : √14 ^ 2 = 14 := Real.sq_sqrt (by norm_num)
theorem sq42 : √42 ^ 2 = 42 := Real.sq_sqrt (by norm_num)

/-- The points `ptsPlus` realise the lengths `sPlus`. -/
theorem realizes_plus : Realizes ptsPlus sPlus := by
  intro e
  fin_cases e <;>
    simp [edgeV, sqDist, ptsPlus, sPlus, Fin.sum_univ_succ, div_pow] <;>
    nlinarith [sq14, sq42]

/-- The points `ptsMinus` realise the lengths `sMinus`. -/
theorem realizes_minus : Realizes ptsMinus sMinus := by
  intro e
  fin_cases e <;>
    simp [edgeV, sqDist, ptsMinus, sMinus, Fin.sum_univ_succ, div_pow] <;>
    nlinarith [sq14, sq42]

/-- The matrix of edge vectors from vertex `0`. -/
def edgeMat (p : Fin 5 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i => p i.succ - p 0

/-- Affine independence of five points of `ℝ⁴` from the non-vanishing of the determinant of the
edge vectors from vertex `0` (the volume of the simplex is `|det| / 4!`). -/
theorem affineIndependent_of_det {p : Fin 5 → Fin 4 → ℝ} (h : (edgeMat p).det ≠ 0) :
    AffineIndependent ℝ p := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ p 0]
  let e : Fin 4 ≃ {x : Fin 5 // x ≠ 0} :=
    Equiv.ofBijective (fun i => ⟨i.succ, Fin.succ_ne_zero i⟩)
      ⟨fun a b hab => Fin.succ_injective _ (congrArg Subtype.val hab),
        fun x => ⟨x.1.pred x.2, Subtype.ext (Fin.succ_pred x.1 x.2)⟩⟩
  have hli : LinearIndependent ℝ (edgeMat p).row := Matrix.linearIndependent_rows_of_det_ne_zero h
  refine (linearIndependent_equiv e).1 ?_
  convert hli using 1
  ext i k
  simp [edgeMat, e, Matrix.row]
  rfl

theorem det_plus : (edgeMat ptsPlus).det = √14 / 4 * (√42 / 7) := by
  simp [edgeMat, ptsPlus, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem det_minus : (edgeMat ptsMinus).det = √14 / 4 * (√42 / 7) := by
  simp [edgeMat, ptsMinus, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem det_ne : √14 / 4 * (√42 / 7) ≠ 0 := by positivity

/-- **The equal-area pair consists of actual simplices.** The two different squared-length
assignments `sPlus`, `sMinus` are realised by affinely independent five-point sets in `ℝ⁴` (so by
Euclidean 4-simplices of non-zero volume), and they have the same ten triangle areas. -/
theorem corner_pair_realized :
    sPlus ≠ sMinus ∧ area sPlus = area sMinus ∧
      (Realizes ptsPlus sPlus ∧ AffineIndependent ℝ ptsPlus) ∧
      (Realizes ptsMinus sMinus ∧ AffineIndependent ℝ ptsMinus) :=
  ⟨corner_pair.1, corner_pair.2.1, ⟨realizes_plus, affineIndependent_of_det (by rw [det_plus]; exact det_ne)⟩,
    ⟨realizes_minus, affineIndependent_of_det (by rw [det_minus]; exact det_ne)⟩⟩

end

end Lightlike.AreaRegge
